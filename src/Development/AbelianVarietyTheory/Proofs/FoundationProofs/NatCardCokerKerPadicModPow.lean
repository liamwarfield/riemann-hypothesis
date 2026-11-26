module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCardCokerKerPadicModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCardCokerKerPadicModPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

private lemma natCard_quotient_ker_of_surjective {G H : Type*} [AddGroup G] [AddGroup H]
    (φ : G →+ H) (hφ : Function.Surjective φ) : Nat.card (G ⧸ φ.ker) = Nat.card H :=
  Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv

theorem _root_.GlobalTheory.natCard_coker_ker_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (X P : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup P] [Module ℤ_[l] P] (f : X →ₗ[ℤ_[l]] P) (R : Type) [CommRing R] (X' P' : Type) [AddCommGroup X'] [Module R X'] [AddCommGroup P'] [Module R P'] (f' : X' →ₗ[R] P') (πX : X →+ X') (πP : P →+ P'), Function.Surjective πX → Function.Surjective πP → (∀ x, πX x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP (f x) = f' (πX x)) → Nat.card ((P ⧸ LinearMap.range f) ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) ((l : ℤ_[l]) ^ r))) = Nat.card (P' ⧸ LinearMap.range f') ∧ ((∀ x p, f x = (l : ℤ_[l]) ^ r • p → ∃ x', f x = (l : ℤ_[l]) ^ r • f x') → Nat.card (LinearMap.ker f ⧸ (LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))).comap (LinearMap.ker f).subtype) = Nat.card (LinearMap.ker f')) := by
  intro l _ r X P _ _ _ _ f R _ X' P' _ _ _ _ f' πX πP hX hP hkX hkP hcomm
  set c : ℤ_[l] := (l : ℤ_[l]) ^ r with hc
  have hrange : ∀ p : P, πP p ∈ LinearMap.range f' ↔ ∃ x y, p = f x + c • y := by
    intro p
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hX x'
      have h0 : πP (p - f x) = 0 := by rw [map_sub, hcomm, hx', sub_self]
      obtain ⟨y, hy⟩ := (hkP _).1 h0
      exact ⟨x, y, by rw [hy]; abel⟩
    · rintro ⟨x, y, rfl⟩
      refine ⟨πX x, ?_⟩
      rw [← hcomm, map_add (f := _), (hkP (c • y)).2 ⟨y, rfl⟩, add_zero]
  constructor
  · let φ₁ : P →+ (P ⧸ LinearMap.range f) ⧸
        LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) c) :=
      ((LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) c)).mkQ.comp
        (LinearMap.range f).mkQ).toAddMonoidHom
    let φ₂ : P →+ P' ⧸ LinearMap.range f' := (LinearMap.range f').mkQ.toAddMonoidHom.comp πP
    have hφ₁ : Function.Surjective φ₁ :=
      (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
    have hφ₂ : Function.Surjective φ₂ := (Submodule.mkQ_surjective _).comp hP
    have hker : φ₁.ker = φ₂.ker := by
      ext p
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
      change Submodule.Quotient.mk (Submodule.Quotient.mk p) = 0 ↔
        Submodule.Quotient.mk (πP p) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, hrange]
      constructor
      · rintro ⟨q, hq⟩
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
        obtain ⟨x, hx⟩ := hq
        exact ⟨-x, y, by rw [map_neg, hx]; abel⟩
      · rintro ⟨x, y, rfl⟩
        refine ⟨Submodule.Quotient.mk y, ?_⟩
        rw [LinearMap.lsmul_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        exact ⟨-x, by rw [map_neg]; abel⟩
    rw [← natCard_quotient_ker_of_surjective φ₁ hφ₁, ← natCard_quotient_ker_of_surjective φ₂ hφ₂,
      hker]
  · intro hdiv
    let ψ : LinearMap.ker f →+ LinearMap.ker f' :=
      { toFun := fun x => ⟨πX x, by
          rw [LinearMap.mem_ker, ← hcomm, LinearMap.mem_ker.1 x.2, map_zero]⟩
        map_zero' := by ext; simp
        map_add' := fun x y => by ext; simp }
    have hψ : Function.Surjective ψ := by
      rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := hX x'
      have h0 : πP (f x) = 0 := by rw [hcomm]; exact hx'
      obtain ⟨p, hp⟩ := (hkP _).1 h0
      obtain ⟨x₁, hx₁⟩ := hdiv x p hp.symm
      refine ⟨⟨x - c • x₁, by rw [LinearMap.mem_ker, map_sub, map_smul, ← hx₁, sub_self]⟩, ?_⟩
      ext
      change πX (x - c • x₁) = πX x
      rw [map_sub, (hkX (c • x₁)).2 ⟨x₁, rfl⟩, sub_zero]
    have hker : ψ.ker = ((LinearMap.range (LinearMap.lsmul ℤ_[l] X c)).comap
        (LinearMap.ker f).subtype).toAddSubgroup := by
      ext x
      rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
        LinearMap.mem_range]
      change (⟨πX x, _⟩ : LinearMap.ker f') = 0 ↔ _
      rw [Subtype.ext_iff, ZeroMemClass.coe_zero, hkX]
      simp [LinearMap.lsmul_apply]
    have h := natCard_quotient_ker_of_surjective ψ hψ
    rw [hker] at h
    exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCardCokerKerPadicModPowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_coker_ker_padic_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (X P : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup P] [Module ℤ_[l] P] (f : X →ₗ[ℤ_[l]] P) (R : Type) [CommRing R] (X' P' : Type) [AddCommGroup X'] [Module R X'] [AddCommGroup P'] [Module R P'] (f' : X' →ₗ[R] P') (πX : X →+ X') (πP : P →+ P'), Function.Surjective πX → Function.Surjective πP → (∀ x, πX x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) → (∀ x, πP (f x) = f' (πX x)) → Nat.card ((P ⧸ LinearMap.range f) ⧸ LinearMap.range (LinearMap.lsmul ℤ_[l] (P ⧸ LinearMap.range f) ((l : ℤ_[l]) ^ r))) = Nat.card (P' ⧸ LinearMap.range f') ∧ ((∀ x p, f x = (l : ℤ_[l]) ^ r • p → ∃ x', f x = (l : ℤ_[l]) ^ r • f x') → Nat.card (LinearMap.ker f ⧸ (LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))).comap (LinearMap.ker f).subtype) = Nat.card (LinearMap.ker f')) := by
  first | exact @GlobalTheory.natCard_coker_ker_mod_pow | exact GlobalTheory.natCard_coker_ker_mod_pow | (intros; apply GlobalTheory.natCard_coker_ker_mod_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntLengthEqOfCardQuotientEqCardSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntLengthEqOfCardQuotientEqCardSubmodule
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

theorem card_residueField_padicInt (l : ℕ) [Fact l.Prime] :
    Nat.card (IsLocalRing.ResidueField ℤ_[l]) = l := by
  rw [Nat.card_congr (PadicInt.residueField (p := l)).toEquiv, Nat.card_zmod]

theorem padicInt_length_eq_top_of_infinite (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X]
    [Module ℤ_[l] X] (h : ¬ Finite X) : Module.length ℤ_[l] X = ⊤ := by
  by_contra hne
  obtain ⟨n, -, hc⟩ := exists_length_eq_and_card_eq_pow_of_isFiniteLength ℤ_[l] X
    (Module.length_ne_top_iff.mp hne)
  rw [card_residueField_padicInt] at hc
  exact h (Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero))

theorem padicInt_length_eq_of_card_eq (l : ℕ) [Fact l.Prime] (X Y : Type) [AddCommGroup X]
    [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] [Finite X] [Finite Y]
    (h : Nat.card X = Nat.card Y) : Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  obtain ⟨n, hn, hc⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] X
  obtain ⟨m, hm, hd⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] Y
  rw [card_residueField_padicInt] at hc hd
  have : n = m := Nat.pow_right_injective (Fact.out : l.Prime).two_le (by
    simp only; rw [← hc, ← hd, h])
  rw [hn, hm, this]

theorem padicInt_length_eq_of_card_quotient_eq_card_submodule (l : ℕ) [Fact l.Prime] (X Y : Type)
    [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y]
    (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ) (hN : Antitone N)
    (hsep : ∀ x, (∀ r, x ∈ N r) → x = 0) (hP : Monotone P) (hex : ∀ y, ∃ r, y ∈ P r)
    (hc : ∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) :
    Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  have key : ∀ r0, c ≤ r0 → (∀ r, r0 ≤ r → Nat.card (P r) ≤ Nat.card (P r0)) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro r0 h0 hb
    have hfin : ∀ r, c ≤ r → Finite (X ⧸ N r) := fun r hr => by
      have := (hc r hr).1
      exact Nat.finite_of_card_ne_zero (by rw [(hc r hr).2]; exact Nat.card_pos.ne')
    have hPtop : P r0 = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨r, hr⟩ := hex y
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := (hc _ (h0.trans hle)).1
      have hbij : Function.Bijective (Submodule.inclusion (hP hle)) :=
        (Submodule.inclusion_injective _).bijective_of_nat_card_le (hb _ hle)
      obtain ⟨z, hz⟩ := hbij.2 ⟨y, hP (le_max_left r r0) hr⟩
      have : (z : Y) = y := congrArg Subtype.val hz
      exact this ▸ z.2
    have hNbot : N r0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      refine (Submodule.mem_bot _).mpr (hsep x fun r => ?_)
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := hfin _ (h0.trans hle)
      have hbij : Function.Bijective (Submodule.factor (hN hle)) :=
        (Submodule.factor_surjective _).bijective_of_nat_card_le (by
          rw [(hc _ (h0.trans hle)).2, (hc _ h0).2]; exact hb _ hle)
      have h1 : (N (max r r0)).mkQ x = 0 := hbij.1 (by
        rw [map_zero, Submodule.factor_mk]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hx)
      exact hN (le_max_left r r0) ((Submodule.Quotient.mk_eq_zero _).mp h1)
    have eX : (X ⧸ N r0) ≃ₗ[ℤ_[l]] X := Submodule.quotEquivOfEqBot _ hNbot
    have eY : (P r0) ≃ₗ[ℤ_[l]] Y := LinearEquiv.ofTop _ hPtop
    have := hfin _ h0
    have := (hc _ h0).1
    rw [← eX.length_eq, ← eY.length_eq]
    exact padicInt_length_eq_of_card_eq l _ _ (hc _ h0).2
  have bdd : ∀ B : ℕ, (∀ r, c ≤ r → Nat.card (P r) ≤ B) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro B hB
    have hS : ((fun r => Nat.card (P r)) '' {r | c ≤ r}).Finite :=
      (Set.finite_le_nat B).subset (by rintro _ ⟨r, hr, rfl⟩; exact hB r hr)
    obtain ⟨_, ⟨r0, hr0, rfl⟩, hmax⟩ := Set.exists_max_image _ id hS ⟨_, c, le_refl c, rfl⟩
    exact key r0 hr0 fun r hr => hmax _ ⟨r, le_trans hr0 hr, rfl⟩
  by_cases hX : Finite X
  · refine bdd (Nat.card X) fun r hr => ?_
    rw [← (hc r hr).2]
    exact Nat.card_le_card_of_surjective _ (N r).mkQ_surjective
  by_cases hY : Finite Y
  · exact bdd (Nat.card Y) fun r _ =>
      Nat.card_le_card_of_injective _ (P r).subtype_injective
  rw [padicInt_length_eq_top_of_infinite l X hX, padicInt_length_eq_top_of_infinite l Y hY]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntLengthEqOfCardQuotientEqCardSubmoduleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_length_eq_of_card_quotient_eq : ∀ (l : ℕ) [Fact l.Prime] (X Y : Type) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ), Antitone N → (∀ x, (∀ r, x ∈ N r) → x = 0) → Monotone P → (∀ y, ∃ r, y ∈ P r) → (∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) → Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  first | exact @GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule | exact GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule | (intros; apply GlobalTheory.padicInt_length_eq_of_card_quotient_eq_card_submodule <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModLThreeCocycleCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModLThreeCocycleCondition
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.PadicCocycleLift

variable {l : ℕ} [Fact l.Prime]

theorem toZModPow_eq_zero_iff (r : ℕ) (x : ℤ_[l]) :
    PadicInt.toZModPow r x = 0 ↔ (l : ℤ_[l]) ^ r ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

theorem continuous_toZModPow (r : ℕ) :
    Continuous (PadicInt.toZModPow r : ℤ_[l] → ZMod (l ^ r)) := by
  refine continuous_of_continuousAt_zero (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) ?_
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(r : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  refine ContinuousAt.congr (f := fun _ => (0 : ZMod (l ^ r))) continuousAt_const ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow] at hx
  exact hx.symm

theorem exists_continuous_div {X : Type*} [TopologicalSpace X] (f : X → ℤ_[l]) (hf : Continuous f)
    (a : ℤ_[l]) (ha : a ≠ 0) (hd : ∀ x, a ∣ f x) :
    ∃ c : X → ℤ_[l], Continuous c ∧ ∀ x, f x = a * c x := by
  choose c hc using hd
  refine ⟨c, ?_, hc⟩
  have ha' : (a : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 ha
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ c : X → ℚ_[l]) = fun x => (a : ℚ_[l])⁻¹ * (f x : ℚ_[l]) := by
    funext x
    rw [hc x, PadicInt.coe_mul, inv_mul_cancel_left₀ ha']
    rfl
  have h2 : Continuous fun x => (a : ℚ_[l])⁻¹ * (f x : ℚ_[l]) :=
    continuous_const.mul (continuous_subtype_val.comp hf)
  rw [← e] at h2
  exact h2

theorem exists_continuous_lift {X : Type*} [TopologicalSpace X] (r : ℕ) (f : X → ZMod (l ^ r))
    (hf : Continuous f) :
    ∃ F : X → ℤ_[l], Continuous F ∧ ∀ x, PadicInt.toZModPow r (F x) = f x := by
  have hs : Function.Surjective (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) :=
    ZMod.ringHom_surjective _
  exact ⟨fun x => Function.surjInv hs (f x),
    (continuous_of_discreteTopology (f := Function.surjInv hs)).comp hf,
    fun x => Function.surjInv_eq hs _⟩

variable {Γ : Type} [Group Γ]

noncomputable def dTwo (χ : Γ → ℤ_[l]) (u : Γ × Γ → ℤ_[l]) (p : Γ × Γ × Γ) : ℤ_[l] :=
  χ p.1 * u (p.2.1, p.2.2) - u (p.1 * p.2.1, p.2.2) + u (p.1, p.2.1 * p.2.2) - u (p.1, p.2.1)

def IsCocycleThree (χ : Γ → ℤ_[l]) (c : Γ × Γ × Γ → ℤ_[l]) : Prop :=
  ∀ g h k m, χ g * c (h, k, m) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m)
    + c (g, h, k) = 0

theorem isCocycleThree_dTwo (χ : Γ → ℤ_[l]) (hχ : ∀ g h, χ (g * h) = χ g * χ h)
    (u : Γ × Γ → ℤ_[l]) : IsCocycleThree χ (dTwo χ u) := by
  intro g h k m
  simp only [dTwo, hχ, mul_assoc]
  ring

theorem IsCocycleThree.sub {χ : Γ → ℤ_[l]} {c c' : Γ × Γ × Γ → ℤ_[l]} (hc : IsCocycleThree χ c)
    (hc' : IsCocycleThree χ c') : IsCocycleThree χ (fun p => c p - c' p) := by
  intro g h k m
  linear_combination hc g h k m - hc' g h k m

theorem IsCocycleThree.cancel {χ : Γ → ℤ_[l]} {c c' : Γ × Γ × Γ → ℤ_[l]} (hc : IsCocycleThree χ c)
    {a : ℤ_[l]} (ha : a ≠ 0) (e : ∀ p, c p = a * c' p) : IsCocycleThree χ c' := by
  intro g h k m
  have := hc g h k m
  simp only [e] at this
  apply mul_left_cancel₀ ha
  linear_combination this

variable [TopologicalSpace Γ] [ContinuousMul Γ]

theorem continuous_dTwo {χ : Γ → ℤ_[l]} (hχ : Continuous χ) {u : Γ × Γ → ℤ_[l]}
    (hu : Continuous u) : Continuous (dTwo χ u) := by
  unfold dTwo
  fun_prop

omit [ContinuousMul Γ] in
theorem exists_dTwo_eq (χ : Γ → ℤ_[l])
    (step : ∀ c : Γ × Γ × Γ → ℤ_[l], Continuous c → IsCocycleThree χ c →
      ∃ u c', Continuous u ∧ Continuous c' ∧ IsCocycleThree χ c' ∧
        ∀ p, c p = dTwo χ u p + l * c' p)
    (c : Γ × Γ × Γ → ℤ_[l]) (hc : Continuous c) (hz : IsCocycleThree χ c) :
    ∃ u, Continuous u ∧ ∀ p, c p = dTwo χ u p := by
  choose U C hU hC hCz hE using step
  let T := {c : Γ × Γ × Γ → ℤ_[l] // Continuous c ∧ IsCocycleThree χ c}
  let nx : T → T := fun t => ⟨C t.1 t.2.1 t.2.2, hC _ _ _, hCz _ _ _⟩
  let s : ℕ → T := fun n => nx^[n] ⟨c, hc, hz⟩
  let u : ℕ → Γ × Γ → ℤ_[l] := fun n => U (s n).1 (s n).2.1 (s n).2.2
  have hu : ∀ n, Continuous (u n) := fun n => hU _ _ _
  have hs : ∀ n p, (s n).1 p = dTwo χ (u n) p + l * (s (n + 1)).1 p := by
    intro n p
    have : s (n + 1) = nx (s n) := Function.iterate_succ_apply' _ _ _
    rw [this]
    exact hE _ _ _ p
  have hn : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hb : ∀ (n : ℕ) (x : ℤ_[l]), ‖(l : ℤ_[l]) ^ n * x‖ ≤ ‖(l : ℤ_[l])‖ ^ n := by
    intro n x
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) x.norm_le_one
  have hg : Summable fun n : ℕ => ‖(l : ℤ_[l])‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hn
  have hsum : ∀ x : ℕ → ℤ_[l], Summable fun n => (l : ℤ_[l]) ^ n * x n := fun x =>
    Summable.of_norm_bounded hg fun n => hb n _
  refine ⟨fun q => ∑' n, (l : ℤ_[l]) ^ n * u n q,
    continuous_tsum (fun n => continuous_const.mul (hu n)) hg fun n q => hb n _, fun p => ?_⟩
  have h1 : HasSum (fun n => (l : ℤ_[l]) ^ n * dTwo χ (u n) p)
      (dTwo χ (fun q => ∑' n, (l : ℤ_[l]) ^ n * u n q) p) := by
    have := ((((hsum fun n => u n (p.2.1, p.2.2)).hasSum.mul_left (χ p.1)).sub
      (hsum fun n => u n (p.1 * p.2.1, p.2.2)).hasSum).add
      (hsum fun n => u n (p.1, p.2.1 * p.2.2)).hasSum).sub
      (hsum fun n => u n (p.1, p.2.1)).hasSum
    have e : (fun n => (l : ℤ_[l]) ^ n * dTwo χ (u n) p) = fun n =>
        χ p.1 * ((l : ℤ_[l]) ^ n * u n (p.2.1, p.2.2)) - (l : ℤ_[l]) ^ n * u n (p.1 * p.2.1, p.2.2)
          + (l : ℤ_[l]) ^ n * u n (p.1, p.2.1 * p.2.2) - (l : ℤ_[l]) ^ n * u n (p.1, p.2.1) := by
      funext n
      simp only [dTwo]
      ring
    rw [e]
    exact this
  have h2 : ∀ N, ∑ n ∈ Finset.range N, (l : ℤ_[l]) ^ n * dTwo χ (u n) p
      = c p - (l : ℤ_[l]) ^ N * (s N).1 p := by
    intro N
    induction N with
    | zero => simp [s]
    | succ N ih => rw [Finset.sum_range_succ, ih, hs N p]; ring
  have h3 := h1.tendsto_sum_nat
  simp only [h2] at h3
  have h4 := (tendsto_const_nhds (x := c p)).sub (hsum fun n => (s n).1 p).tendsto_atTop_zero
  rw [sub_zero] at h4
  exact tendsto_nhds_unique h4 h3

theorem twoCocycle_lift : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (ρ1 : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g x, PadicInt.toZModPow 1 (ρ g x) = ρ1 g (PadicInt.toZModPow 1 x)) → (∀ c : Γ × Γ × Γ → ZMod (l ^ 1), Continuous c → (∀ g h k m, ρ1 g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → ZMod (l ^ 1), Continuous u ∧ ∀ g h k, ρ1 g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k)) → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ y ∈ Z2 ρr, ∃ z ∈ Z2 ρ, ∀ p, PadicInt.toZModPow r (z p) = y p := by
  intro l _ Γ _ _ _ ρ hρ ρ1 h1 H3 r ρr hr y hy
  set χ : Γ → ℤ_[l] := fun g => ρ g 1 with hχdef
  have hρχ : ∀ g x, ρ g x = χ g * x := by
    intro g x
    have := map_smul (ρ g) x 1
    rw [smul_eq_mul, mul_one, smul_eq_mul] at this
    rw [this, mul_comm]
  have hχm : ∀ g h, χ (g * h) = χ g * χ h := by
    intro g h
    rw [← hρχ]
    simp only [hχdef, map_mul, Module.End.mul_apply]
  have hχc : Continuous χ := hρ.comp (continuous_id.prodMk continuous_const)
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have step : ∀ c : Γ × Γ × Γ → ℤ_[l], Continuous c → IsCocycleThree χ c →
      ∃ u c', Continuous u ∧ Continuous c' ∧ IsCocycleThree χ c' ∧
        ∀ p, c p = dTwo χ u p + l * c' p := by
    intro c hc hz
    obtain ⟨v, hv, hvc⟩ := H3 (fun p => PadicInt.toZModPow 1 (c p))
      ((continuous_toZModPow 1).comp hc) (by
        intro g h k m
        have := congrArg (PadicInt.toZModPow 1) (hz g h k m)
        rw [← hρχ] at this
        simpa only [map_add (f := _), map_sub, h1, map_zero] using this)
    obtain ⟨u, hu, huv⟩ := exists_continuous_lift 1 v hv
    obtain ⟨c', hc', e⟩ := exists_continuous_div (fun p => c p - dTwo χ u p)
      (hc.sub (continuous_dTwo hχc hu)) l hl0 (by
        rintro ⟨g, h, k⟩
        rw [← pow_one (l : ℤ_[l]), ← toZModPow_eq_zero_iff]
        simp only [dTwo, ← hρχ, map_add (f := _), map_sub, h1, huv, hvc, sub_self])
    exact ⟨u, c', hu, hc', (hz.sub (isCocycleThree_dTwo χ hχm u)).cancel hl0 e,
      fun p => by linear_combination e p⟩
  obtain ⟨Y, hY, hYy⟩ := exists_continuous_lift r y hy.1
  obtain ⟨c, hc, e⟩ := exists_continuous_div (dTwo χ Y) (continuous_dTwo hχc hY)
    ((l : ℤ_[l]) ^ r) (pow_ne_zero _ hl0) (by
      rintro ⟨g, h, k⟩
      rw [← toZModPow_eq_zero_iff]
      simp only [dTwo, ← hρχ, map_add (f := _), map_sub, hr, hYy]
      exact hy.2 g h k)
  obtain ⟨u, hu, hcu⟩ := exists_dTwo_eq χ step c hc
    ((isCocycleThree_dTwo χ hχm Y).cancel (pow_ne_zero _ hl0) e)
  refine ⟨fun p => Y p - (l : ℤ_[l]) ^ r * u p,
    ⟨hY.sub (continuous_const.mul hu), fun g h k => ?_⟩, fun p => ?_⟩
  · have e1 := e (g, h, k)
    rw [hcu] at e1
    simp only [dTwo] at e1
    rw [hρχ]
    linear_combination e1
  · rw [map_sub, hYy, (toZModPow_eq_zero_iff r _).2 (dvd_mul_right _ _), sub_zero]

end GlobalTheory.PadicCocycleLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModLThreeCocycleConditionStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mod_l_three_cocycle_condition : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ] (ρ : Representation ℤ_[l] Γ ℤ_[l]), ContAction ρ → ∀ (ρ1 : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g x, PadicInt.toZModPow 1 (ρ g x) = ρ1 g (PadicInt.toZModPow 1 x)) → (∀ c : Γ × Γ × Γ → ZMod (l ^ 1), Continuous c → (∀ g h k m, ρ1 g (c (h, k, m)) - c (g * h, k, m) + c (g, h * k, m) - c (g, h, k * m) + c (g, h, k) = 0) → ∃ u : Γ × Γ → ZMod (l ^ 1), Continuous u ∧ ∀ g h k, ρ1 g (u (h, k)) - u (g * h, k) + u (g, h * k) - u (g, h) = c (g, h, k)) → ∀ (r : ℕ) (ρr : Representation (ZMod (l ^ r)) Γ (ZMod (l ^ r))), (∀ g x, PadicInt.toZModPow r (ρ g x) = ρr g (PadicInt.toZModPow r x)) → ∀ y ∈ Z2 ρr, ∃ z ∈ Z2 ρ, ∀ p, PadicInt.toZModPow r (z p) = y p := by
  first | exact @GlobalTheory.PadicCocycleLift.twoCocycle_lift | exact GlobalTheory.PadicCocycleLift.twoCocycle_lift | (intros; apply GlobalTheory.PadicCocycleLift.twoCocycle_lift <;> assumption)
end
end
