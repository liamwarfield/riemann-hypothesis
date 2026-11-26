module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDef

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunValueLe
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_value_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (n : ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    Covers2 (fun y => r (a y)) ∧ ∀ B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ, (∀ y, 0 ≤ B y y) →
      (2 : ℝ) ^ n * evalR (vorFun O g) B ≤ 2 ^ g * ∑ y, B (r (a y)) (r (a y)) ∧
      ((2 : ℝ) ^ n * evalR (vorFun O g) B = 2 ^ g * ∑ y, B (r (a y)) (r (a y)) ↔ ∀ y, IsMin2 B (r (a y))) := by
  intro O _ _ _ _ bar g X _ _ _ n r a hr ha
  have hfin : Module.Finite ℤ X := Module.Finite.of_surjective r hr
  have hs : ∀ c d : Fin n → ℤ, r (c + (((1 : ℕ) : ℤ) + 1) • d) = r c + (r d + r d) := fun c d => by
    rw [map_add (f := _), map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  refine ⟨fun x => ?_, fun B hB => ?_⟩
  · obtain ⟨b, rfl⟩ := hr x
    obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq (M := 1) (a := b) (a' := a (redV 1 b)) (ha _).symm
    exact ⟨redV 1 b, r d, by rw [← hs, ← hd]⟩
  set Br : (Fin n → ℤ) → (Fin n → ℤ) → ℝ := fun c d => B (r c) (r d) with hBr
  have hval : (2 : ℝ) ^ n * evalR (vorFun O g) B = 2 ^ g * ∑ y, classMin 1 Br y := by
    have h0 : zeroFun.eval X (fun c d => B c d) = 0 := by
      rw [zeroFun.eval_eq hr]; rfl
    have h1 : (fineMean 1).eval X (fun c d => B c d) =
        (((((1 : ℕ) : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin 1 Br y - Br 0 0) := by
      rw [(fineMean 1).eval_eq hr]; rfl
    have h2 : Br 0 0 = 0 := by simp [hBr]
    have h3 : ((fineDen g {1} : ℕ) : ℝ) = 2 ^ g := by
      simp only [fineDen, Finset.prod_singleton]; norm_num
    have h4 : (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
    unfold evalR vorFun
    rw [eval_baseFun, h0, Finset.sum_singleton, h1, h2, h3, h4]
    field_simp
    ring
  have hbdd : ∀ y, BddBelow {x | ∃ c : Fin n → ℤ, redV 1 c = y ∧ Br c c = x} := fun y =>
    ⟨0, by rintro x ⟨c, -, rfl⟩; exact hB _⟩
  have hle : ∀ y, classMin 1 Br y ≤ B (r (a y)) (r (a y)) := fun y =>
    csInf_le (hbdd y) ⟨a y, ha y, rfl⟩
  have hiff : ∀ y, classMin 1 Br y = B (r (a y)) (r (a y)) ↔ IsMin2 B (r (a y)) := fun y => by
    constructor
    · intro h x
      obtain ⟨b, rfl⟩ := hr x
      rw [← h, ← hs]
      refine csInf_le (hbdd y) ⟨_, ?_, rfl⟩
      rw [redV_add_smul, ha]
    · intro h
      refine le_antisymm (hle y) (le_csInf ⟨_, a y, ha y, rfl⟩ ?_)
      rintro x ⟨c, hc, rfl⟩
      obtain ⟨d, rfl⟩ := exists_eq_add_of_redV_eq (M := 1) (a := c) (a' := a y) (by rw [hc, ha])
      simp only [hBr]
      rw [hs]
      exact h _
  have hp : (0 : ℝ) < 2 ^ g := by positivity
  rw [hval]
  refine ⟨mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hle y) hp.le, ?_⟩
  rw [mul_right_inj' hp.ne', Finset.sum_eq_sum_iff_of_le fun y _ => hle y]
  simp only [Finset.mem_univ, true_imp_iff, hiff]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbits
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCover
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupport
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupport
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_smul_mem_of_le_of_finrank_le {M : Type} [AddCommGroup M] [Module.Finite ℤ M] {P Q : Submodule ℤ M}
    (h : P ≤ Q) (hr : Module.finrank ℤ Q ≤ Module.finrank ℤ P) {y : M} (hy : y ∈ Q) :
    ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ P := by
  have e : (P.comap Q.subtype) ≃ₗ[ℤ] P := Submodule.comapSubtypeEquivOfLe h
  have h1 := Submodule.finrank_quotient_add_finrank (P.comap Q.subtype)
  rw [e.finrank_eq] at h1
  have h2 : Module.finrank ℤ (Q ⧸ P.comap Q.subtype) = 0 := by omega
  obtain ⟨n, hn, hz⟩ := Module.finrank_eq_zero_iff.1 h2 (Submodule.Quotient.mk ⟨y, hy⟩)
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  simpa using hz

theorem diag_eq_zero_iff_of_isPosDef {X₁ : Type} [AddCommGroup X₁] {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B) (z : X₁) :
    B z z = 0 ↔ z ∈ Submodule.torsion ℤ X₁ := by
  constructor
  · intro h0
    by_contra hz
    have hy : LinearIndependent ℤ ![z] := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      obtain rfl : i = 0 := Subsingleton.elim _ _
      by_contra hi
      have hg' : g 0 • z = 0 := by simpa using hg
      exact hz ((Submodule.mem_torsion_iff _).2 ⟨⟨g 0, mem_nonZeroDivisors_of_ne_zero hi⟩, hg'⟩)
    have := h 1 _ hy ![1] (by simp)
    simp [h0] at this
  · intro hz
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hz
    have ha' : (a : ℤ) • z = 0 := ha
    have h1 : ((a : ℤ) : ℝ) * B z z = 0 := by
      rw [← zsmul_eq_mul, ← map_smul, ha', map_zero]
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast nonZeroDivisors.ne_zero a.2)

theorem exists_radical_of_mem_psdCone {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone (bar := bar) (X := X)) : ∃ N : Submodule ℤ X, ∀ y, y ∈ N ↔ B y y = 0 := by
  obtain ⟨X₁, _, _, _, r, B₁, -, -, h1, h2⟩ := hB
  refine ⟨(Submodule.torsion ℤ X₁).comap r.toAddMonoidHom.toIntLinearMap, fun y => ?_⟩
  rw [h2, diag_eq_zero_iff_of_isPosDef h1]
  rfl

theorem exists_least_radical : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)),
    K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) →
      ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  intro O _ _ _ _ bar X _ _ _ K hne hK hadd
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  choose! N hN using fun B (hB : B ∈ K) => exists_radical_of_mem_psdCone (hK hB)
  have hnn : ∀ B ∈ K, ∀ y, 0 ≤ B y y := fun B hB y => nonneg_of_mem_psdCone (hK hB) y
  obtain ⟨B₁, hB₁, hmin⟩ : ∃ B₁ ∈ K, ∀ B ∈ K, Module.finrank ℤ (N B₁) ≤ Module.finrank ℤ (N B) :=
    ⟨Function.argminOn (fun B => Module.finrank ℤ (N B)) K hne, Function.argminOn_mem _ _ hne,
      fun B hB => Function.argminOn_le (fun B => Module.finrank ℤ (N B)) K hB⟩
  refine ⟨B₁, hB₁, fun B hB y hy => ?_⟩
  have hsum := hadd B hB B₁ hB₁
  have hle : N (B + B₁) ≤ N B₁ := fun z hz => by
    have h0 : B z z + B₁ z z = 0 := by simpa using (hN _ hsum z).1 hz
    exact (hN _ hB₁ z).2 (by linarith [hnn B hB z, hnn B₁ hB₁ z])
  obtain ⟨n, hn, hny⟩ := exists_smul_mem_of_le_of_finrank_le hle (hmin _ hsum) ((hN _ hB₁ y).2 hy)
  have h0 : B (n • y) (n • y) + B₁ (n • y) (n • y) = 0 := by simpa using (hN _ hsum _).1 hny
  have h1 : B (n • y) (n • y) = 0 := by linarith [hnn B hB (n • y), hnn B₁ hB₁ (n • y)]
  have h2 : ((n : ℝ) * (n : ℝ)) * B y y = 0 := by
    rw [← h1]
    simp only [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
    ring
  exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hn))

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeExistsMaximalSupportStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_cone_exists_maximal_support : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (K : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ)), K.Nonempty → K ⊆ psdCone (bar := bar) (X := X) → (∀ B ∈ K, ∀ B' ∈ K, B + B' ∈ K) → ∃ B₁ ∈ K, ∀ B ∈ K, ∀ y, B₁ y y = 0 → B y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_least_radical <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMem
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMem
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Orth

variable {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

def orthSum (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ) :
    (X₁ × X₂) →ₗ[ℤ] (X₁ × X₂) →ₗ[ℤ] ℝ :=
  B₁.compl₁₂ (LinearMap.fst ℤ X₁ X₂) (LinearMap.fst ℤ X₁ X₂) +
    B₂.compl₁₂ (LinearMap.snd ℤ X₁ X₂) (LinearMap.snd ℤ X₁ X₂)

theorem sum_basis_nonneg {K : Type} [Fintype K] (e : Module.Basis K ℤ X₁) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef B)
    (c : K → ℝ) : 0 ≤ ∑ k, ∑ l, c k * c l * B (e k) (e l) := by
  by_cases hc : c = 0
  · simp [hc]
  · exact ((isPosDef_iff_basis e B).1 h c hc).le

theorem isPosDef_orthSum {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (e₁ : Module.Basis K₁ ℤ X₁)
    (e₂ : Module.Basis K₂ ℤ X₂) {B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {B₂ : X₂ →ₗ[ℤ] X₂ →ₗ[ℤ] ℝ}
    (h₁ : IsPosDef B₁) (h₂ : IsPosDef B₂) : IsPosDef (orthSum B₁ B₂) := by
  rw [isPosDef_iff_basis (e₁.prod e₂)]
  intro c hc
  have key : ∑ i, ∑ j, c i * c j * orthSum B₁ B₂ ((e₁.prod e₂) i) ((e₁.prod e₂) j) =
      (∑ k, ∑ l, c (Sum.inl k) * c (Sum.inl l) * B₁ (e₁ k) (e₁ l)) +
        ∑ k, ∑ l, c (Sum.inr k) * c (Sum.inr l) * B₂ (e₂ k) (e₂ l) := by
    simp [Fintype.sum_sum_type, Finset.sum_add_distrib, orthSum]
  rw [key]
  by_cases h0 : (fun k => c (Sum.inl k)) = 0
  · have h3 : (fun k => c (Sum.inr k)) ≠ 0 := fun h3 => hc (by
      ext (k | k)
      · exact congrFun h0 k
      · exact congrFun h3 k)
    exact add_pos_of_nonneg_of_pos (sum_basis_nonneg e₁ h₁ _) ((isPosDef_iff_basis e₂ B₂).1 h₂ _ h3)
  · exact add_pos_of_pos_of_nonneg ((isPosDef_iff_basis e₁ B₁).1 h₁ _ h0) (sum_basis_nonneg e₂ h₂ _)

theorem isPosDef_compl_injective {Y : Type} [AddCommGroup Y] {C : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (h : IsPosDef C)
    (j : Y →ₗ[ℤ] X₁) (hj : Function.Injective j) : IsPosDef (C.compl₁₂ j j) := fun n x hx c hc => by
  simpa using h n (fun i => j (x i)) (hx.map' j (LinearMap.ker_eq_bot.2 hj)) c hc

end Orth

section DedekindLFunctions

variable (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]

theorem free_int_of_torsion_eq_bot (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (ht : Submodule.torsion O M = ⊥) : Module.Free ℤ M := by
  have : Module.Finite ℤ M := Module.Finite.trans O M
  have : HasUniqueDiv M := by
    refine ⟨fun n hn a b hab => ?_⟩
    change n • a = n • b at hab
    have h0 : ((n : ℕ) : O) ≠ 0 := by exact_mod_cast hn
    have h1 : ((n : ℕ) : O) • (a - b) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, smul_sub, hab, sub_self]
    have h2 : a - b ∈ Submodule.torsion O M :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨_, mem_nonZeroDivisors_of_ne_zero h0⟩, h1⟩
    rw [ht] at h2
    exact sub_eq_zero.1 h2
  exact Module.free_of_finite_type_torsion_free'

end DedekindLFunctions

theorem add_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone (bar := bar) (X := X) → B' ∈ psdCone (bar := bar) (X := X) → B + B' ∈ psdCone (bar := bar) (X := X) := by
  intro O _ _ _ _ bar X _ _ _ B B' hB hB'
  obtain ⟨X₁, _, _, _, r₁, B₁, hr₁, hb₁, hd₁, he₁⟩ := hB
  obtain ⟨X₂, _, _, _, r₂, B₂, hr₂, hb₂, hd₂, he₂⟩ := hB'
  have : Module.Finite O X₁ := Module.Finite.of_surjective r₁ hr₁
  have : Module.Finite O X₂ := Module.Finite.of_surjective r₂ hr₂
  have ht₁ : Submodule.torsion O X₁ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have ht₂ : Submodule.torsion O X₂ = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
  have : Module.Free ℤ X₁ := free_int_of_torsion_eq_bot O X₁ ht₁
  have : Module.Free ℤ X₂ := free_int_of_torsion_eq_bot O X₂ ht₂
  have : Module.Finite ℤ X₁ := Module.Finite.trans O X₁
  have : Module.Finite ℤ X₂ := Module.Finite.trans O X₂
  have hdef := isPosDef_orthSum (Module.Free.chooseBasis ℤ X₁) (Module.Free.chooseBasis ℤ X₂) hd₁ hd₂
  let r : X →ₗ[O] X₁ × X₂ := r₁.prod r₂
  let P := LinearMap.range r
  have htP : Submodule.torsion O P = ⊥ := by
    have ht : Submodule.torsion O (X₁ × X₂) = ⊥ := IsDedekindDomain.flat_iff_torsion_eq_bot.1 inferInstance
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨a, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    have h1 : (u : X₁ × X₂) ∈ Submodule.torsion O (X₁ × X₂) :=
      (Submodule.mem_torsion_iff _).2 ⟨a, by simpa using congrArg Subtype.val hau⟩
    rw [ht] at h1
    exact Subtype.ext h1
  have : Module.Flat O P := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htP
  have : Module.FinitePresentation O P := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O P := Module.Flat.projective_of_finitePresentation
  let j : P →ₗ[ℤ] X₁ × X₂ := P.subtype.toAddMonoidHom.toIntLinearMap
  refine ⟨P, inferInstance, inferInstance, hproj, r.rangeRestrict, (orthSum B₁ B₂).compl₁₂ j j,
    r.surjective_rangeRestrict, ⟨fun y z => ?_, fun a y z => ?_⟩,
    isPosDef_compl_injective hdef j Subtype.val_injective, fun a b => ?_⟩
  · change B₁ _ _ + B₂ _ _ = B₁ _ _ + B₂ _ _
    rw [hb₁.1, hb₂.1]
  · change B₁ (a • _) _ + B₂ (a • _) _ = B₁ _ (bar a • _) + B₂ _ (bar a • _)
    rw [hb₁.2, hb₂.2]
    rfl
  · change B a b + B' a b = B₁ (r₁ a) (r₁ b) + B₂ (r₂ a) (r₂ b)
    rw [he₁, he₂]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeAddMemStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_cone_add_mem : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), B ∈ psdCone (bar := bar) (X := X) → B' ∈ psdCone (bar := bar) (X := X) → B + B' ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | exact GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.add_mem_psdCone <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjection
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjection
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem eq_zero_of_zsmul_eq_zero_of_projective {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {n : ℤ} (hn : n ≠ 0) {z : P} (h : n • z = 0) : z = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O P)
  have hs' : ∀ x, Finsupp.linearCombination O (id : P → P) (s x) = x := fun x => LinearMap.congr_fun hs x
  have h0 : s z = 0 := by
    ext i
    have h1 : n • s z = 0 := by rw [← map_zsmul, h, map_zero]
    have h2 : (n : O) * s z i = 0 := by
      have := DFunLike.congr_fun h1 i
      simpa [zsmul_eq_mul] using this
    have h3 : (n : O) ≠ 0 := by exact_mod_cast hn
    simpa using (mul_eq_zero.1 h2).resolve_left h3
  rw [← hs' z, h0, map_zero]

theorem IsPosDef.eq_zero_of_apply_self {O : Type} [CommRing O] [IsDomain O] [CharZero O] {P : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P] {B : P →ₗ[ℤ] P →ₗ[ℤ] ℝ} (h : IsPosDef B) {z : P}
    (hz : B z z = 0) : z = 0 := by
  by_contra hne
  have hli : LinearIndependent ℤ ![z] := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    by_contra hi
    exact hne (eq_zero_of_zsmul_eq_zero_of_projective (O := O) hi (by simpa using hg))
  have := h 1 _ hli ![1] (by simp)
  simp [hz] at this

theorem exists_psdCone_descend (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hr : Function.Surjective r) (hB : B ∈ psdCone (bar := bar) (X := X))
    (hk : ∀ y, r y = 0 → B y y = 0) : ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  obtain ⟨X', _, _, _, r', B', hr', h1, h2, h3⟩ := hB
  have hker : LinearMap.ker r ≤ LinearMap.ker r' := fun y hy =>
    IsPosDef.eq_zero_of_apply_self (O := O) h2 (by rw [← h3]; exact hk y hy)
  let s : X₁ →ₗ[O] X' := ((LinearMap.ker r).liftQ r' hker) ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
  have hs : ∀ x, s (r x) = r' x := fun x => by
    have : (r.quotKerEquivOfSurjective hr).symm (r x) = (LinearMap.ker r).mkQ x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun z => by
    obtain ⟨x, rfl⟩ := hr' z
    exact ⟨r x, hs x⟩
  refine ⟨pullR s B', ⟨X', _, _, inferInstance, s, B', hsurj, h1, h2, fun _ _ => rfl⟩, ?_⟩
  ext a b
  simp [h3, hs]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeDescendsAlongSurjectionStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_cone_descends_along_surjection : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X X₁ : Type) [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁] (r : X →ₗ[O] X₁) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), Function.Surjective r → B ∈ psdCone (bar := bar) (X := X) → (∀ y, r y = 0 → B y y = 0) → ∃ B₁ ∈ psdCone (bar := bar) (X := X₁), B = pullR r B₁ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_psdCone_descend <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCover
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

section Pull

variable {O : Type} [CommRing O] {bar : O → O} {X X₁ : Type} [AddCommGroup X] [Module O X] [AddCommGroup X₁] [Module O X₁]

theorem isMin2_pullR_iff {r : X →ₗ[O] X₁} (hr : Function.Surjective r) (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (y : X) :
    IsMin2 (pullR r B) y ↔ IsMin2 B (r y) := by
  have e : ∀ x : X, r (y + (x + x)) = r y + (r x + r x) := fun x => by rw [map_add (f := _), map_add (f := _)]
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := hr x
    have := h x
    simp only [pullR_apply, e] at this
    exact this
  · intro h x
    simp only [pullR_apply, e]
    exact h (r x)

theorem pullR_mem_contact {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (h : B ∈ contact bar fun i => r (a i)) : pullR r B ∈ contact bar a :=
  ⟨pullR_mem_psdCone hr h.1, fun i => (isMin2_pullR_iff hr B (a i)).2 (h.2 i)⟩

theorem mem_contact_of_pullR {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {ι : Type} {a : ι → X}
    (hB : B ∈ psdCone (bar := bar) (X := X₁)) (h : pullR r B ∈ contact bar a) : B ∈ contact bar fun i => r (a i) :=
  ⟨hB, fun i => (isMin2_pullR_iff hr B (a i)).1 (h.2 i)⟩

end Pull

theorem isSpanned_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X),
      Covers2 a → IsSpanned bar (contact bar a) := by
  intro O _ _ _ _ bar red X _ _ _ _ ι _ a ha
  have hadd : ∀ B ∈ contact bar a, ∀ B' ∈ contact bar a, B + B' ∈ contact bar a := fun B hB B' hB' =>
    ⟨GlobalTheory.T.psd_cone_add_mem O bar X B B' hB.1 hB'.1, fun i x => by
      have h1 := hB.2 i x
      have h2 := hB'.2 i x
      simp only [LinearMap.add_apply]
      exact add_le_add h1 h2⟩
  obtain ⟨B₁, hB₁, hrad⟩ := GlobalTheory.T.psd_cone_exists_maximal_support O bar X (contact bar a) ⟨0, zero_mem_contact bar a⟩ (fun B hB => hB.1) hadd
  obtain ⟨X₁, _, _, _, r, B₁', hr, hbal, hdef, hfac⟩ := id hB₁.1
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  have hfac' : B₁ = pullR r B₁' := LinearMap.ext₂ hfac
  have hB₁' : B₁' ∈ contact bar fun i => r (a i) :=
    mem_contact_of_pullR hr (hdef.mem_psdCone hbal) (hfac' ▸ hB₁)
  have hcov : Covers2 fun i => r (a i) := fun y => by
    obtain ⟨y, rfl⟩ := hr y
    obtain ⟨i, x, rfl⟩ := ha y
    exact ⟨i, r x, by rw [map_add (f := _), map_add (f := _)]⟩
  obtain ⟨m, γ, hγ, hnn, hK, hsub⟩ :=
    GlobalTheory.T.contact_set_spans_of_pos_def O bar X₁ ι (fun i => r (a i)) (red X₁) hcov ⟨B₁', hB₁', hdef⟩
  refine ⟨m, fun i => pull r (γ i), fun i => pull_mem r (hγ i), fun i y => hnn i (r y), fun i => ?_, fun B hB => ?_⟩
  · have e : toReal (pull r (γ i)) = pullR r (toReal (γ i)) := LinearMap.ext₂ fun _ _ => by simp
    rw [e]
    exact pullR_mem_contact hr (hK i)
  · have hker : ∀ y, r y = 0 → B y y = 0 := fun y hy => hrad B hB y (by rw [hfac, hy]; simp)
    obtain ⟨B', hB', rfl⟩ := GlobalTheory.T.psd_cone_descends_along_surjection O bar X X₁ r B hr hB.1 hker
    obtain ⟨t, ht, e⟩ := hsub (mem_contact_of_pullR hr hB' hB)
    refine ⟨t, ht, LinearMap.ext₂ fun y z => ?_⟩
    simp [e, LinearMap.sum_apply]

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpannedOfCoverStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.contact_set_spanned_of_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), Covers2 a → IsSpanned bar (contact bar a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLift
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsNatCombOfToRealMemRcone
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_nat_comb_of_toReal_mem_rcone (X : Type) [AddCommGroup X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) (hβ : toReal β ∈ rcone γ) :
    ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i := by
  obtain ⟨t, ht0, ht⟩ := hβ
  let vec : X × X → Fin (m + 1) → ℤ := fun p =>
    Fin.snoc (α := fun _ => ℤ) (fun i => γ i p.1 p.2) (-(β p.1 p.2))
  obtain ⟨r, v, hreal, -⟩ :=
    GlobalTheory.MinkWeylReal.cone_orthant_fg (m + 1) ∅ (Set.range vec) Set.finite_empty
  let T : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) t 1
  have hpt : ∀ y z : X, (β y z : ℝ) = ∑ i, t i * (γ i y z : ℝ) := by
    intro y z
    have h := LinearMap.congr_fun (LinearMap.congr_fun ht y) z
    simpa [toReal, LinearMap.sum_apply] using h
  have hT : (∀ i, 0 ≤ T i) ∧ (∀ a ∈ (∅ : Set (Fin (m + 1) → ℤ)), ∑ i, (a i : ℝ) * T i ≤ 0) ∧
      (∀ b ∈ Set.range vec, ∑ i, (b i : ℝ) * T i = 0) := by
    refine ⟨fun i => ?_, fun a ha => absurd ha (Set.notMem_empty a), ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [T]
      · simpa [T] using ht0 j
    · rintro _ ⟨⟨y, z⟩, rfl⟩
      rw [Fin.sum_univ_castSucc]
      simp only [vec, T, Fin.snoc_castSucc, Fin.snoc_last]
      have h2 : ∑ x, ((γ x y z : ℤ) : ℝ) * t x = ∑ i, t i * (γ i y z : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have h3 := hpt y z
      push_cast
      linarith
  obtain ⟨c, hc0, hTc⟩ := (hreal T).1 hT
  have hlast : (1 : ℝ) = ∑ k, c k * (v k (Fin.last m) : ℝ) := by
    have h := congrFun hTc (Fin.last m)
    simpa [T, Finset.sum_apply] using h
  have hex : ∃ k, 0 < v k (Fin.last m) := by
    by_contra hno
    push_neg at hno
    have : ∑ k, c k * (v k (Fin.last m) : ℝ) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have : v k (Fin.last m) = 0 := Nat.le_zero.1 (hno k)
        simp [this]
    rw [this] at hlast
    exact one_ne_zero hlast
  obtain ⟨k, hk⟩ := hex
  have hv := (hreal (fun i => (v k i : ℝ))).2
    ⟨Pi.single k 1, fun j => by
      by_cases h : j = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h], by
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp⟩
  refine ⟨v k (Fin.last m), fun i => v k i.castSucc, hk, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have h := hv.2.2 (vec (y, z)) ⟨(y, z), rfl⟩
  rw [Fin.sum_univ_castSucc] at h
  simp only [vec, Fin.snoc_castSucc, Fin.snoc_last] at h
  have h' : ∑ i, γ i y z * (v k i.castSucc : ℤ) + -(β y z) * (v k (Fin.last m) : ℤ) = 0 := by
    exact_mod_cast h
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul]
  push_cast
  have h2 : ∑ i, (v k i.castSucc : ℤ) * γ i y z = ∑ i, γ i y z * (v k i.castSucc : ℤ) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLift
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem isMin2_sum_smul {X : Type} [AddCommGroup X] {m : ℕ} (B : Fin m → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c : Fin m → ℝ) (y : X)
    (hc : ∀ i, 0 ≤ c i) (hB : ∀ i, IsMin2 (B i) y) : IsMin2 (∑ i, c i • B i) y := by
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i x) (hc i)

def sumDiag {X ι : Type} [AddCommGroup X] [Fintype ι] (g : ℕ) (p : ι → X) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := 2 ^ g * ∑ y, β (p y) (p y)
  map_add' β γ := by
    simp only [LinearMap.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' k β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem isCell_vorFun_of_contact : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ)
    (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) →
    (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ →
    IsCell bar (vorFun O g) γ := by
  intro O _ _ _ _ bar g X _ _ _ _ n r a hr ha m γ hbal hpsd hcon hsub
  have hval := (vorFun_value_le O bar g X n r a hr ha).2
  have hreal : ∀ (β : LinearMap.BilinForm ℤ X) , (∀ y, 0 ≤ β y y) → ∀ y, 0 ≤ toReal β y y := fun β hβ y => by
    simpa [toReal_apply] using hβ y
  have hℓ : ∀ β : LinearMap.BilinForm ℤ X, ((sumDiag g (fun y => r (a y)) β : ℤ) : ℝ) =
      2 ^ g * ∑ y, toReal β (r (a y)) (r (a y)) := fun β => by
    simp [sumDiag, toReal_apply]
  have hgen : ∀ i, (2 : ℝ) ^ n * (vorFun O g).evalZ (γ i) = sumDiag g (fun y => r (a y)) (γ i) := fun i => by
    rw [hℓ, ← evalR_toReal]
    exact (hval _ (hreal _ (hpsd i))).2.2 (hcon i).2
  refine ⟨hbal, hpsd, (linearOn_iff _ γ).2 fun c hc => ?_, 2 ^ n, sumDiag g (fun y => r (a y)), by positivity, ?_, ?_, ?_⟩
  · have hS : ∀ y, 0 ≤ (∑ i, c i • toReal (γ i)) y y := fun y => by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (hreal _ (hpsd i) y)
    have h1 := (hval _ hS).2.2 fun y => isMin2_sum_smul _ c _ hc fun i => (hcon i).2 y
    have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
    refine mul_left_cancel₀ hp (h1.trans ?_)
    have h2 : ∀ i, (2 : ℝ) ^ g * ∑ y, toReal (γ i) (r (a y)) (r (a y)) = 2 ^ n * (vorFun O g).evalZ (γ i) := fun i => by
      rw [hgen, hℓ]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, h2, mul_left_comm]
  · intro i
    push_cast
    exact (hgen i).symm
  · intro β _ hβ
    have h := (hval _ (hreal β hβ)).1
    rw [evalR_toReal] at h
    rw [hℓ]
    push_cast
    exact h
  · intro β hb hβ he
    have hmin : ∀ y, IsMin2 (toReal β) (r (a y)) := by
      refine (hval _ (hreal β hβ)).2.1 ?_
      rw [evalR_toReal, ← hℓ]
      exact_mod_cast he
    have hpc : toReal β ∈ psdCone (bar := bar) (X := X) := by
      simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hb]) (by simp [hβ]) (by simp)
    exact exists_nat_comb_of_toReal_mem_rcone X m γ β (hsub ⟨hpc, hmin⟩)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MemConeOfModTwoLiftStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (n : ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ), Function.Surjective r → (∀ y, redV 1 (a y) = y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, toReal (γ i) ∈ contact bar fun y => r (a y)) → (contact bar fun y => r (a y)) ⊆ rcone γ → IsCell bar (vorFun O g) γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact | exact GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isCell_vorFun_of_contact <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbits
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_vorFun_cells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro O _ _ _ _ bar g hcov X _ _ _ _
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' ℤ X
  obtain ⟨k, nP, P, hPs, hPp, hPc⟩ := hcov X
  have hcls : ∀ (j : Fin k) (y : Fin n → ZMod (1 + 1)), ∃ F : Finset (Fin n → ℤ), (∀ a ∈ F, redV 1 a = y) ∧
      ∀ B ∈ rcone (P j), ∃ a ∈ F, ∀ a', redV 1 a' = y → B (r a) (r a) ≤ B (r a') (r a') := by
    intro j y
    obtain ⟨F, hF⟩ := GlobalTheory.dickson_finite_below_every (ι := {a : Fin n → ℤ // redV 1 a = y}) (nP j)
      fun a i => (P j i (r a.1) (r a.1)).toNat
    refine ⟨F.map (Function.Embedding.subtype _), fun a ha => ?_, ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 ha
      exact a.2
    · rintro B ⟨t, ht, rfl⟩
      have hval : ∀ a : Fin n → ℤ, (∑ i, t i • toReal (P j i)) (r a) (r a) = ∑ i, t i * (P j i (r a) (r a) : ℝ) := fun a => by
        simp [LinearMap.sum_apply]
      obtain ⟨a0, ha0, -⟩ := hF ⟨_, (redV_surjective 1 n y).choose_spec⟩
      obtain ⟨a1, ha1, hmin⟩ := Finset.exists_min_image (F.map (Function.Embedding.subtype _))
        (fun a => (∑ i, t i • toReal (P j i)) (r a) (r a)) ⟨_, Finset.mem_map_of_mem _ ha0⟩
      refine ⟨a1, ha1, fun a ha => ?_⟩
      obtain ⟨a', ha', hle⟩ := hF ⟨a, ha⟩
      refine (hmin _ (Finset.mem_map_of_mem _ ha')).trans ?_
      simp only [Function.Embedding.subtype_apply, hval]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have h1 := hle i
      have h2 := hPp j i (r a'.1)
      have h3 := hPp j i (r a)
      simp only at h1
      exact_mod_cast (by omega : P j i (r a'.1) (r a'.1) ≤ P j i (r a) (r a))
  choose F hFred hFmin using hcls
  have hred : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)) (y : Fin n → ZMod (1 + 1)), redV 1 (c y).1 = y :=
    fun j c y => hFred j y _ (c y).2
  have cell : ∀ (j : Fin k) (c : ∀ y, ↥(F j y)), ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X),
      IsCell bar (vorFun O g) γ ∧ (contact bar fun y => r (c y).1) ⊆ rcone γ := by
    intro j c
    have hcv := (vorFun_value_le O bar g X n r (fun y => (c y).1) hr (hred j c)).1
    obtain ⟨s, γ, h1, h2, h3, h4⟩ := GlobalTheory.T.contact_set_spanned_of_cover O bar hcov X _ _ hcv
    exact ⟨s, γ, GlobalTheory.T.isCell_vorFun_of_contact_subset_rcone O bar g X n r _ hr (hred j c) s γ h1 h2 h3 h4, h4⟩
  choose s γ hγ hγc using cell
  refine ⟨⋃ j, ⋃ c, Set.range (γ j c), Set.finite_iUnion fun j => Set.finite_iUnion fun c => Set.finite_range _,
    fun B hB => ?_⟩
  obtain ⟨e, j, c, hc0, hce⟩ := hPc B hB
  have hB' : pullR e.toLinearMap B ∈ psdCone (bar := bar) (X := X) := pullR_mem_psdCone e.surjective hB
  have hBP : pullR e.toLinearMap B ∈ rcone (P j) := ⟨c, hc0, hce⟩
  choose a0 ha0F ha0 using fun y => hFmin j y _ hBP
  let d : ∀ y, ↥(F j y) := fun y => ⟨a0 y, ha0F y⟩
  have hcon : pullR e.toLinearMap B ∈ contact bar fun y => r (d y).1 := by
    refine ⟨hB', fun y x => ?_⟩
    obtain ⟨b, rfl⟩ := hr x
    have hb : redV 1 (a0 y + (b + b)) = y := by
      have h2 : a0 y + (b + b) = a0 y + (((1 : ℕ) : ℤ) + 1) • b := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [h2, redV_add_smul]
      exact hFred j y _ (ha0F y)
    simpa only [map_add (f := _)] using ha0 y _ hb
  obtain ⟨c', hc', hBc⟩ := hγc j d hcon
  exact ⟨e, _, γ j d, c', hγ j d, fun i => Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨d, i, rfl⟩⟩, hc', hBc⟩

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbitsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.psd_cone_finitely_many_orbits : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := bar) (X := X), ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar (vorFun O g) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells | exact GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.exists_vorFun_cells <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFunctionIntegralPositive
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFunctionIntegralPositive
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_least_points {X : Type} [AddCommGroup X] {n : ℕ} (r : (Fin n → ℤ) →ₗ[ℤ] X)
    (hr : Function.Surjective r) (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y) :
    ∃ a : (Fin n → ZMod (1 + 1)) → Fin n → ℤ, (∀ y, redV 1 (a y) = y) ∧ ∀ y, IsMin2 (toReal β) (r (a y)) := by
  have hmin : ∀ y : Fin n → ZMod (1 + 1), ∃ c : Fin n → ℤ, redV 1 c = y ∧
      ∀ c', redV 1 c' = y → β (r c) (r c) ≤ β (r c') (r c') := fun y => by
    obtain ⟨c0, h0⟩ := redV_surjective 1 n y
    obtain ⟨c, hc, hm⟩ := WellFounded.has_min
      (InvImage.wf (fun c : Fin n → ℤ => (β (r c) (r c)).toNat) Nat.lt_wfRel.wf)
      {c | redV 1 c = y} ⟨c0, h0⟩
    refine ⟨c, hc, fun c' hc' => ?_⟩
    have h1 : ¬ (β (r c') (r c')).toNat < (β (r c) (r c)).toNat := hm c' hc'
    have h2 := hβ (r c)
    have h3 := hβ (r c')
    omega
  choose a ha hm using hmin
  refine ⟨a, ha, fun y x => ?_⟩
  obtain ⟨d, rfl⟩ := hr x
  have h := hm y (a y + (((1 : ℕ) : ℤ) + 1) • d) (by rw [redV_add_smul, ha])
  have e : r (a y + (((1 : ℕ) : ℤ) + 1) • d) = r (a y) + (r d + r d) := by
    rw [map_add (f := _), map_smul, show (((1 : ℕ) : ℤ) + 1) = 2 by norm_num, two_smul]
  rw [e] at h
  simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
  exact_mod_cast h

theorem apply_eq_zero_of_self {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {z : X} (hz : β z z = 0) (w : X) : β z w = 0 := by
  by_contra ht
  have h := hβ (w + (-(β w w + 1) * β z w) • z)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hz, hs w z] at h
  have h1 : 1 ≤ β z w * β z w := mul_self_pos.2 ht
  have h2 := hβ w
  nlinarith

theorem eq_zero_of_covers {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y)
    (hβ : ∀ y, 0 ≤ β y y) {ι : Type} {a : ι → X} (hc : Covers2 a) (h0 : ∀ i, β (a i) (a i) = 0) : β = 0 := by
  have hdiv : ∀ (k : ℕ) (z w : X), (2 : ℤ) ^ k ∣ β z w := by
    intro k
    induction k with
    | zero => intro z w; simp
    | succ k ih =>
      intro z w
      obtain ⟨i, x, rfl⟩ := hc z
      obtain ⟨m, hm⟩ := ih x w
      refine ⟨m, ?_⟩
      simp only [map_add (f := _), LinearMap.add_apply, apply_eq_zero_of_self β hs hβ (h0 i) w, hm]
      ring
  refine LinearMap.ext₂ fun z w => ?_
  refine Int.eq_zero_of_abs_lt_dvd (hdiv (β z w).natAbs z w) ?_
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_two_pow_self

theorem vorFun_int_pos : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q →
    (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  intro O _ _ _ _ bar g q X _ _ _ _ hg hq
  have hfin : Module.Finite ℤ X := Module.Finite.trans O X
  have hO : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  have htf : Module.IsTorsionFree ℤ X := Module.IsTorsionFree.trans O
  have hfree : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  have hn : Module.finrank ℤ X ≤ g := by
    rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := O) (M := X)]
    exact (Nat.mul_le_mul_left _ hq).trans hg
  let b : Module.Basis (Fin (Module.finrank ℤ X)) ℤ X := Module.finBasis ℤ X
  let r : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X := b.equivFun.symm.toLinearMap
  have hr : Function.Surjective r := b.equivFun.symm.surjective
  have key : ∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) →
      ∃ a : (Fin (Module.finrank ℤ X) → ZMod (1 + 1)) → Fin (Module.finrank ℤ X) → ℤ, Covers2 (fun y => r (a y)) ∧
        (vorFun O g).evalZ β = 2 ^ (g - Module.finrank ℤ X) * ∑ y, (β (r (a y)) (r (a y)) : ℝ) := by
    intro β hβ
    obtain ⟨a, ha, hm⟩ := exists_least_points r hr β hβ
    obtain ⟨hc, h⟩ := vorFun_value_le O bar g X _ r a hr ha
    refine ⟨a, hc, ?_⟩
    have hB : ∀ y, 0 ≤ toReal β y y := fun y => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
      exact_mod_cast hβ y
    have h1 := ((h (toReal β) hB).2).2 hm
    rw [evalR_toReal] at h1
    have h2 : ∀ u v, toReal β u v = (β u v : ℝ) := fun u v => by
      simp only [toReal, LinearMap.compr₂_apply, Algebra.linearMap_apply, eq_intCast]
    simp only [h2] at h1
    have h3 : (2 : ℝ) ^ g = 2 ^ Module.finrank ℤ X * 2 ^ (g - Module.finrank ℤ X) := by
      rw [← pow_add, Nat.add_sub_cancel' hn]
    rw [h3, mul_assoc] at h1
    exact mul_left_cancel₀ (by positivity) h1
  refine ⟨fun β hβ => ?_, fun β hs hβ hne => ?_⟩
  · obtain ⟨a, -, h⟩ := key β hβ
    exact ⟨2 ^ (g - Module.finrank ℤ X) * ∑ y, β (r (a y)) (r (a y)), by rw [h]; push_cast; rfl⟩
  · obtain ⟨a, hc, h⟩ := key β hβ
    have hnn : ∀ y, (0 : ℝ) ≤ (β (r (a y)) (r (a y)) : ℝ) := fun y => by exact_mod_cast hβ _
    rw [h]
    refine mul_pos (by positivity) (lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hnn y) fun h0 => hne ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn y).1 h0.symm
    exact eq_zero_of_covers β hs hβ hc fun y => by exact_mod_cast h1 y (Finset.mem_univ y)

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFunctionIntegralPositiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.voronoi_function_integral_positive : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank ℤ O * q ≤ g → Module.finrank O X ≤ q → (∀ β : LinearMap.BilinForm ℤ X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (vorFun O g).evalZ β = n) ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (vorFun O g).evalZ β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos | exact GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.vorFun_int_pos <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunHomogSuperadd
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem evalR_vorFun_eq (O : Type) [CommRing O] [Module.Finite ℤ O] (g : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Finite ℤ X] {d : ℕ} {s : (Fin d → ℤ) →ₗ[ℤ] X} (hs : Function.Surjective s)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (vorFun O g) B = (fineDen g {1} : ℝ) *
      ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ * ∑ y, classMin 1 (fun a b => B (s a) (s b)) y := by
  have h0 : zeroFun.eval X (fun a b => B a b) = 0 := by
    rw [zeroFun.eval_eq hs]
    rfl
  rw [evalR, vorFun, eval_baseFun, h0, Finset.sum_singleton, fineMean_eval_eq 1 hs, zero_add, mul_assoc]

theorem vorFun_homog_superadd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (g : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone (bar := bar) (X := X), ∀ t : ℝ, 0 ≤ t → evalR (vorFun O g) (t • B) = t * evalR (vorFun O g) B) ∧
    ∀ B ∈ psdCone (bar := bar) (X := X), ∀ B' ∈ psdCone (bar := bar) (X := X),
      evalR (vorFun O g) B + evalR (vorFun O g) B' ≤ evalR (vorFun O g) (B + B') := by
  intro O _ _ _ _ bar g X _ _ _
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  have hc : (0 : ℝ) ≤ (fineDen g {1} : ℝ) * ((((1 : ℕ) : ℝ) + 1) ^ d)⁻¹ := by positivity
  refine ⟨fun B _ t ht => ?_, fun B hB B' hB' => ?_⟩
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs]
    simp only [LinearMap.smul_apply, smul_eq_mul, classMin_smul ht, ← Finset.mul_sum]
    ring
  · rw [evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, evalR_vorFun_eq O g hs, ← mul_add,
      ← Finset.sum_add_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hc
    simp only [LinearMap.add_apply]
    exact classMin_add_le (fun a => nonneg_of_mem_psdCone hB _) (fun a => nonneg_of_mem_psdCone hB' _) y

end GlobalTheory.CompanionTheory.Ar.Fan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedral
set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_isPolyFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  intro O _ _ _ _ bar g q hred hg X _ _ _ _ hX
  obtain ⟨hhom, hsup⟩ := vorFun_homog_superadd O bar g X
  obtain ⟨hint, hpos⟩ := GlobalTheory.T.voronoi_function_integral_positive O bar g q X hg hX
  exact
    { homog := hhom
      superadd := hsup
      integral := fun β _ h => hint β h
      pos := fun β hβ h h0 => hpos β hβ.1 h h0
      finite := GlobalTheory.T.psd_cone_finitely_many_orbits O bar g hred X }

end GlobalTheory.CompanionTheory.Ar.Fan
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedralStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.voronoi_fan_is_polyhedral : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ), (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) → Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan | exact GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan <;> assumption)
end
