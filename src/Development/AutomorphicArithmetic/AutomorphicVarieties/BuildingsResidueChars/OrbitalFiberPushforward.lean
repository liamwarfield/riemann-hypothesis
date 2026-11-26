module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforwardEqZero
open MulAction

theorem UpperTheory.orbitalFiber_pushforward_eq_zero :
    UpperTheory.V.Z.Sym.Glob.Fib.PushZero := by
  intro H Y _ _ H₀ k hidx htriv hk hfin
  classical
  have hout : ∀ (o : orbitRel.Quotient H Y) (y : Y),
      (Quotient.mk (orbitRel H Y) y : orbitRel.Quotient H Y) = o ↔ y ∈ orbit H o.out := by
    intro o y
    rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel H Y), Quotient.out_eq]
  have hkeq : ∀ (x y : Y), y ∈ orbit H x → k y = k x := by
    rintro x y ⟨h, rfl⟩
    exact hk h x
  set S : Finset Y := hfin.toFinset with hS
  have hmem : ∀ y, y ∈ S ↔ k y ≠ 0 := by
    intro y; simp [hS]
  let q : Y → orbitRel.Quotient H Y := fun y => Quotient.mk (orbitRel H Y) y
  have h1 : ∑ᶠ y, k y = ∑ y ∈ S, k y := finsum_eq_sum k hfin
  have h2 : UpperTheory.V.Z.Sym.gq H₀ k =
      ∑ o ∈ S.image q, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ) := by
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_sum_of_support_subset
    intro o ho
    have hne : k o.out ≠ 0 := by
      intro h0
      exact ho (by simp [h0])
    simp only [Finset.coe_image]
    exact ⟨o.out, by simpa [hmem] using hne, Quotient.out_eq o⟩
  rw [h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image q) (g := q)
    (fun y hy => Finset.mem_image_of_mem q hy), Finset.sum_div]
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨y₀, hy₀, hy₀o⟩ := Finset.mem_image.mp ho
  have hne : k o.out ≠ 0 := by
    rw [← hkeq o.out y₀ ((hout o y₀).mp hy₀o)]
    exact (hmem y₀).mp hy₀
  have hset : ((S.filter fun y => q y = o : Finset Y) : Set Y) = orbit H o.out := by
    ext y
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · exact fun h => (hout o y).mp h.2
    · intro h
      exact ⟨(hmem y).mpr (by rw [hkeq _ _ h]; exact hne), (hout o y).mpr h⟩
  have hcard : (S.filter fun y => q y = o).card = (stabilizer H o.out).index := by
    rw [index_stabilizer, ← hset, Set.ncard_coe_finset]
  have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
  have hmul := Subgroup.relIndex_mul_index hle
  have hsum : ∑ y ∈ S with q y = o, k y = ((stabilizer H o.out).index : ℂ) * k o.out := by
    rw [Finset.sum_congr rfl (g := fun _ => k o.out), Finset.sum_const, hcard, nsmul_eq_mul]
    intro y hy
    exact hkeq _ _ ((hout o y).mp (Finset.mem_filter.mp hy).2)
  rw [← hmul] at hidx
  have ha : ((H₀.relIndex (stabilizer H o.out) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hidx)
  have hb : (((stabilizer H o.out).index : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hidx)
  rw [hsum, ← hmul, Nat.cast_mul]
  field_simp
end

open MulAction

theorem UpperTheory.orbitalFiber_pushforward :
    UpperTheory.V.Z.Sym.Glob.Fib.Push := by
  intro H X' X _ _ _ H₀ q k hN hq hH₀ hk hT hfin hidx
  classical
  let F : orbitRel.Quotient H X → Set X' := fun i => {y | q y = Quotient.out i}
  letI act : ∀ i : orbitRel.Quotient H X, MulAction (stabilizer H (Quotient.out i)) (F i) := fun i =>
    { smul := fun h y => ⟨(h : H) • (y : X'), by
          show q ((h : H) • (y : X')) = Quotient.out i
          rw [hq, show q (y : X') = Quotient.out i from y.2]
          exact mem_stabilizer_iff.mp h.2⟩
      one_smul := fun y => Subtype.ext (one_smul H (y : X'))
      mul_smul := fun a b y => Subtype.ext (mul_smul (a : H) (b : H) (y : X')) }
  have hD := UpperTheory.orbitalFiber_decomposition H X' (orbitRel.Quotient H X) H₀ k
    (fun i => stabilizer H (Quotient.out i)) (fun i => F i)
    (fun i => (stabilizer H (Quotient.out i)).subtype) (fun i y => (y : X'))
    (fun i y => k (y : X')) hN hk hT
    (fun i h y => rfl) (fun i => Subtype.val_injective)
    (fun i h y => hk (h : H) (y : X')) (fun i y _ => rfl) ?cover ?disj
  case cover =>
    intro x hx
    obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.mk_out (s := orbitRel H X) (q x))
    refine ⟨Quotient.mk _ (q x), ⟨g • x, ?_⟩, g⁻¹, ?_, ?_⟩
    · show q (g • x) = _
      rw [hq]; exact hg
    · show k (g • x) ≠ 0
      rw [hk]; exact hx
    · show x = g⁻¹ • g • x
      rw [inv_smul_smul]
  case disj =>
    intro i j y y' h _ _ he
    have hqe : h • Quotient.out i = Quotient.out j := by
      have h1 : q (h • (y : X')) = q (y' : X') := congrArg q he
      rw [hq, show q (y : X') = Quotient.out i from y.2,
        show q (y' : X') = Quotient.out j from y'.2] at h1
      exact h1
    have hij : i = j := by
      rw [← Quotient.out_eq i, ← Quotient.out_eq j]
      exact (Quotient.sound (orbitRel_apply.mpr ⟨h, hqe⟩)).symm
    subst hij
    refine ⟨rfl, ?_⟩
    rw [Subgroup.range_subtype]
    exact mem_stabilizer_iff.mpr hqe
  rw [hD]
  conv_rhs => unfold UpperTheory.V.Z.Sym.gq
  refine finsum_congr (fun i => ?_)
  beta_reduce
  by_cases hz : ∃ y : X', q y = Quotient.out i ∧ k y ≠ 0
  · obtain ⟨y₀, hy₀, hk₀⟩ := hz
    have hind : (Subgroup.comap (stabilizer H (Quotient.out i)).subtype H₀).index ≠ 0 := by
      have := hidx y₀ hk₀
      rw [hy₀] at this
      exact this
    rw [UpperTheory.orbitalFiber_pushforward_eq_zero _ (F i) _ _ hind
      (fun z hz y => Subtype.ext (hH₀ (z : H) (Subgroup.mem_comap.mp hz) (y : X')))
      (fun h y => hk (h : H) (y : X'))
      (((hfin (Quotient.out i)).preimage Subtype.val_injective.injOn).subset
        (fun y hy => ⟨y.2, hy⟩))]
    rw [finsum_set_coe_eq_finsum_mem (f := k) (F i)]
    rfl
  · push_neg at hz
    have h0 : (∑ᶠ (y : X') (_ : q y = Quotient.out i), k y) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro y
      rw [finsum_eq_if]
      split_ifs with hy
      · exact hz y hy
      · rfl
    rw [h0, zero_div]
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_zero_of_forall_eq_zero
    intro o
    beta_reduce
    rw [hz _ (Quotient.out o).2, zero_div]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ClassicalFormsLevelMonotoneAndUpStable
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem lower_step {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω) (φ : X.I.T →* Ωˣ) (U : Subgroup X.Ub) (c : ℕ)
    (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) :
    ∀ F ∈ X.Cl τ W.ξ U (c + 1) φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Cl τ W.ξ U c φ := by
  classical
  intro F hF
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) X.I.z X.I.z_mem
  have hsum : X.UF m W ⟨X.I.z, X.I.z_mem⟩ F =
      (((W.χ ⟨X.I.z, X.I.P_le _ X.I.z_mem⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * X.I.z) F := by
    rw [← (h2 s hs hu).2 F hF.2.1]; rfl
  refine ⟨?_, ?_⟩
  · rw [hsum]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
    · change F i (X.glob γ * g * (1, u * X.I.z)) = _ *ᵥ F i (g * (1, u * X.I.z))
      rw [mul_assoc]
      exact hF.1.1 i trivial γ _
    · rw [(ctrlEq Γ Ga Gp X O Ω W m τ).2.2, hF.1.2 w hw]
  · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ hφ).2 F hF.2)

theorem UpperTheory.classicalForms_level_monotone_and_Up_stable :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type)
      [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ)
      (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ),
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ) ∧
      (∀ F ∈ X.ClO W τ U c φ, X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U c φ) ∧
      ∀ e n : ℕ, e ≤ n → ∀ F ∈ X.ClO W τ U (c + e) φ,
        (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ n) F ∈ X.ClO W τ U c φ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c hφ
  have mono : ∀ c', c ≤ c' → X.ClO W τ U c φ ≤ X.ClO W τ U c' φ := by
    intro c' hc F hF
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hF
    refine Submodule.mem_inf.2 ⟨h1, ?_⟩
    exact ⟨h2.1, fun y hy => h2.2.1 y (X.I.Nm_anti hc hy), h2.2.2⟩
  have step : ∀ e, ∀ F ∈ X.ClO W τ U (c + e + 1) φ,
      X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.ClO W τ U (c + e) φ := by
    intro e F hF
    exact lower_step X W _ _ U (c + e)
      (fun t ht => by simp [hφ t (X.I.Tc_anti (Nat.le_add_right c e) ht)]) F hF
  have down : ∀ e, ∀ F ∈ X.ClO W τ U (c + e) φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ e) F ∈ X.ClO W τ U c φ := by
    intro e
    induction e with
    | zero =>
      intro F hF
      simpa using hF
    | succ e ih =>
      intro F hF
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (step e F hF)
  have stay : ∀ k, ∀ F ∈ X.ClO W τ U c φ,
      (X.UF m W ⟨X.I.z, X.I.z_mem⟩ ^ k) F ∈ X.ClO W τ U c φ := by
    intro k
    induction k with
    | zero =>
      intro F hF
      simpa using hF
    | succ k ih =>
      intro F hF
      rw [pow_succ, mul_apply_eq_comp]
      exact ih _ (step 0 F (mono _ (Nat.le_succ c) hF))
  refine ⟨mono, fun F hF => step 0 F (mono _ (Nat.le_succ c) hF), ?_⟩
  intro e n hen F hF
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hen
  rw [add_comm e k, pow_add, mul_apply_eq_comp]
  exact stay k _ (down e F hF)
end
