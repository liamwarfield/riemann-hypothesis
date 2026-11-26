module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFiniteOrder

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem two_smul_pow {G M : Type*} [Group G] [AddCommGroup M] (q : G → M) (q1 : q 1 = 0)
    (hq : ∀ x y : G, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹) (ψ : G) (n : ℕ) :
    (2 : ℤ) • q (ψ ^ n) = ((n : ℤ) * (n + 1)) • q ψ + ((n : ℤ) * (n - 1)) • q ψ⁻¹ := by
  induction n using Nat.twoStepInduction with
  | zero => simp [q1]
  | one => simp [two_zsmul]
  | more n h0 h1 =>
    have h := hq (ψ ^ (n + 1)) ψ
    rw [← pow_succ, pow_succ ψ n, mul_inv_cancel_right, ← pow_succ] at h
    push_cast at h1 ⊢
    linear_combination (norm := module) (2 : ℤ) • h - h0 + (2 : ℤ) • h1

theorem pull_one_eq_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h0 : pull (η[A]).left c = 0 := GlobalTheory.cechPic_sp_field_eq_zero K _
  rw [Hom.one_def, Over.comp_left, pull_comp, h0, map_zero]

theorem pull_iter {S : Scheme.{0}} {A : Over S} (σ : A ≅ A) (c : Pic A.left)
    (h : pull σ.hom.left c = c) (m : ℕ) : pull (GlobalTheory.SerreField.iter σ m).hom.left c = c := by
  induction m with
  | zero => exact pull_id c
  | succ m ih =>
    change pull ((GlobalTheory.SerreField.iter σ m).hom.left ≫ σ.hom.left) c = c
    rw [pull_comp, h, ih]

theorem eff_add_nsmul {X : Scheme.{0}} [IsIntegral X] {a b : Pic X} (ha : Eff a) (hb : Eff b) (k : ℕ) :
    Eff (a + k • b) := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [succ_nsmul, ← add_assoc]; exact eff_add _ _ ih hb

theorem exists_ge_cast_ne_zero (K : Type) [Field K] (t : ℕ) : ∃ n : ℕ, t ≤ n ∧ (n : K) ≠ 0 := by
  by_cases h : (t : K) = 0
  · exact ⟨t + 1, by omega, by simp [h]⟩
  · exact ⟨t, le_rfl, h⟩

theorem finiteOrder_of_const_of_cube :
    GlobalTheory.AmpleRigid.ConstSt → GlobalTheory.AmpleRigid.CubeSt → GlobalTheory.AmpleRigid.FiniteOrderSt := by
  intro hConst hCube K _ _ A _ _ hA L hL hAmp σ hσ hfix
  haveI : IsIntegral A.left := GlobalTheory.SS.isIntegral_of_abelian A hA
  let q : (A ⟶ A) → Pic A.left := fun u => pull u.left (cls L hL)
  have q1 : q 1 = 0 := pull_one_eq_zero A _
  have hq : ∀ x y : A ⟶ A, q (x * y) + q (x * y⁻¹) = q x + q x + q y + q y⁻¹ := by
    intro x y
    have h : q (x * y * y⁻¹) + q x + q y + q y⁻¹ = q (x * y) + q (x * y⁻¹) + q (y * y⁻¹) + q 1 :=
      hCube K A hA L hL hAmp (cls L hL) x y y⁻¹
    rw [mul_inv_cancel_right, mul_inv_cancel, q1, add_zero, add_zero] at h
    exact h.symm
  obtain ⟨d, hd, r, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hAmp
  have heff : ∀ u : A ⟶ A, Eff ((d : ℤ) • q u) := fun u => by
    have h := eff_pull_of_veryAmpleBy K A.hom _ r s (GlobalTheory.AbLaw.isLB_pw hL d) hs u.left inferInstance
    rwa [cls_pw hL, map_zsmul] at h
  obtain ⟨t₀, ht₀⟩ := hConst K A hA L hL hAmp
    ((2 * d : ℤ) • (q (𝟙 A) + q (𝟙 A) + q (𝟙 A) + q (𝟙 A)⁻¹))
  obtain ⟨n, hn, hnK⟩ := exists_ge_cast_ne_zero K t₀
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hnK)
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA (k + 1) hnK
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.SerreField.exists_iter_fix σ (𝟙_ (Over (Sp K))) (k + 1)
  refine ⟨m, hm0, ?_⟩
  have hx : q (GlobalTheory.SerreField.iter σ m).hom = q (𝟙 A) := (pull_iter σ _ hfix m).trans (pull_id _).symm
  have hxm : IsMonHom (GlobalTheory.SerreField.iter σ m).hom := inferInstance
  generalize (GlobalTheory.SerreField.iter σ m).hom = x at hm hx hxm ⊢
  have hu : IsMonHom (x * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, e⟩ := hdiv _ hu (fun y hy => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hm y hy, Category.comp_id, mul_inv_cancel])
  have h1 := hq x (𝟙 A)
  rw [hx, e] at h1
  have h2 := two_smul_pow q q1 hq ψ (k + 1)
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * ((k + 1) * (k + 2))) (hn.trans ?_) ψ hψ ?_
    · nlinarith [Nat.zero_le k, Nat.mul_le_mul_right ((k + 1) * (k + 2)) hd]
    · have h3 := eff_add_nsmul (eff_add _ _ (heff (x * 𝟙 A)) (heff (x * 𝟙 A))) (heff ψ⁻¹) ((k + 1) * k)
      convert h3 using 1
      change _ - _ • q ψ = _
      rw [← natCast_zsmul, ← natCast_zsmul]
      push_cast at h2 ⊢
      linear_combination (norm := module) (d : ℤ) • h2 - (2 * d : ℤ) • h1
  rw [hψ1, one_pow] at e
  exact mul_inv_eq_one.1 e

end GlobalTheory.AmpleFiniteOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSeparated
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.EffBound

theorem pull_one_left_eq_zero {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h : pull (η[A] : 𝟙_ (Over (Sp K)) ⟶ A).left c = 0 := GlobalTheory.ThetaExtend.pic_local (R := K) _
  rw [Hom.one_def, Over.comp_left, pull_comp, h, map_zero]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

theorem pull_pow_left (hcube : CubeSt) {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L)
    (c : Pic A.left) (ψ : A ⟶ A) (n : ℕ) :
    pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c := by
  have hrec : ∀ n : ℕ, pull (ψ ^ (n + 2)).left c + pull (ψ ^ n).left c =
      2 • pull (ψ ^ (n + 1)).left c + pull ψ.left c + pull ψ⁻¹.left c := by
    intro n
    have h := hcube K A hA L hL hamp c (ψ ^ (n + 1)) ψ ψ⁻¹
    have e1 : ψ ^ (n + 1) * ψ * ψ⁻¹ = ψ ^ (n + 1) := mul_inv_cancel_right _ _
    have e2 : ψ ^ (n + 1) * ψ = ψ ^ (n + 2) := (pow_succ _ _).symm
    have e3 : ψ ^ (n + 1) * ψ⁻¹ = ψ ^ n := by rw [pow_succ, mul_inv_cancel_right]
    have e4 : ψ * ψ⁻¹ = 1 := mul_inv_cancel _
    rw [e1, e2, e3, e4, pull_one_left_eq_zero, add_zero, add_zero] at h
    rw [two_nsmul]
    exact h.symm
  have key : ∀ n : ℕ, (pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c +
      ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) ∧ (pull (ψ ^ (n + 1)).left c =
      (((n + 1 + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, pull_one_left_eq_zero]; simp
      · rw [pow_one]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := eq_sub_of_add_eq (hrec n)
      rw [show n + 1 + 1 = n + 2 from rfl, h, ih.1, ih.2]
      rw [show n + 2 + 1 = n + 1 + 1 + 1 from rfl, choose_two_succ (n + 1 + 1), choose_two_succ (n + 1),
        choose_two_succ n]
      push_cast
      module
  exact (key n).1

theorem separatedSt_of_const_cube : ConstSt → CubeSt → SeparatedSt := by
  intro hconst hcube K _ _ A _ _ hA L hL hamp Q hQ u hu
  haveI := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  obtain ⟨d, hd, n0, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
  have heff : ∀ φ : A.left ⟶ A.left, Eff (pull φ ((d : ℤ) • cls L hL)) := by
    intro φ
    rw [← cls_pw hL (d : ℤ)]
    exact eff_pull_of_veryAmpleBy K A.hom _ n0 s _ hs φ inferInstance
  have heffn : ∀ (φ : A.left ⟶ A.left) (j : ℕ), 1 ≤ j → Eff ((j : ℤ) • pull φ ((d : ℤ) • cls L hL)) := by
    intro φ j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using heff φ
    | succ j hj ih =>
      push_cast
      rw [add_zsmul, one_zsmul]
      exact eff_add _ _ ih (heff φ)
  obtain ⟨t₀, ht₀⟩ := hconst K A hA L hL hamp ((d : ℤ) • pull u.left (cls L hL))
  have hN : t₀ + 2 < Q ^ (t₀ + 2) := Nat.lt_pow_self (by omega)
  obtain ⟨ψ, hψ, rfl⟩ := hu (t₀ + 2)
  have hpow := pull_pow_left hcube hA L hL hamp (cls L hL) ψ (Q ^ (t₀ + 2))
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * (Q ^ (t₀ + 2) + 1).choose 2) ?_ ψ hψ ?_
    · have h1 : Q ^ (t₀ + 2) ≤ (Q ^ (t₀ + 2) + 1).choose 2 := by
        rw [choose_two_succ]; omega
      have h2 : (Q ^ (t₀ + 2) + 1).choose 2 ≤ d * (Q ^ (t₀ + 2) + 1).choose 2 :=
        Nat.le_mul_of_pos_left _ hd
      omega
    · have hb : 1 ≤ (Q ^ (t₀ + 2)).choose 2 := Nat.choose_pos (by omega)
      have e : (d : ℤ) • pull (ψ ^ (Q ^ (t₀ + 2))).left (cls L hL) -
          (d * (Q ^ (t₀ + 2) + 1).choose 2) • pull ψ.left (cls L hL) =
          (((Q ^ (t₀ + 2)).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left ((d : ℤ) • cls L hL) := by
        rw [hpow, map_zsmul, ← natCast_zsmul]
        push_cast
        module
      rw [e]
      exact heffn _ _ hb
  rw [hψ1, one_pow]

end GlobalTheory.AmpleRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodConstantEqOfCardCmType
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatAlgebraic

theorem natAbs_discr_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    (discr F).natAbs = 1 := by
  have hb : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  let e : ℚ ≃ₐ[ℚ] F := (Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)
  rw [← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]
  rfl

theorem two_le_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  have hE := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow] at hE
  have h2 : Module.finrank ℚ E = 2 := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]
  have h3 := NumberField.abs_discr_gt_two (K := E) (by omega)
  have h4 : |(discr E : ℤ)| = 1 := by rw [Int.abs_eq_natAbs, hE]; rfl
  omega

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := _root_.GlobalTheory.LatValRam.card_eq_finrank (E := E) (I := I) (φ := φ) h

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

end GlobalTheory.LatAlgebraic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordInEqOfJet
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped Classical

namespace GlobalTheory.LatConjOne

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) : ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ j, κ j • ({j} : Multiset I)).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']
  simp [Multiset.count_singleton]

theorem exists_perm {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (ι : K →+* ℂ) (φ : I → E →+* ℂ) (g : ℂ ≃+* ℂ) (hφ : IsCMType φ) (hK : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (hg : ∀ x, g (ι x) = ι x) (hr : ∃ x, starRingEnd ℂ (ι x) ≠ ι x) :
    ∃ π : I ≃ I, ∀ i, (g : ℂ →+* ℂ).comp (φ i) = φ (π i) := by
  have e : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hK]
  have h1 : ∀ i, ∃ j, (g : ℂ →+* ℂ).comp (φ i) = φ j := by
    intro i
    obtain ⟨j, hj, -⟩ := hφ ((g : ℂ →+* ℂ).comp (φ i))
    rcases hj with hj | hj
    · exact ⟨j, hj⟩
    · exfalso
      obtain ⟨x, hx⟩ := hr
      have := congrArg (fun f : E →+* ℂ => f (algebraMap K E x)) hj
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, e] at this
      rw [RingEquiv.coe_toRingHom, hg] at this
      exact hx this.symm
  choose π hπ using h1
  have hinj : Function.Injective π := by
    intro i i' h
    have h2 : φ i = φ i' := by
      have h3 := (hπ i).trans ((congrArg φ h).trans (hπ i').symm)
      ext x
      have := congrArg (fun f : E →+* ℂ => f x) h3
      simpa using g.injective this
    obtain ⟨j, -, hj⟩ := hφ (φ i)
    rw [hj i (Or.inl rfl), hj i' (Or.inl h2)]
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), hπ⟩

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem two_le_finrank_of_unramFin (E : Type) [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by omega
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hE : Module.finrank ℚ E = 2 := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E), h1, h2]
  have hgt := NumberField.abs_discr_gt_two (K := E) (by omega)
  have hbt : (⊥ : Subalgebra ℚ (maximalRealSubfield E)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  let f : (maximalRealSubfield E) ≃ₐ[ℚ] ℚ :=
    AlgEquiv.trans (Subalgebra.topEquiv (R := ℚ) (A := maximalRealSubfield E)).symm
      ((Subalgebra.equivOfEq _ _ hbt.symm).trans (Algebra.botEquiv ℚ (maximalRealSubfield E)))
  have hF : NumberField.discr (maximalRealSubfield E) = 1 := by
    rw [NumberField.discr_eq_discr_of_algEquiv _ f, Rat.numberField_discr]
  have key := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := maximalRealSubfield E) (𝒪 := 𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, hF] at key
  simp at key
  rw [Int.abs_eq_natAbs, key] at hgt
  norm_num at hgt

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem gamma_nat_add (k m : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + m) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range m, ((k : ℝ) + j) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    have := Real.Gamma_nat_eq_factorial (k - 1)
    rwa [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel] at this
  | succ m ih =>
    have h0 : (k : ℝ) + m ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      exact ne_of_gt (by linarith)
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one h0, ih]; ring

theorem cmPeriodConstant_eq_of_card_cmType (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (κ : I → ℕ) :
    (C0 E d k κ : ℂ) = (cWt E k : ℂ) * risingFactor k κ * (-1) ^ (∑ i, κ i) *
      ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) := by
  rw [cmValueConst_eq]
  simp only [cWt, risingFactor, gamma_nat_add _ _ hk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
    Finset.prod_pow_eq_pow_sum]
  have h1 : ((-1 : ℂ)) ^ (∑ i, κ i) * (-1) ^ (∑ i, κ i) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  linear_combination (-(((|(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
    ((k - 1).factorial : ℂ) ^ Module.finrank ℚ (maximalRealSubfield E) * (∏ x, ∏ j ∈ Finset.range (κ x), ((k : ℂ) + j)) *
    (Real.pi : ℂ) ^ (∑ i, κ i) * ((Real.sqrt d : ℝ) : ℂ)⁻¹ ^ (∑ i, κ i) * 2 ^ (∑ i, κ i))) * h1

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

end GlobalTheory.LatConjOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

theorem ahFactor_im_int_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := by
    haveI := q.isPrime
    haveI := p0.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime p0.asIdeal).symm)
  rw [this]
  exact hj

theorem ahFactor_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (v w : Fin g → ℂ) : w ⬝ᵥ Hm.mulVec (star v) = star (v ⬝ᵥ Hm.mulVec (star w)) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b, star_star]
  ring

theorem ahFactor_im_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  intro g A _ L u Hm χ hL hF l hl l' hl'
  obtain ⟨hH, hχ, hfac⟩ := hF
  obtain ⟨i, hi⟩ := ahFactor_im_int_chart L hL (u.ex 0).left
  have hex : ∀ z ∈ u.Λ, u.ex z = u.ex 0 := fun z hz => by
    rw [(u.ker z).mpr hz, (u.ker 0).mpr (zero_mem _)]
  have hc : ∀ z ∈ u.Λ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := fun z hz => by rw [hex z hz]; exact hi
  have e1 := hfac ⟨l, hl⟩ i 0 (hc 0 (zero_mem _))
  have e2 := hfac ⟨l', hl'⟩ i l (hc l hl)
  have e3 := hfac ⟨l', hl'⟩ i 0 (hc 0 (zero_mem _))
  have e4 := hfac ⟨l, hl⟩ i l' (hc l' hl')
  have hne := u.fr_ne i (l + l') (hc _ (add_mem hl hl'))
  have hχ1 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
  have hχ2 : χ ⟨l', hl'⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l', hl'⟩
  have hsw := ahFactor_herm_swap hH l l'
  simp only [zero_add, zero_dotProduct, mul_zero] at e1 e3
  rw [e2] at e1
  rw [e4, add_comm l' l] at e3
  have key := e1.symm.trans e3
  set F := u.fr i (l + l')
  set H := l ⬝ᵥ Hm.mulVec (star l')
  set H' := l' ⬝ᵥ Hm.mulVec (star l')
  set H0 := l ⬝ᵥ Hm.mulVec (star l)
  set Hs := l' ⬝ᵥ Hm.mulVec (star l)
  set c1 := χ ⟨l, hl⟩
  set c2 := χ ⟨l', hl'⟩
  have key2 : (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) =
      (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0)) := by
    simp only [Complex.exp_add] at key ⊢
    linear_combination key
  have hnz : c1 * c2 * F ≠ 0 := mul_ne_zero (mul_ne_zero hχ1 hχ2) hne
  have key3 := mul_left_cancel₀ hnz key2
  have key4 : Complex.exp ((Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) -
      (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0))) = 1 := by
    rw [Complex.exp_sub, key3, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp key4
  refine ⟨n, ?_⟩
  have hsc : H - Hs = 2 * (H.im : ℂ) * Complex.I := by
    rw [hsw]
    have h7 := Complex.sub_conj H
    push_cast at h7
    exact h7
  have h5 : ((H.im : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination hn - (Real.pi : ℂ) * hsc
  have h6 := sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right Complex.two_pi_I_ne_zero)
  exact_mod_cast h6

end GlobalTheory.TorusRM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLatticeStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  first | exact @GlobalTheory.TorusRM.ahFactor_im_int | exact GlobalTheory.TorusRM.ahFactor_im_int | (intros; apply GlobalTheory.TorusRM.ahFactor_im_int <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosedImmFieldDescent

set_option backward.isDefEq.respectTransparency.types false

theorem isClosedImmersion_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have hP : HasAffineProperty @IsClosedImmersion (affineAnd fun f ↦ Function.Surjective f) :=
    IsClosedImmersion.hasAffineProperty
  have H₂ : ∀ {R S : CommRingCat.{0}} {f : R ⟶ S}, (@Surjective ⊓ @Flat) (Spec.map f) →
      RingHom.FaithfullyFlat f.hom := by
    intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h hf
  have : IsAffine Y := by
    have : IsAffineHom g := MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩
      (HasAffineProperty.affineAnd_le_isAffineHom @IsClosedImmersion hP _ hf)
    exact isAffine_of_isAffineHom g
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ RingHom.FaithfullyFlat.codescendsAlong_surjective H₂ _ h hf
  intro R' S' f'
  exact HasAffineProperty.SpecMap_iff_of_affineAnd hP RingHom.surjective_respectsIso f'

theorem isPullback_baseChange_step {R k Ω : Type} [CommRing R] [Field k] [Field Ω] [Algebra R k]
    [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
      (pullback.map c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) c (Spec.map (CommRingCat.ofHom (algebraMap R k)))
        (𝟙 C) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback c _).flip
  have h0 := (IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).flip
  rw [pullback.lift_fst, Category.comp_id, e]
  exact h0

theorem fpqc_specMap_field (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  refine ⟨⟨⟨fun x ↦ ?_⟩, ?_⟩, inferInstance⟩
  · obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem isClosedImmersion_of_baseChange_extension :
    ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  intro R k Ω _ _ _ _ _ _ _ V W f hΩ
  have hd := isClosedImmersion_descendsAlong_fpqc
  have e : (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R k))) = (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let vX := pullback.map V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  let vY := pullback.map W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  have sX : IsPullback (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vX (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) V.hom
  have sY : IsPullback (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vY (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) W.hom
  let φk := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left
  let φΩ := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left
  have hk2 : φk ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hk1 : φk ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≫ f.left := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ2 : φΩ ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ1 : φΩ ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have comm : φΩ ≫ vY = vX ≫ φk := by
    apply pullback.hom_ext
    · simp only [vX, vY, Category.assoc, hk1, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      exact hΩ1
    · simp only [vX, vY, Category.assoc, hk2, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, hΩ2]
  have sq : IsPullback φΩ vX vY φk := by
    refine IsPullback.of_right ?_ comm sY
    rw [hΩ2, hk2]
    exact sX
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sY (fpqc_specMap_field k Ω)) hΩ

end GlobalTheory.ClosedImmFieldDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExtStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_of_baseChange_field_ext : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  first | exact @GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension | exact GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension | (intros; apply GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_of_baseChange_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCover
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem Pt.aff_in (s : X ⟶ Sp R) (V : X.affineOpens) : (Pt.aff s V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Pt.homAff (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) : (Pt.aff s V).Hom Q :=
  ⟨{ (GlobalTheory.Points.valMap Q.x V.1 h).hom with
      commutes' := fun r ↦ by
        have e := GlobalTheory.Points.valR_constFn_of_over s (algebraMap R Q.B) Q.x Q.w V.1 h r
        rw [GlobalTheory.Points.valR_eq Q.x V.1 h] at e
        exact e },
    GlobalTheory.Points.specMap_valMap_fromSpec V.2 Q.x h⟩

theorem Pt.homAff_apply (V : X.affineOpens) (Q : Pt s) (h : Q.In V.1) (a : CechDR.Sec s V.1) :
    (Pt.homAff V Q h).ρ a = valR Q.x V.1 a :=
  (GlobalTheory.Points.valR_eq Q.x V.1 h a).symm

theorem exists_sec_of_isNat (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens)
    (U : X.Opens) (hWU : ∀ j, W j ≤ U) (hU : U ≤ ⨆ j, W j) (F : PtFn s) (hF : ∀ j, IsNat (W j) F) :
    ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  let Ix := {V : X.affineOpens // ∃ j, V.1 ≤ W j}
  let Vs : Ix → X.Opens := fun i ↦ i.1.1
  have hVU : ∀ i : Ix, Vs i ≤ U := fun i ↦ i.2.choose_spec.trans (hWU _)
  let iUV : ∀ i : Ix, Vs i ⟶ U := fun i ↦ homOfLE (hVU i)
  have hcov : U ≤ iSup Vs := by
    intro x hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hU hx)
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := x) hj
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, j, hVW⟩, hxV⟩
  have hres : ∀ (i : Ix) (V : X.affineOpens) (h : V.1 ≤ i.1.1),
      F (Pt.aff s V) = CechDR.Sec.res s h (F (Pt.aff s i.1)) := fun i V h ↦
    hF i.2.choose (Pt.aff s i.1) (Pt.aff s V) (Pt.affHom s h) ((Pt.aff_in s i.1).mono i.2.choose_spec)
  let sf : ∀ i : Ix, Γ(X, Vs i) := fun i ↦ F (Pt.aff s i.1)
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 Vs sf := by
    intro i i'
    refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ Vs i ⊓ Vs i'} ↦ V.1.1) _
      (fun V ↦ homOfLE V.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := Vs i ⊓ Vs i') (x := x) hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
    · intro V
      have k : ∀ (T : Ix) (h2 : Vs i ⊓ Vs i' ≤ Vs T) (g : Vs i ⊓ Vs i' ⟶ Vs T),
          X.sheaf.1.map (homOfLE V.2).op (X.sheaf.1.map g.op (sf T)) = F (Pt.aff s V.1) := fun T h2 g ↦ by
        rw [Subsingleton.elim g (homOfLE h2)]
        change CechDR.Sec.res s V.2 (CechDR.Sec.res s h2 (sf T)) = _
        rw [← CechDR.Sec.res_res]
        exact (hres T V.1 _).symm
      exact (k i inf_le_left _).trans (k i' inf_le_right _).symm
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' Vs U iUV hcov sf hcomp
  refine ⟨f, fun j P hP ↦ ?_⟩
  have hPU : P.In U := hP.mono (hWU j)
  have key : ∀ (V' : (Sp P.B).affineOpens) (i : Ix), V'.1 ≤ P.x ⁻¹ᵁ i.1.1 →
      CechDR.toSec R P.B V' (F P) = CechDR.toSec R P.B V' (valR P.x U f) := by
    intro V' i hV'
    let P' : Pt s := ⟨CechDR.Sec (CechDR.algStr R P.B) V'.1, CechDR.affPt (CechDR.algStr R P.B) V' ≫ P.x, by
      rw [Category.assoc, P.w]; exact CechDR.affPt_w _ V'⟩
    have hpt : spMap ((CechDR.toSec R P.B V' : P.B →ₐ[R] P'.B) : P.B →+* P'.B) ≫ P.x = P'.x := by
      change _ = CechDR.affPt _ V' ≫ P.x
      rw [CechDR.affPt_eq]; rfl
    let φ : P.Hom P' := ⟨CechDR.toSec R P.B V', hpt⟩
    have hP'V : P'.In i.1.1 := fun q _ ↦ hV' (V'.2.fromSpec_preimage_self.ge (Set.mem_univ q))
    have e1 : F P' = φ.ρ (F P) := hF j P P' φ hP
    have e2 : F P' = (Pt.homAff i.1 P' hP'V).ρ (F (Pt.aff s i.1)) :=
      hF i.2.choose _ _ _ ((Pt.aff_in s i.1).mono i.2.choose_spec)
    rw [Pt.homAff_apply] at e2
    have e3 : valR P'.x i.1.1 (F (Pt.aff s i.1)) = valR P'.x U f := by
      have h0 := hf i
      have h1 := GlobalTheory.Points.valR_res P'.x (hVU i) hP'V f
      change valR P'.x i.1.1 (sf i) = _
      rw [← h0]
      exact h1
    have e4 : valR P'.x U f = φ.ρ (valR P.x U f) := by
      have h2 := GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* P'.B) P.x U hPU f
      rw [hpt] at h2
      exact h2
    exact e1.symm.trans (e2.trans (e3.trans e4))
  have hex : ∀ y : Sp P.B, ∃ V' : (Sp P.B).affineOpens, y ∈ V'.1 ∧ ∃ i : Ix, V'.1 ≤ P.x ⁻¹ᵁ i.1.1 := by
    intro y
    obtain ⟨V, hV, hyV, hVW⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := W j) (x := P.x y) (hP (Set.mem_univ y))
    obtain ⟨V', hV', hyV', hV'V⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp P.B) (U := P.x ⁻¹ᵁ V) (x := y) hyV
    exact ⟨⟨V', hV'⟩, hyV', ⟨⟨V, hV⟩, j, hVW⟩, hV'V⟩
  choose V' hyV' i hi using hex
  have key2 : (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (F P) =
      (Scheme.ΓSpecIso (CommRingCat.of P.B)).inv (valR P.x U f) := by
    refine (Sp P.B).sheaf.eq_of_locally_eq' (fun y ↦ (V' y).1) ⊤ (fun _ ↦ homOfLE le_top)
      (fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV' y⟩) _ _ (fun y ↦ ?_)
    have := key (V' y) (i y) (hi y)
    change (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (F P) =
      (CechDR.secMap (𝟙 (Sp P.B)) (V' y).1).hom (valR P.x U f) at this
    simp only [CechDR.secMap, Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  exact (Scheme.ΓSpecIso (CommRingCat.of P.B)).symm.commRingCatIsoToRingEquiv.injective key2

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCoverStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens) (U : X.Opens), (∀ j, W j ≤ U) → U ≤ ⨆ j, W j → ∀ F : PtFn s, (∀ j, IsNat (W j) F) → ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  first | exact @GlobalTheory.CechKS.exists_sec_of_isNat | exact GlobalTheory.CechKS.exists_sec_of_isNat | (intros; apply GlobalTheory.CechKS.exists_sec_of_isNat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrict
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isDominant_of_isIso_restrict (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    (U : X.Opens) (hU : (U : Set X).Nonempty) (h : IsIso (s ∣_ U)) : IsDominant s := by
  refine ⟨?_⟩
  have hd : Dense (U : Set X) := U.isOpen.dense hU
  refine hd.mono ?_
  intro x hx
  obtain ⟨y, hy⟩ := (s ∣_ U).surjective ⟨x, hx⟩
  refine ⟨y.1, ?_⟩
  have := morphismRestrict_base_coe s U y
  rw [hy] at this
  exact this.symm

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def transl {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : G ⟶ G :=
  𝟙 G * (Over.homMk G.hom (by simp) ≫ y)

def Near.chart {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : Option (Fin n) → (pullback N.U.hom π ⟶ G.left)
  | none => N.u
  | some k => N.u ≫ (transl (x k)⁻¹).left

theorem Near.chart_some {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) (k : Fin n) :
    N.chart x (some k) = N.u ≫ (transl (x k)⁻¹).left := rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalDivisorOfForm
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isDivOfForm_and_toPic : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  intro k _ _ Y _ _ q n _ η hη
  obtain ⟨c, hc⟩ := (isFreeGen_baseForm q n).2 η
  replace hc : c • baseForm q n = η := hc
  have h0 : c ≠ 0 := fun e => hη (by rw [← hc, e, zero_smul])
  have h := (isDivOfForm_canonical q n).smul (Units.mk0 c h0)
  rw [Units.val_mk0, hc] at h
  refine ⟨⟨_, h⟩, fun K hK Kc => ?_⟩
  rw [hK.unique hη h, map_add (f := _), toPic_principal]
  simpa using (presents_canonical q n).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ Kc))

end GlobalTheory.Discrepancy
end
