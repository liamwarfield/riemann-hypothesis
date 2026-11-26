module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.GenTrait

theorem spMap_stalkHom_fromSpecStalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)
    (x : M.Z) : spMap (M.stalkHom x) ≫ M.Z.fromSpecStalk x = M.pt := by
  have e2 : spMap (M.stalkHom x) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
      Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) x)) := by
    rw [RatModel.stalkHom]
    show Spec.map _ = _
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    rfl
  rw [e2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt

end GlobalTheory.Poinc.GenTrait


open GlobalTheory.Poinc.GenTrait in
theorem GlobalTheory.Poinc.exists_trait_of_stalk_dvr : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : Trait F) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro g n o _ ζ F o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.Poinc.traitExtSt g n o ζ F V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp',
      Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_moduli_of_stalk_completeDVR : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : Trait F) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  first | exact @GlobalTheory.Poinc.exists_trait_of_stalk_dvr | exact GlobalTheory.Poinc.exists_trait_of_stalk_dvr | (intros; apply GlobalTheory.Poinc.exists_trait_of_stalk_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalar
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp


open GlobalTheory.VolBr.NuEq in
theorem val_frame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  intro k _ X _ p P a b σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have hL : CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG
  have hA : CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y ≠ 0 := by
    rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG'
  set gL := CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y with hgL
  set gA := CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y with hgA
  have hG : gL ^ a * gA ^ b ≠ 0 := mul_ne_zero (zpow_ne_zero _ hL) (zpow_ne_zero _ hA)
  have hGn : (‖gL ^ a * gA ^ b‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hG)
  refine ⟨(‖gL ^ a * gA ^ b‖ : ℂ) / (gL ^ a * gA ^ b), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hG)]
  intro f hf
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have hrv : ratVal (P.loc a b f i j) y =
      gL ^ a * gA ^ b * ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y := by
    rw [hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
      ratVal_zpow' uG, ratVal_zpow' uG', eG, eG']
    rfl
  have c0 : 0 < ‖gL‖ := norm_pos_iff.2 hL
  have c0' : 0 < ‖gA‖ := norm_pos_iff.2 hA
  have hexp : Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) =
      ‖gL ^ a * gA ^ b‖⁻¹ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) := by
    rw [(P.L.φ σ).trans i _ y hi hi₀, (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_zpow, norm_zpow,
      ← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
      Real.log_pow, Real.log_pow, ← hgL, ← hgA, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [val, hrv, hexp]
  push_cast
  field_simp

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameEqLocalFunctionUnitScalarStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → ∃ θ : ℂ, ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ y f = θ * (ratVal (P.loc a b f i j) y * (Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
  first | exact @GlobalTheory.HSAmp.val_frame | exact GlobalTheory.HSAmp.val_frame | (intros; apply GlobalTheory.HSAmp.val_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
private lemma ofReal_norm_sum_mul_sq_eq_double_sum_conj {ι : Type} [Fintype ι] (c w : ι → ℂ) :
    ((‖∑ i, c i * w i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (w i * (starRingEnd ℂ) (w j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring


set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
theorem _root_.GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form (S : Type) (Y : S → Type)
    [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι]
    [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ)
    (h : _root_.GlobalTheory.HSAmp.IsFam μ v) :
    (_root_.GlobalTheory.HSAmp.gram μ v).IsHermitian ∧ ∀ c : ι → ℂ,
      (∀ σ, Integrable (_root_.GlobalTheory.HSAmp.cmb v c σ) (μ σ)) ∧
      0 ≤ _root_.GlobalTheory.HSAmp.l2 μ v c ∧
      (_root_.GlobalTheory.HSAmp.l2 μ v c : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * _root_.GlobalTheory.HSAmp.gram μ v i j := by
  haveI : Fintype S := @Fintype.ofFinite S h.finite
  have hint := h.integrable
  have hterm : ∀ (c : ι → ℂ) (σ : S), Integrable (fun y => ∑ i, ∑ j,
      c i * (starRingEnd ℂ) (c j) * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun c σ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hint σ i j).const_mul _
  refine ⟨?_, fun c => ⟨fun σ => ?_, ?_, ?_⟩⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.HSAmp.gram, Matrix.of_apply,
      finsum_eq_sum_of_fintype]
    rw [star_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.star_def, ← integral_conj]
    congr 1 with y
    simp [mul_comm]
  · refine (hterm c σ).re.congr (ae_of_all _ fun y => ?_)
    simp only [_root_.GlobalTheory.HSAmp.cmb]
    rw [← ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)]
    exact Complex.ofReal_re _
  · unfold _root_.GlobalTheory.HSAmp.l2
    exact finsum_nonneg fun σ => integral_nonneg fun y => by
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      positivity
  · unfold _root_.GlobalTheory.HSAmp.l2 _root_.GlobalTheory.HSAmp.gram
    simp only [Matrix.of_apply, finsum_eq_sum_of_fintype]
    have key : ∀ σ, ((∫ y, _root_.GlobalTheory.HSAmp.cmb v c σ y ∂μ σ : ℝ) : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := by
      intro σ
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      rw [← integral_complex_ofReal,
        integral_congr_ae (ae_of_all _ fun y => ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)),
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [Complex.ofReal_sum]
    simp only [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSumStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_isHermitian_l2_eq_double_sum : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).IsHermitian ∧ ∀ c : ι → ℂ, (∀ σ, Integrable (cmb v c σ) (μ σ)) ∧ 0 ≤ l2 μ v c ∧ (l2 μ v c : ℂ) = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * gram μ v i j := by
  first | exact @GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | exact GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | (intros; apply GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithFnField

theorem charZero_and_trdeg_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  intro k _ X _ p D h
  refine ⟨?_, ArithTrdeg.trdeg_functionField_eq h⟩
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
  exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0

end GlobalTheory.ArithFnField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdegStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArith_functionField_charZero_trdeg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Algebra.trdeg ℤ X.functionField = D := by
  first | exact @GlobalTheory.ArithFnField.charZero_and_trdeg_functionField | exact GlobalTheory.ArithFnField.charZero_and_trdeg_functionField | (intros; apply GlobalTheory.ArithFnField.charZero_and_trdeg_functionField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNorms
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem upAtPrime_groups_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  intro k _ X _ p P u a b
  have key : ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      Real.exp (-(a * ((upperParabolic P u).L.φ σ).φ (pick ((upperParabolic P u).L.φ σ).isLB y) y + b * ((upperParabolic P u).A.φ σ).φ (pick ((upperParabolic P u).A.φ σ).isLB y) y) / 2)
        = Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2)
          * Real.exp (-(a * u.u σ y) / 2) := by
    intro σ y
    rw [← Real.exp_add]
    congr 1
    show -(a * ((P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + u.u σ y) + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 = _
    ring
  refine ⟨rfl, fun f => rfl, fun σ y f => ⟨?_, ?_⟩⟩
  · show ratVal _ y * ((Real.exp _ : ℝ) : ℂ) = ratVal _ y * ((Real.exp _ : ℝ) : ℂ) * _
    rw [key σ y, Complex.ofReal_mul, mul_assoc]
    rfl
  · show ‖ratVal _ y‖ * Real.exp _ = ‖ratVal _ y‖ * Real.exp _ * _
    rw [key σ y, mul_assoc]
    rfl

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaiseFirstWeightSectionsLociValuesNormsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (u : SmFn p) (a b : ℤ), (upperParabolic P u).H a b = P.H a b ∧ (∀ f, NV (upperParabolic P u) a b f = NV P a b f) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), val (upperParabolic P u) a b σ y f = val P a b σ y f * (Real.exp (-(a * u.u σ y) / 2) : ℝ) ∧ (upperParabolic P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(a * u.u σ y) / 2) := by
  first | exact @GlobalTheory.HSAmp.upAtPrime_groups_values_norms | exact GlobalTheory.HSAmp.upAtPrime_groups_values_norms | (intros; apply GlobalTheory.HSAmp.upAtPrime_groups_values_norms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLoci
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLoci
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.HSAmp.pow_sec_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p P e
  have hR : P.Rep ((e : ℤ) * 1) ((e : ℤ) * 0) (P.L.pow e) :=
    GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L e (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  rw [mul_one, mul_zero] at hR
  obtain ⟨g, -, hrange, -, hloc⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P (e : ℤ) 0 (P.L.pow e) hR
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have key : ∀ u : (lbPow P.L.B e).Sec, NV P e 0 (g u) = (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X) := by
    intro u
    ext x
    obtain ⟨i, hi⟩ := hcov P.L.isLB x
    obtain ⟨j, hj⟩ := hcov P.A.isLB x
    constructor
    · intro h
      exact (hloc u x i j hi hj).2 (h i j hi hj)
    · intro h i' j' hi' hj'
      exact (hloc u x i' j' hi' hj').1 h
  refine ⟨fun u => ⟨g u, ?_, key u⟩, fun f hf => ?_⟩
  · have : g u ∈ Set.range g := ⟨u, rfl⟩
    rw [hrange] at this
    exact this
  · have : f ∈ Set.range g := by rw [hrange]; exact hf
    obtain ⟨u, rfl⟩ := this
    exact ⟨u, key u⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLociStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.HSAmp.pow_sec_dict | exact GlobalTheory.HSAmp.pow_sec_dict | (intros; apply GlobalTheory.HSAmp.pow_sec_dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem loc_continuousOn_holo : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  intro k _ X _ p P a b σ f hf i j
  have key : ∀ y ∈ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j), ∃ (W : X.Opens) (hW : genericPoint X ∈ W)
      (g : Γ(X, W)), y ∈ ptsIn p σ W ∧ P.loc a b f i j = fnOf W hW g := by
    intro y hy
    have hr : RegAt (under y) (P.loc a b f i j) := hf _ i j (mem_ptsIn.1 hy.1) (mem_ptsIn.1 hy.2)
    obtain ⟨W, hx, g, e⟩ := hr.exists_fnOf
    exact ⟨W, gen_mem hx, g, mem_ptsIn.2 hx, e.symm⟩
  refine ⟨fun y hy => ?_, fun D c => ?_⟩
  · obtain ⟨W, hW, g, hy', e⟩ := key y hy
    have hc : ContinuousAt (ratVal (q := p) (σ := σ) (P.loc a b f i j)) y := by
      refine ((continuousOn_ev (p := p) (σ := σ) g).continuousAt ((isOpen_ptsIn W).mem_nhds hy')).congr ?_
      filter_upwards [(isOpen_ptsIn W).mem_nhds hy'] with z hz
      rw [e, ratVal_fnOf hz]
    exact hc.continuousWithinAt
  · intro v hv
    obtain ⟨W, hW, g, hy', e⟩ := key _ hv.2
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W) :=
      c.e.isOpen_inter_preimage_symm (isOpen_ptsIn W)
    have hm : v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ W := ⟨hv.1, hy'⟩
    have hd := (c.holo W g).differentiableAt (hO.mem_nhds hm)
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hO.mem_nhds hm] with w hw
    rw [e, ratVal_fnOf hw.2]
    rfl

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField), f ∈ P.H a b → ∀ i j, ContinuousOn (ratVal (q := p) (σ := σ) (P.loc a b f i j)) (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) ∧ ∀ (D : ℕ) (c : AlgChart p σ D), DifferentiableOn ℂ (fun v => ratVal (P.loc a b f i j) (c.e.symm v)) (c.e.target ∩ c.e.symm ⁻¹' (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j))) := by
  first | exact @GlobalTheory.HSAmp.loc_continuousOn_holo | exact GlobalTheory.HSAmp.loc_continuousOn_holo | (intros; apply GlobalTheory.HSAmp.loc_continuousOn_holo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem ringKrullDim_stalk_le_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (z : X) :
    ringKrullDim (Y.presheaf.stalk (f z)) ≤ ringKrullDim (X.presheaf.stalk z) := by
  letI : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := (f.stalkMap z).hom.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := Flat.stalkMap f z
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f z)) (X.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  haveI : Algebra.HasGoingDown (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := Algebra.HasGoingDown.of_flat
  exact GroundTheory.Arith.SchemeCoh.ringKrullDim_le_of_hasGoingDown

theorem Setup.height_under_vert (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left)
    (hz : Vert (σ.C x).G.hom (σ.ρ x σ.f) z) :
    (spMap (σ.ρ x) ((σ.C x).G.hom z)).asIdeal.height = 1 := by
  haveI := (σ.C x).semi.smooth
  haveI : Flat (spMap (σ.ρ x)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact σ.flat x
  have h1 := (ringKrullDim_stalk_le_of_flat (spMap (σ.ρ x)) ((σ.C x).G.hom z)).trans
    (ringKrullDim_stalk_le_of_flat (σ.C x).G.hom z)
  rw [hz.1] at h1
  have hf : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom z)).asIdeal := hz.2
  generalize spMap (σ.ρ x) ((σ.C x).G.hom z) = p at h1 hf ⊢
  letI : Algebra σ.R ((Sp σ.R).presheaf.stalk p) := StructureSheaf.stalkAlgebra σ.R p
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := σ.R) p
  haveI : IsLocalization.AtPrime ((Sp σ.R).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk σ.R p
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  refine le_antisymm (by exact_mod_cast h1) ?_
  have hlt : (⊥ : Ideal σ.R) < p.asIdeal := bot_lt_iff_ne_bot.2 fun h => σ.hf (by rwa [h, Ideal.mem_bot] at hf)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  exact le_add_self.trans h2

theorem Setup.forall_mem_W_iff : ∀ (σ : Setup) (u : σ.A.left.functionField),
    (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  intro σ u
  refine ⟨fun h p _ _ => h p, fun h x z hz => ?_⟩
  have h1 := h _ (σ.height_under_vert x z hz) hz.2
  rw [← (GlobalTheory.T.gaussProperty_codimOne_chart_heightOnePrime σ x z hz).2] at h1
  exact h1

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes : ∀ (σ : Setup) (u : σ.A.left.functionField), (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  first | exact @GlobalTheory.Desc.Setup.forall_mem_W_iff | exact GlobalTheory.Desc.Setup.forall_mem_W_iff | (intros; apply GlobalTheory.Desc.Setup.forall_mem_W_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isMapOf_existsUnique_and : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  intro p k _ d e G H c c' f
  have hone := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2
  have hcomp : ∀ j n, G.res n (f.app (n + 1) (c'.x (n + 1) j)) = f.app n (c'.x n j) := fun j n => by
    rw [res_app, c'.res]
  refine ⟨?_, ?_⟩
  · choose φ hφ _ using fun j => hone (fun n => f.app n (c'.x n j)) (hcomp j)
    refine ⟨φ, fun n j => hφ j n, fun ψ hψ => funext fun j => ?_⟩
    obtain ⟨g, -, hg⟩ := hone (fun n => f.app n (c'.x n j)) (hcomp j)
    exact (hg (ψ j) fun n => hψ n j).trans (hg (φ j) fun n => hφ j n).symm
  intro φ hφ
  have hconst : ∀ j, constantCoeff (φ j) = 0 := fun j => by
    have h1 := (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d (G.A 0) (c.x 0) (c.nil 0) (c.aug 0) (φ j)).1
    change Coalgebra.counit (R := k) (c.ev 0 (φ j)) = _ at h1
    rw [← h1, hφ 0 j, CoalgHomClass.counit_comp_apply, c'.aug]
  refine ⟨hconst, fun n => ⟨fun g => ?_, fun s => ?_⟩⟩
  · have hy : ∀ j, IsNilpotent (f.app n (c'.x n j)) := fun j => (c'.nil n j).map (f.app n)
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (G.A n)).1 (Fin d) (c.ev n)
      (fun t => by
        change IsNilpotent (evA k (c.x n) (c.nil n) (X t))
        rw [evA_X]; exact c.nil n t) φ hconst _ hy (fun j => hφ n j) g
    rw [h1]
    exact ((GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e) (H.A n)).2 (G.A n) (f.app n : H.A n →ₐ[k] G.A n) (c'.x n)
      (c'.nil n) _ hy (fun _ => rfl) g).symm
  · let F : H.A n ⊗[k] H.A n →ₐ[k] G.A n ⊗[k] G.A n :=
      Algebra.TensorProduct.map (f.app n : H.A n →ₐ[k] G.A n) (f.app n : H.A n →ₐ[k] G.A n)
    have hy : ∀ i, IsNilpotent (F (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map F
    have hev := GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n
    have ha : ∀ i, constantCoeff ((Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) :
        Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k) i) = 0 := by
      intro i
      have hc := hev.2.2.2
      cases i with
      | inl j =>
        rw [Sum.elim_inl, ← hc, hev.1, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
      | inr j =>
        rw [Sum.elim_inr, ← hc, hev.2.1, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change Coalgebra.counit (R := k) (c.ev n (φ j)) = 0
        rw [hφ n j, CoalgHomClass.counit_comp_apply, c'.aug]
    have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n ⊗[k] G.A n)).1 (Fin d ⊕ Fin d) (c.ev₂ n)
      (fun t => by
        change IsNilpotent (evA k (c.x₂ n) (c.nil₂ n) (X t))
        rw [evA_X]; exact c.nil₂ n t) _ ha _ hy
      (fun i => by
        cases i with
        | inl j =>
          simp only [Sum.elim_inl]
          rw [hev.1, hφ n j]
          show _ = F (c'.x n j ⊗ₜ 1)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
        | inr j =>
          simp only [Sum.elim_inr]
          rw [hev.2.1, hφ n j]
          show _ = F (1 ⊗ₜ c'.x n j)
          rw [Algebra.TensorProduct.map_tmul, map_one]; rfl) s
    have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n ⊗[k] G.A n) F
      (c'.x₂ n) (c'.nil₂ n) _ hy (fun _ => rfl) s
    have h3 : pullbackTwo (f.app n) (c'.ev₂ n s) = F (c'.ev₂ n s) := by
      induction (c'.ev₂ n s) with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => rfl
    unfold pull2 at2
    rw [h1, h3]
    exact h2.symm

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUniqueStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k) (c : Chart G d) (c' : Chart H e), ∀ f : G ⟶ H, (∃! φ, c.IsMapOf c' f φ) ∧ ∀ (φ : Fin e → MvPowerSeries (Fin d) k), c.IsMapOf c' f φ → (∀ j, constantCoeff (φ j) = 0) ∧ ∀ n, (∀ g, c.ev n (subst φ g) = f.app n (c'.ev n g)) ∧ ∀ s, c.ev₂ n (pull2 φ s) = pullbackTwo (f.app n) (c'.ev₂ n s) := by
  first | exact @GlobalTheory.Katz.isMapOf_existsUnique_and | exact GlobalTheory.Katz.isMapOf_existsUnique_and | (intros; apply GlobalTheory.Katz.isMapOf_existsUnique_and <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLift
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianHodge

theorem exists_isCompl_ker {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ C : Submodule R M, IsCompl (LinearMap.ker f) C := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfg : ∀ y, f (g y) = y := fun y ↦ LinearMap.congr_fun hg y
  refine ⟨LinearMap.range g, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    have : y = 0 := (hfg y).symm.trans hx
    rw [this, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have e : x = (x - g (f x)) + g (f x) := by abel
    rw [e]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self g _)
    rw [LinearMap.mem_ker, map_sub, hfg, sub_self]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

theorem mem_F1_iff_supported (hO : Function.Injective (cmpO s)) (c : FirstDeRham s) :
    c ∈ F1 s ↔ cmp1 s c ∈ CechHodgeFiltration s := by
  change toH1O s c = 0 ↔ toHO1 s (cmp1 s c) = 0
  rw [structureSheaf_comparison_comm]
  exact ⟨fun h ↦ h ▸ map_zero _, fun h ↦ hO (h.trans (map_zero _).symm)⟩

theorem hodge_of_cmp (P : Submodule R (FirstDeRham s)) (hP : P = ⊤)
    (hb : Function.Bijective (cmp1 s)) (hO : Function.Injective (cmpO s)) (t : X ⟶ Sp R) (hst : s = t)
    (hcl : ClosedForm t = ⊤) (hinj : Function.Injective (clForm t))
    (hsurj : Function.Surjective (toHO1 t)) (hproj : Module.Projective R (HO1 t)) :
    (∃ N : Submodule R P, IsCompl ((F1 s).comap P.subtype) N) ∧
      Nonempty (((F1 s).comap P.subtype) ≃ₗ[R] GlobForm t) := by
  subst hst
  let E : P ≃ₗ[R] HH1 s := (LinearEquiv.ofTop P hP).trans (LinearEquiv.ofBijective (cmp1 s) hb)
  have hE : ∀ x : P, E x = cmp1 s x.1 := fun _ ↦ rfl
  have hc : (F1 s).comap P.subtype = (CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s) := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe, hE]
    exact mem_F1_iff_supported s hO x.1
  obtain ⟨N', hN'⟩ := exists_isCompl_ker (toHO1 s) hsurj
  refine ⟨⟨N'.comap (E : P →ₗ[R] HH1 s), ?_⟩, ⟨?_⟩⟩
  · rw [hc, Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm]
    exact (Submodule.orderIsoMapComap E.symm).isCompl hN'
  · let e1 : ((F1 s).comap P.subtype) ≃ₗ[R] ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) :=
      LinearEquiv.ofEq _ _ hc
    let e2 : ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) ≃ₗ[R] CechHodgeFiltration s :=
      E.ofSubmodules _ (CechHodgeFiltration s) (Submodule.map_comap_eq_of_surjective E.surjective _)
    let e3 : CechHodgeFiltration s ≃ₗ[R] LinearMap.range (clForm s) := LinearEquiv.ofEq _ _ (cechHodgeFiltration_eq_range s)
    let e4 : LinearMap.range (clForm s) ≃ₗ[R] ClosedForm s := (LinearEquiv.ofInjective (clForm s) hinj).symm
    let e5 : ClosedForm s ≃ₗ[R] GlobForm s := LinearEquiv.ofTop _ hcl
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

end GlobalTheory.AbelianHodge

namespace GlobalTheory.AbelianHodge

theorem abelianDeRham_hodge (P1 : GlobalTheory.Published.CrystallineSmoothLift) (P2 : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.Hodge := by
  intro R _ A _ g hA hg
  obtain ⟨h0, -⟩ := GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison P1 P2) R A g hA hg
  obtain ⟨-, -, ⟨hGf, hGp, hGr⟩, ⟨-, hOp, -⟩, ⟨hcl, hinj, hsurj⟩, -⟩ := P2 R A g hA hg
  have := hA.smooth
  have := hA.proper
  obtain ⟨hb, -⟩ := cechDeRham_comparison_bijective_cup_smooth P1 R A.left (A.hom ≫ 𝟙 _) inferInstance inferInstance
    inferInstance
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 _)
  obtain ⟨⟨N, hN⟩, ⟨e⟩⟩ := hodge_of_cmp (A.hom ≫ 𝟙 _) (primDR A) h0 hb hO A.hom
    (Category.comp_id _) hcl hinj hsurj hOp
  exact ⟨GlobalTheory.T.hodgeLieSequence_exact_abelianScheme P1 P2 R A g hA hg, ⟨N, hN⟩, Module.Finite.equiv e.symm,
    Module.Projective.of_equiv e.symm, fun p ↦ by
      change Module.rankAtStalk ((F1 (A.hom ≫ 𝟙 _)).comap (primDR A).subtype) p = g
      rw [Module.rankAtStalk_eq_of_equiv e, hGr]⟩

end GlobalTheory.AbelianHodge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLiftStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Hodge := by
  first | exact @GlobalTheory.AbelianHodge.abelianDeRham_hodge | exact GlobalTheory.AbelianHodge.abelianDeRham_hodge | (intros; apply GlobalTheory.AbelianHodge.abelianDeRham_hodge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPos
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.VolFin

open GlobalTheory.ChartGlue
open scoped ENNReal

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem meas_eq [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D) (c : AlgChart p σ D)
    {S : Set (CxPts p σ)} (hS : MeasurableSet S) (hc : S ⊆ c.e.source) :
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
  rw [VolDens.meas, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hS hc,
    chartMeas_apply_of_subset _ _ hS hc]

theorem continuousOn_dens (ω : VolDens p σ D) (c : AlgChart p σ D) :
    ContinuousOn (fun v => ω.dens c (c.e.symm v)) c.e.target :=
  (ω.cont c).comp c.e.continuousOn_symm fun _ hv => c.e.map_target hv

theorem exists_open_lt_top [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O : Set (CxPts p σ), IsOpen O ∧ y ∈ O ∧ ω.meas O < ∞ := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g v < g (c.e y) + 1 :=
    hg.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target := c.e.open_target.mem_nhds hv0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε,
    c.e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hy, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, ?_⟩
  have hO : MeasurableSet (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) :=
    (c.e.isOpen_inter_preimage Metric.isOpen_ball).measurableSet
  rw [meas_eq ω c hO Set.inter_subset_left]
  have hsub : c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) ⊆ Metric.ball (c.e y) ε := by
    rintro _ ⟨z, hz, rfl⟩; exact hz.2
  calc ∫⁻ v in c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε), ENNReal.ofReal (g v)
      ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ ≤ ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) + 1) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ = ENNReal.ofReal (g (c.e y) + 1) * volume (Metric.ball (c.e y) ε) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

theorem meas_pos [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {U : Set (CxPts p σ)} (hU : IsOpen U) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hyU : y ∈ U) : ω.meas U ≠ 0 := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have hpos : 0 < g (c.e y) := by
    simp only [g, c.e.left_inv hy]; exact ω.pos c y hy
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g (c.e y) / 2 < g v :=
    hg.eventually (lt_mem_nhds (half_lt_self hpos))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
    (isOpen_over c.e hU).mem_nhds (mem_over c.e hy hyU)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  have hA : MeasurableSet (c.e.source ∩ U) := (c.e.open_source.inter hU).measurableSet
  have hsub : Metric.ball (c.e y) ε ⊆ c.e '' (c.e.source ∩ U) := by
    rw [c.e.image_source_inter_eq']; exact fun v hv => (hball v hv).2
  refine (lt_of_lt_of_le ?_ (measure_mono (μ := ω.meas) (Set.inter_subset_right :
    c.e.source ∩ U ⊆ U))).ne'
  rw [meas_eq ω c hA Set.inter_subset_left]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (g (c.e y) / 2) * volume (Metric.ball (c.e y) ε) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne' (Metric.measure_ball_pos _ _ hε).ne'
    _ = ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) / 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ ≤ ∫⁻ v in c.e '' (c.e.source ∩ U), ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end GlobalTheory.HSAmp.VolFin


open GlobalTheory.HSAmp.VolFin in
theorem GlobalTheory.HSAmp.volDens_meas_finite_openPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    IsFiniteMeasure ω.meas ∧ ω.meas.IsOpenPosMeasure := by
  intro k _ X _ p D hX hS σ ω
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  haveI := hX.compactSpace σ
  obtain ⟨R⟩ := hS σ
  haveI : IsLocallyFiniteMeasure ω.meas := ⟨fun y => by
    obtain ⟨i, hi⟩ := R.cover y
    obtain ⟨O, hO, hyO, hfin⟩ := exists_open_lt_top ω (R.chart i) hi
    exact ⟨O, hO.mem_nhds hyO, hfin⟩⟩
  refine ⟨inferInstance, ⟨fun U hU ⟨y, hyU⟩ => ?_⟩⟩
  obtain ⟨i, hi⟩ := R.cover y
  exact meas_pos ω (R.chart i) hU hi hyU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPosStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D), IsFiniteMeasure ω.meas ∧ ω.meas.IsOpenPosMeasure := by
  first | exact @GlobalTheory.HSAmp.volDens_meas_finite_openPos | exact GlobalTheory.HSAmp.volDens_meas_finite_openPos | (intros; apply GlobalTheory.HSAmp.volDens_meas_finite_openPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.PullPow

theorem gdeg_pull_and_isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX
  refine ⟨fun Y _ q hY π hπ hη hδ L => GlobalTheory.CovTest.gdegPull k X Y p q D hX hY π hπ hη hδ L, ?_⟩
  intro L n a ha
  exact GlobalTheory.SelfInterPow.isSelfInter_pow hC k X p D hX L a ha n

end GlobalTheory.HSAmp.PullPow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreeProjectionFormulaSelfInterPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  first | exact @GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow | exact GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow | (intros; apply GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow <;> assumption)
end
end
