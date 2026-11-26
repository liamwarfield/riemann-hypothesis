module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

variable (d : ℕ)

theorem X_mem_one (i : Fin (d + 1)) : (X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ 1 :=
  isHomogeneous_X ℂ i

abbrev chart (i : Fin (d + 1)) : (PSpace ℂ d).Opens := Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)

def ratioSec (i j : Fin (d + 1)) : Γ(PSpace ℂ d, chart d i) :=
  Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i)
    (Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j))

variable {d} {Z : Scheme.{0}} [IsIntegral Z]


open Classical in
def rat (φ : Z ⟶ PSpace ℂ d) (i j : Fin (d + 1)) : Z.functionField :=
  if h : genericPoint Z ∈ φ ⁻¹ᵁ chart d i then
    Z.presheaf.germ (φ ⁻¹ᵁ chart d i) (genericPoint Z) h (φ.app (chart d i) (ratioSec d i j))
  else 0

variable [Algebra ℂ Z.functionField]

def fld (φ : Z ⟶ PSpace ℂ d) : IntermediateField ℂ Z.functionField := IntermediateField.adjoin ℂ (Set.range (rat φ 0))

def crd (φ : Z ⟶ PSpace ℂ d) : Fin (d + 1) → fld φ := fun j =>
  ⟨rat φ 0 j, IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩⟩

theorem crd_val (φ : Z ⟶ PSpace ℂ d) (j : Fin (d + 1)) : ((crd φ j : fld φ) : Z.functionField) = rat φ 0 j := rfl

end GlobalTheory.PD.XCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDiv
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
open MvPolynomial HomogeneousLocalization

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Overlap

variable {d : ℕ}

def awayRatio (i j : Fin (d + 1)) : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) :=
  Away.mk (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 (X j) (by simpa using X_mem_one d j)

theorem ratioSec_eq (i j : Fin (d + 1)) :
    ratioSec d i j = Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X i) (awayRatio i j) := rfl

theorem germ_awayToSection_mul (a b : Fin (d + 1)) {x : MvPolynomial (Fin (d + 1)) ℂ} (hx : x = X a * X b)
    (y : PSpace ℂ d) (hya : y ∈ chart d a)
    (hy : y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) x)
    (s : Away (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a)) :
    (PSpace ℂ d).presheaf.germ (chart d a) y hya
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) =
      (PSpace ℂ d).presheaf.germ _ y hy (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
        (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s)) := by
  have e := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ)
    (X_mem_one d b) hx) s
  simp only [ConcreteCategory.comp_apply] at e
  have e' : Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) x
      (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d b) hx s) =
      (PSpace ℂ d).presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op
        (Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a) s) := e
  rw [e', TopCat.Presheaf.germ_res_apply]

theorem awayRatio_mul_awayRatio (a i : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
        (rfl : X a * X i = X a * X i) (awayRatio a i) *
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i a) = 1 := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, Away.mk, Away.mk, val_awayMap_mk, val_awayMap_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem awayRatio_change (a i j : Fin (d + 1)) :
    HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
        (mul_comm (X a) (X i)) (awayRatio i j) =
      HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i)
          (rfl : X a * X i = X a * X i) (awayRatio a j) *
        HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d a)
          (mul_comm (X a) (X i)) (awayRatio i a) := by
  apply val_injective
  rw [HomogeneousLocalization.val_mul, awayRatio, awayRatio, awayRatio, Away.mk, Away.mk, Away.mk, val_awayMap_mk,
    val_awayMap_mk, val_awayMap_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

theorem rat_eq_germ {Z : Scheme.{0}} [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (k l : Fin (d + 1))
    (hk : genericPoint Z ∈ φ ⁻¹ᵁ chart d k) :
    rat φ k l = φ.stalkMap (genericPoint Z) ((PSpace ℂ d).presheaf.germ (chart d k) _ hk (ratioSec d k l)) := by
  unfold rat
  rw [dite_eq_left hk]
  exact (Scheme.Hom.germ_stalkMap_apply φ _ _ hk _).symm

end Overlap


open Overlap in
theorem rat_overlap : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)),
    genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i →
      rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  intro d Z _ φ a i j ha hi
  have hW : φ (genericPoint Z) ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) := by
    rw [Proj.basicOpen_mul]; exact ⟨ha, hi⟩
  let F := ((Proj.awayToSection (homogeneousSubmodule (Fin (d + 1)) ℂ) (X a * X i) ≫
    (PSpace ℂ d).presheaf.germ _ _ hW) ≫ φ.stalkMap (genericPoint Z)).hom
  have hA : ∀ l, rat φ a l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d i) (rfl : X a * X i = X a * X i) (awayRatio a l)) := by
    intro l
    rw [rat_eq_germ φ a l ha, ratioSec_eq, germ_awayToSection_mul a i rfl _ ha hW]
    rfl
  have hI : ∀ l, rat φ i l = F (HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (d + 1)) ℂ)
      (X_mem_one d a) (mul_comm (X a) (X i)) (awayRatio i l)) := by
    intro l
    rw [rat_eq_germ φ i l hi, ratioSec_eq, germ_awayToSection_mul i a (mul_comm (X a) (X i)) _ hi hW]
    rfl
  have h1 : rat φ a i * rat φ i a = 1 := by
    rw [hA, hI, ← map_mul, awayRatio_mul_awayRatio, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
  rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right h1, hI, hA, hI, ← map_mul, awayRatio_change]
end GlobalTheory.PD.XCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledBackProjCoordinateRatioOverlapDivStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (φ : Z ⟶ PSpace ℂ d) (a i j : Fin (d + 1)), genericPoint Z ∈ φ ⁻¹ᵁ chart d a → genericPoint Z ∈ φ ⁻¹ᵁ chart d i → rat φ a i ≠ 0 ∧ rat φ i j = rat φ a j / rat φ a i := by
  first | (exact @GlobalTheory.PD.XCover.rat_overlap) | (exact GlobalTheory.PD.XCover.rat_overlap) | (intros; apply GlobalTheory.PD.XCover.rat_overlap  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProjectiveChartAffineCover
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairwiseDisjointTriangularCells
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

theorem mem_span_X_of_pos {d n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin (d + 1)) ℂ}
    (hf : f.IsHomogeneous n) : f ∈ Ideal.span (Set.range (X : Fin (d + 1) → MvPolynomial _ ℂ)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  by_contra! H
  obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
  have := hf (mem_support_iff.1 hm)
  simp only [map_zero] at this
  omega

theorem iSup_chart_eq_top (d : ℕ) : ⨆ i, chart d i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _
    ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun _ hn _ hf => mem_span_X_of_pos hn hf)

theorem inf_chart_eq (d : ℕ) (I : Finset (Fin (d + 1))) :
    I.inf (fun i => chart d i) = Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) ℂ) (∏ i ∈ I, X i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.prod_insert ha, Proj.basicOpen_mul, ih]

theorem preimage_chart_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ],
    (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧
      ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  intro d Z φ _
  constructor
  · rw [← Scheme.Hom.preimage_iSup, iSup_chart_eq_top, Scheme.Hom.preimage_top]
  · intro I hI
    have key : (I.inf fun i => φ ⁻¹ᵁ chart d i) = φ ⁻¹ᵁ (I.inf fun i => chart d i) := by
      classical
      clear hI
      induction I using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, ih, Scheme.Hom.preimage_inf]
    rw [key, inf_chart_eq]
    have hdeg : (∏ i ∈ I, X i : MvPolynomial (Fin (d + 1)) ℂ) ∈ homogeneousSubmodule (Fin (d + 1)) ℂ I.card := by
      have := SetLike.prod_mem_graded (homogeneousSubmodule (Fin (d + 1)) ℂ) (fun _ => 1) (fun i => X i)
        (F := I) (fun i _ => X_mem_one d i)
      simpa using this
    exact (Proj.isAffineOpen_basicOpen _ _ hdeg (Finset.card_pos.2 hI)).preimage φ

end GlobalTheory.PD.XCover
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_affine_cover : ∀ (d : ℕ) (Z : Scheme.{0}) (φ : Z ⟶ PSpace ℂ d) [IsAffineHom φ], (⨆ i, φ ⁻¹ᵁ chart d i) = ⊤ ∧ ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsAffineOpen (I.inf fun i => φ ⁻¹ᵁ chart d i) := by
  first | (exact @GlobalTheory.PD.XCover.preimage_chart_cover) | (exact GlobalTheory.PD.XCover.preimage_chart_cover) | (intros; apply GlobalTheory.PD.XCover.preimage_chart_cover  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionFieldIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOrthogonalInvariantProjection
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

theorem mem_germ_range_of_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (y : Z.functionField), y ∈ rB ℂ Z.functionField (crd φ) I → ∃ f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i), (Z.presheaf.germ _ (genericPoint Z) h).hom f = y := by
  intro d Z _ p _ inst hinst φ _ _ hgen I hI h y hy
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have hsc : ∀ r : ℂ, algebraMap ℂ Z.functionField r = (Z.presheaf.germ ⊤ (genericPoint Z) trivial).hom
      (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) := by
    subst hinst; intro r; rfl
  set U : Z.Opens := I.inf fun i => φ ⁻¹ᵁ chart d i with hU
  have hUa : IsAffineOpen U := (GlobalTheory.T.projective_chart_affine_cover d Z φ).2 I hI
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hUa
  have halg : ∀ b, algebraMap Γ(Z, U) Z.functionField b = (Z.presheaf.germ U (genericPoint Z) h).hom b := fun _ => rfl
  haveI : IsIntegrallyClosed Γ(Z, U) := by
    have hs := p.smooth_appLE (U := ⊤) (isAffineOpen_top _) hUa (by simp)
    letI := (p.appLE ⊤ U (by simp)).hom.toAlgebra
    haveI : Algebra.Smooth Γ(Sp ℂ, ⊤) Γ(Z, U) := hs
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    haveI : IsDomain Γ(Sp ℂ, ⊤) := e.injective.isDomain (e : Γ(Sp ℂ, ⊤) →+* ℂ)
    haveI : IsIntegrallyClosed Γ(Sp ℂ, ⊤) := IsIntegrallyClosed.of_equiv e.symm
    exact isIntegrallyClosed_of_smooth Γ(Sp ℂ, ⊤) Γ(Z, U)
  have hgerm : ∀ a ∈ rA ℂ (crd φ) I, ∃ g : Γ(Z, U),
      (Z.presheaf.germ U (genericPoint Z) h).hom g = ((a : fld φ) : Z.functionField) := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi, j, rfl⟩ := hx
      have hle : U ≤ φ ⁻¹ᵁ chart d i := Finset.inf_le hi
      refine ⟨Z.presheaf.map (homOfLE hle).op (φ.app (chart d i) (ratioSec d i j)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      have hr := (GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d Z φ 0 i j (hgen 0) (hgen i)).2
      simp only [IntermediateField.coe_div, crd_val]
      rw [← hr, rat, dite_eq_left (hgen i)]
    | algebraMap r =>
      refine ⟨Z.presheaf.map (homOfLE le_top).op (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)), ?_⟩
      rw [Z.presheaf.germ_res_apply]
      exact (hsc r).symm
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g + g', by rw [map_add (f := _), hg, hg']; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      exact ⟨g * g', by rw [map_mul, hg, hg']; rfl⟩
  have hy' : IsIntegral (rA ℂ (crd φ) I) y := hy
  have hB : IsIntegral Γ(Z, U) y := by
    obtain ⟨q, hq, hqy⟩ := hy'
    have hl : q.map (algebraMap (rA ℂ (crd φ) I) Z.functionField) ∈
        Polynomial.lifts (algebraMap Γ(Z, U) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨g, hg⟩ := hgerm _ (q.coeff n).2
      exact ⟨g, by rw [halg, hg]; rfl⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hq.map _)
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map, hqy]
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hB
  exact ⟨b, hb⟩

end GlobalTheory.PD.XCover
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_function_field_integral : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (y : Z.functionField), y ∈ rB ℂ Z.functionField (crd φ) I → ∃ f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i), (Z.presheaf.germ _ (genericPoint Z) h).hom f = y := by
  first | (exact @GlobalTheory.PD.XCover.mem_germ_range_of_mem_rB) | (exact GlobalTheory.PD.XCover.mem_germ_range_of_mem_rB) | (intros; apply GlobalTheory.PD.XCover.mem_germ_range_of_mem_rB  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatios
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatios
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped GlobalTheory.ProjSpace
namespace GlobalTheory.PD.XCover.Integ
attribute [local instance] MvPolynomial.gradedAlgebra
variable {d : ℕ}

theorem ratioSec_eq_ratio (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  rw [ratioSec, GlobalTheory.ProjFrac.awayToSection_mk]
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem basicOpen_ratioSec (a i : Fin (d + 1)) :
    (PSpace ℂ d).basicOpen (ratioSec d a i) = chart d a ⊓ chart d i := by
  rw [ratioSec_eq_ratio]
  exact GlobalTheory.ProjSpace.basicOpen_ratioOn

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem basicOpen_prod (φ : Z ⟶ PSpace ℂ d) (a : Fin (d + 1)) (T : Finset (Fin (d + 1))) :
    Z.basicOpen (φ.app (chart d a) (∏ i ∈ T, ratioSec d a i)) =
      φ ⁻¹ᵁ chart d a ⊓ T.inf fun i => φ ⁻¹ᵁ chart d i := by
  rw [← Scheme.preimage_basicOpen]
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.basicOpen_of_isUnit _ isUnit_one, Finset.inf_empty, inf_top_eq]
  | insert j T hj ih =>
    rw [Finset.prod_insert hj, Scheme.basicOpen_mul, Scheme.Hom.preimage_inf, ih, basicOpen_ratioSec,
      Scheme.Hom.preimage_inf, Finset.inf_insert, inf_inf_inf_comm, inf_idem]

theorem rat_eq (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1)) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (ratioSec d a j)) := by
  rw [rat, dite_eq_left ha]

theorem germ_const (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (c : ℂ) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) (algebraMap ℂ Γ(PSpace ℂ d, chart d a) c)) =
      algebraMap ℂ Z.functionField c := by
  subst hinst hφ
  rw [GlobalTheory.ProjSpace.algebraMap_sections_eq]
  simp only [Scheme.Hom.appLE, ffAlg, RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Hom.comp_appTop]
  generalize (CommRingCat.Hom.hom (Scheme.Hom.app (PSpace.str ℂ d) ⊤))
    ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv) c) = w
  have e := ConcreteCategory.congr_hom (φ.naturality (homOfLE (le_top : chart d a ≤ ⊤)).op) w
  simp only [ConcreteCategory.comp_apply] at e
  erw [e, TopCat.Presheaf.germ_res_apply]
  rfl

theorem germ_mem_adjoin (p : Z ⟶ Sp ℂ) [inst : Algebra ℂ Z.functionField] (hinst : inst = ffAlg p)
    (φ : Z ⟶ PSpace ℂ d) (hφ : φ ≫ PSpace.str ℂ d = p) (a : Fin (d + 1))
    (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) (t : Γ(PSpace ℂ d, chart d a)) :
    Z.presheaf.germ (φ ⁻¹ᵁ chart d a) (genericPoint Z) ha (φ.app (chart d a) t) ∈
      Algebra.adjoin ℂ (Set.range (rat φ a)) := by
  obtain ⟨q, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d a t
  induction q using MvPolynomial.induction_on with
  | C c => rw [aeval_C, germ_const p hinst φ hφ a ha c]; exact Subalgebra.algebraMap_mem _ c
  | add q r hq hr => rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem hq hr
  | mul_X q j hq =>
    rw [map_mul, map_mul, map_mul, aeval_X, ← ratioSec_eq_ratio, ← rat_eq φ a j ha]
    exact mul_mem hq (Algebra.subset_adjoin ⟨j, rfl⟩)

theorem rat_eq_crd [Algebra ℂ Z.functionField] (φ : Z ⟶ PSpace ℂ d) (a j : Fin (d + 1))
    (h0 : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (ha : genericPoint Z ∈ φ ⁻¹ᵁ chart d a) :
    rat φ a j = algebraMap (fld φ) Z.functionField (crd φ j / crd φ a) := by
  rw [map_div₀]
  exact (rat_overlap d Z φ 0 a j h0 ha).2

end GlobalTheory.PD.XCover.Integ


open GlobalTheory.PD.XCover.Integ in
theorem GlobalTheory.PD.XCover.germ_mem_rB : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  intro d Z _ p _ inst hinst φ _ hφ hgen I hI h f
  obtain ⟨a, ha⟩ := hI
  have hV : IsAffineOpen (chart d a) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d a
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d a) := hV.preimage φ
  have hsub : Algebra.adjoin ℂ (Set.range (rat φ a)) ≤
      (rA ℂ (crd φ) I).map (IsScalarTower.toAlgHom ℂ (fld φ) Z.functionField) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact ⟨crd φ j / crd φ a, Algebra.subset_adjoin ⟨a, ha, j, rfl⟩, (rat_eq_crd φ a j (hgen 0) (hgen a)).symm⟩
  have hint : ∀ y : Γ(Z, φ ⁻¹ᵁ chart d a),
      IsIntegral (rA ℂ (crd φ) I) ((Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y) := by
    intro y
    obtain ⟨P, hPm, hP⟩ := IsIntegralHom.isIntegral_app φ _ hV y
    set G := (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom
    have hlift : P.map (G.comp (φ.app (chart d a)).hom) ∈
        Polynomial.lifts (algebraMap (rA ℂ (crd φ) I) Z.functionField) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨x, hx, hxy⟩ := hsub (germ_mem_adjoin p hinst φ hφ a (hgen a) (P.coeff n))
      exact ⟨⟨x, hx⟩, hxy⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.map _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
  set s := φ.app (chart d a) (∏ i ∈ I, ratioSec d a i) with hs
  have hbo : Z.basicOpen s = I.inf fun i => φ ⁻¹ᵁ chart d i := by
    rw [hs, basicOpen_prod]
    exact inf_eq_right.2 (Finset.inf_le (f := fun i => φ ⁻¹ᵁ chart d i) ha)
  have hgs : (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom s = ∏ i ∈ I, rat φ a i := by
    rw [hs, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => (rat_eq φ a i (hgen a)).symm
  have hinv : (∏ i ∈ I, rat φ a i)⁻¹ = algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i) := by
    rw [map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [rat_eq_crd φ a i (hgen 0) (hgen a), ← map_inv₀, inv_div]
  have hne : (∏ i ∈ I, rat φ a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => (rat_overlap d Z φ a i i (hgen a) (hgen i)).1
  suffices H : ∀ (W : Z.Opens) (hW : W = Z.basicOpen s) (h : genericPoint Z ∈ W) (f : Γ(Z, W)),
      (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I from H _ hbo.symm h f
  rintro W rfl h f
  haveI := hU.isLocalization_basicOpen s
  obtain ⟨⟨y, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers s) f
  dsimp only at e
  have hres : ∀ z : Γ(Z, φ ⁻¹ᵁ chart d a), (Z.presheaf.germ _ (genericPoint Z) h).hom
      (algebraMap Γ(Z, φ ⁻¹ᵁ chart d a) Γ(Z, Z.basicOpen s) z) = (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom z :=
    fun z => Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le s)) _ h z
  have e' := congrArg (Z.presheaf.germ _ (genericPoint Z) h).hom e
  rw [map_mul, hres, hres, map_pow, hgs] at e'
  have hf : (Z.presheaf.germ _ (genericPoint Z) h).hom f =
      (Z.presheaf.germ _ (genericPoint Z) (hgen a)).hom y * ((∏ i ∈ I, rat φ a i)⁻¹) ^ n := by
    rw [inv_pow, ← e', mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]
  have hr : (∏ i ∈ I, crd φ a / crd φ i) ∈ rA ℂ (crd φ) I :=
    prod_mem fun i hi => Algebra.subset_adjoin ⟨i, hi, a, rfl⟩
  have hA : IsIntegral (rA ℂ (crd φ) I)
      (algebraMap (fld φ) Z.functionField (∏ i ∈ I, crd φ a / crd φ i)) :=
    isIntegral_algebraMap (R := rA ℂ (crd φ) I) (A := Z.functionField) (x := ⟨_, hr⟩)
  rw [hf, hinv]
  exact (Subalgebra.mem_restrictScalars ℂ).2 ((hint y).mul (hA.pow n))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericGermChartInterIntegralCoordinateRatiosStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → ∀ (I : Finset (Fin (d + 1))), I.Nonempty → ∀ (h : genericPoint Z ∈ I.inf fun i => φ ⁻¹ᵁ chart d i) (f : Γ(Z, I.inf fun i => φ ⁻¹ᵁ chart d i)), (Z.presheaf.germ _ (genericPoint Z) h).hom f ∈ rB ℂ Z.functionField (crd φ) I := by
  first | (exact @GlobalTheory.PD.XCover.germ_mem_rB) | (exact GlobalTheory.PD.XCover.germ_mem_rB) | (intros; apply GlobalTheory.PD.XCover.germ_mem_rB  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteProjectionFunctionField
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilIntegralParahoricEquivariance
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

noncomputable section

namespace GlobalTheory.PD.XCover

theorem finiteDimensional_of_finite {A B F K : Type} [CommRing A] [CommRing B] [Field F] [Field K] [Algebra F K]
    (ψ : B →+* A) (hψ : ψ.Finite) (g : A →+* K) (hB : ∀ b, g (ψ b) ∈ Set.range (algebraMap F K))
    (hfr : ∀ x : K, ∃ a b : A, g b ≠ 0 ∧ x * g b = g a) : FiniteDimensional F K := by
  letI := ψ.toAlgebra
  haveI : Module.Finite B A := hψ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := A)
  let M : Submodule F K := Submodule.span F (g '' (s : Set A))
  have hMfg : M.FG := Submodule.fg_span (s.finite_toSet.image g)
  have hM : ∀ a : A, g a ∈ M := by
    intro a
    have ha : a ∈ Submodule.span B (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact M.add_mem hx hy
    | smul b x _ hx =>
      obtain ⟨c, hc⟩ := hB b
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, ← hc, ← Algebra.smul_def]
      exact M.smul_mem c hx
  let R := Algebra.adjoin F (Set.range g)
  have hRM : Subalgebra.toSubmodule R ≤ M := by
    rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ g.range.toSubmonoid := (Submonoid.closure_le.2 (fun y hy => hy)) hx
    obtain ⟨a, rfl⟩ := hx'
    exact hM a
  have hRfg : (Subalgebra.toSubmodule R).FG := by
    haveI : FiniteDimensional F M := Module.Finite.iff_fg.2 hMfg
    exact isNoetherian_submodule.1 inferInstance _ hRM
  have htop : ∀ z : K, z ∈ M := by
    intro z
    obtain ⟨a, b, hb, e⟩ := hfr z
    have hbR : g b ∈ R := Algebra.subset_adjoin ⟨b, rfl⟩
    have hint : IsIntegral F (g b) := IsIntegral.of_mem_of_fg R hRfg _ hbR
    have hinv : (g b)⁻¹ ∈ R := Subalgebra.inv_mem_of_algebraic R (x := ⟨g b, hbR⟩) hint.isAlgebraic
    have hz : z = g a * (g b)⁻¹ := by rw [← e, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [hz]
    exact hRM (R.mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) hinv)
  have : M = ⊤ := eq_top_iff.2 fun z _ => htop z
  exact ⟨this ▸ hMfg⟩

variable {d : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ratioSec_eq (i j : Fin (d + 1)) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  refine (GlobalTheory.ProjFrac.awayToSection_mk (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (d + 1)) ℂ) (X_mem_one d i) 1 _).trans ?_
  exact GlobalTheory.ProjFrac.frac_eq (by ring)

theorem exists_frac_germ (Z : Scheme.{0}) [IsIntegral Z] (U : Z.Opens) (hU : IsAffineOpen U) (h : genericPoint Z ∈ U)
    (x : Z.functionField) : ∃ a b : Γ(Z, U), (Z.presheaf.germ U _ h).hom b ≠ 0 ∧
      x * (Z.presheaf.germ U _ h).hom b = (Z.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, U)) x
  have hb' : algebraMap Γ(Z, U) Z.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem germ_app_mem (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) (φ : Z ⟶ PSpace ℂ d)
    (hp : φ ≫ PSpace.str ℂ d = p) (h : genericPoint Z ∈ φ ⁻¹ᵁ chart d 0) (b : Γ(PSpace ℂ d, chart d 0)) :
    letI := ffAlg p
    (Z.presheaf.germ _ _ h).hom ((φ.app (chart d 0)).hom b) ∈ fld φ := by
  letI := ffAlg p
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℂ d 0 b
  have e := congrArg (fun t => t P) (GlobalTheory.ProjSpace.appLE_comp_aeval_ratio (φ := φ) (W := φ ⁻¹ᵁ chart d 0) (i := 0) (hi := le_rfl))
  simp only [RingHom.comp_apply, RingHom.coe_coe] at e
  rw [← Scheme.Hom.appLE_eq_app, e, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
  refine MvPolynomial.eval₂_mem (fun _ _ => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, hp]
    have hc : ∀ c : ℂ, (Z.presheaf.germ _ _ h).hom ((GlobalTheory.QCoh.Qcqs.baseRingHom p (φ ⁻¹ᵁ chart d 0)).hom c) =
        algebraMap ℂ Z.functionField c := by
      intro c
      rw [← GlobalTheory.QCoh.Qcqs.baseRingHom_res p (le_top : φ ⁻¹ᵁ chart d 0 ≤ ⊤), Z.presheaf.germ_res_apply,
        GlobalTheory.QCoh.Qcqs.baseRingHom_top]
      rfl
    rw [hc]
    exact IntermediateField.algebraMap_mem _ _
  · have hr : (Z.presheaf.germ _ _ h).hom (GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl j) = rat φ 0 j := by
      rw [rat, dite_eq_left h, ratioSec_eq, ← Scheme.Hom.appLE_eq_app]
      rfl
    simp only [Function.comp_apply]
    rw [hr]
    exact IntermediateField.subset_adjoin ℂ _ ⟨j, rfl⟩

theorem finiteDimensional_fld : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p →
    (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  intro d Z _ p _ inst hinst φ _ hp hgen
  subst hinst
  have hC : IsAffineOpen (chart d 0) := GlobalTheory.ProjSpace.isAffineOpen_chart ℂ d 0
  have hU : IsAffineOpen (φ ⁻¹ᵁ chart d 0) := hC.preimage φ
  exact finiteDimensional_of_finite (φ.app (chart d 0)).hom (φ.finite_app _ hC) (Z.presheaf.germ _ _ (hgen 0)).hom
    (fun b => ⟨⟨_, germ_app_mem Z p φ hp (hgen 0) b⟩, rfl⟩) (exists_frac_germ Z _ hU (hgen 0))

end GlobalTheory.PD.XCover
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projection_function_field : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → FiniteDimensional (fld φ) Z.functionField := by
  first | (exact @GlobalTheory.PD.XCover.finiteDimensional_fld) | (exact GlobalTheory.PD.XCover.finiteDimensional_fld) | (intros; apply GlobalTheory.PD.XCover.finiteDimensional_fld  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AffineGermSubalgebraSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermImageSmooth
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory

theorem germImage_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  intro Z _ p hp inst hinst U hU h B hB
  exact smooth_sections_in_functionField Z p hp hinst U hU h B hB

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_germ_subalgebra_smooth : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [Smooth p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (U : Z.Opens), IsAffineOpen U → ∀ (h : genericPoint Z ∈ U) (B : Subalgebra ℂ Z.functionField), (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) h).hom f = y) → Algebra.Smooth ℂ B := by
  first | (exact @GlobalTheory.germImage_smooth) | (exact GlobalTheory.germImage_smooth) | (intros; apply GlobalTheory.germImage_smooth  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRati
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRati
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem injective_mvPolynomial_of_finite_of_ringKrullDim {k B : Type} [Field k] [CommRing B] {d : ℕ}
    (ψ : MvPolynomial (Fin d) k →+* B) (hψ : ψ.Finite) (hB : ringKrullDim B = d) :
    Function.Injective ψ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := (RingHom.kerLift ψ).toAlgebra
  have hfin : (RingHom.kerLift ψ).Finite := by
    have e : ψ = (RingHom.kerLift ψ).comp (Ideal.Quotient.mk _) := by
      ext x <;> rfl
    exact RingHom.Finite.of_comp_finite (e ▸ hψ)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := ⟨hfin.to_isIntegral⟩
  have e1 : ringKrullDim B = ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) :=
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (RingHom.kerLift_injective ψ)
  have e2 : ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) ≤
      ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (by rw [Ideal.span_singleton_le_iff_mem]; exact hr))
  have e3 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at e3
  have e4 : (d : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    (hB.symm.trans e1).le.trans e2
  have h := (add_le_add e4 (le_refl (1 : WithBot ℕ∞))).trans e3
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, zero_add] at h
  norm_cast at h
  omega

theorem ratioSec_eq_projSpace_ratio (d : ℕ) (i j : Fin (d + 1)) (h : j ≠ i) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  have e := GlobalTheory.ProjSpace.chartAlgEquiv_X ℂ d i ⟨j, h⟩
  rw [GlobalTheory.ProjSpace.chartAlgEquiv_apply, GlobalTheory.ProjSpace.polyToAway, MvPolynomial.eval₂Hom_X'] at e
  exact e

theorem algebraicIndependent_rat : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p →
    ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) →
      AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  intro d Z _ p _ inst hinst φ _ hφ hgen
  subst hφ
  obtain ⟨hU, hψ₀⟩ := (GlobalTheory.ProjSpace.isFinite_iff_pullRatio φ (U := fun i => φ ⁻¹ᵁ chart d i)
    (fun _ => rfl)).1 inferInstance 0
  set c := (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str ℂ d) (φ ⁻¹ᵁ chart d 0)).hom with hc
  set y := GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl with hy
  let ψ : MvPolynomial (Fin d) ℂ →+* Γ(Z, φ ⁻¹ᵁ chart d 0) := MvPolynomial.eval₂Hom c (fun j => y j.succ)
  let σ : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin d) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)
  have hcomp : ψ.comp σ = MvPolynomial.eval₂Hom c y := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp [ψ, σ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [ψ, σ, y]
      · simp [ψ, σ]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (hcomp ▸ hψ₀)
  have hdim : ringKrullDim Γ(Z, φ ⁻¹ᵁ chart d 0) = d :=
    GlobalTheory.SmoothDim.ringKrullDim_affineOpen ℂ Z (φ ≫ PSpace.str ℂ d) d inferInstance _ hU ⟨_, hgen 0⟩
  have hinj : Function.Injective ψ := injective_mvPolynomial_of_finite_of_ringKrullDim ψ hψ hdim
  have hgerm : Function.Injective (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom :=
    germ_injective_of_isIntegral Z _ (hgen 0)
  have key : (MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)).toRingHom =
      (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_C]
      subst hinst
      have e : (φ ≫ PSpace.str ℂ d).appLE ⊤ (φ ⁻¹ᵁ chart d 0) le_top =
          (φ ≫ PSpace.str ℂ d).appTop ≫ Z.presheaf.map (homOfLE le_top).op := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_map _ _ _).symm
      rw [hc, GlobalTheory.QCoh.Qcqs.baseRingHom, CommRingCat.hom_comp, RingHom.comp_apply, e,
        CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_X']
      rw [rat, dite_eq_left (hgen 0), hy, GlobalTheory.ProjSpace.pullRatio, ← ratioSec_eq_projSpace_ratio d 0 j.succ (Fin.succ_ne_zero j),
        Scheme.Hom.app_eq_appLE]
  rw [algebraicIndependent_iff_injective_aeval]
  have : ⇑(MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)) =
      ⇑((Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ) :=
    congrArg DFunLike.coe key
  rw [this]
  exact hgerm.comp hinj

end GlobalTheory.PD.XCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicIndependentPulledBackProjCoordinateRatiStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p → ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) → AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  first | (exact @GlobalTheory.PD.XCover.algebraicIndependent_rat) | (exact GlobalTheory.PD.XCover.algebraicIndependent_rat) | (intros; apply GlobalTheory.PD.XCover.algebraicIndependent_rat  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSmoothFiniteCoverOfFormsNoCommonZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace ℂ N)

theorem resG_fRatio {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n) (hg : g ∈ grading ℂ N n)
    {W : X.Opens} (hW : W ≤ fOpen ι g) {V : (PSpace ℂ N).Opens} (hV : V ≤ Proj.basicOpen (grading ℂ N) g)
    (hWV : W ≤ ι ⁻¹ᵁ V) :
    resG X hW (fRatio ι a g ha hg) = (ι.appLE V W hWV).hom (frac (grading ℂ N) V a g ha hg hV) := by
  have e : fRatio ι a g ha hg = (ι.appLE (Proj.basicOpen (grading ℂ N) g) (fOpen ι g) le_rfl).hom
      (frac (grading ℂ N) _ a g ha hg le_rfl) := by
    unfold fRatio; rw [Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact (resG_appLE ι _ hW _).trans (appLE_resG ι hV hWV _).symm

theorem basicOpen_fRatio_le {n : ℕ} {a g : MvPolynomial (Fin (N + 1)) ℂ} (ha : a ∈ grading ℂ N n)
    (hg : g ∈ grading ℂ N n) : X.basicOpen (fRatio ι a g ha hg) ≤ fOpen ι a := by
  have e : X.basicOpen (fRatio ι a g ha hg) =
      ι ⁻¹ᵁ (PSpace ℂ N).basicOpen (frac (grading ℂ N) _ a g ha hg le_rfl) :=
    (Scheme.preimage_basicOpen ι _).symm
  rw [e, basicOpen_frac]
  exact ι.preimage_mono inf_le_right

variable {d n : ℕ} (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ grading ℂ N n)

theorem isCoordFamily_fRatio (hcov : ⨆ i, fOpen ι (f i) = ⊤) :
    IsCoordFamily (fun i => fOpen ι (f i)) (fun i j => fRatio ι (f j) (f i) (hf j) (hf i)) := by
  refine { cover := hcov
           self := fun i => fRatio_self ι (f i) (hf i)
           mul := ?_
           basicOpen_le := fun i j => basicOpen_fRatio_le ι (hf j) (hf i) }
  intro i j k
  have hWV : fOpen ι (f i) ⊓ fOpen ι (f j) ≤
      ι ⁻¹ᵁ (Proj.basicOpen (grading ℂ N) (f i) ⊓ Proj.basicOpen (grading ℂ N) (f j)) :=
    fun x hx => ⟨hx.1, hx.2⟩
  rw [resG_fRatio ι (hf j) (hf i) _ inf_le_left hWV, resG_fRatio ι (hf k) (hf j) _ inf_le_right hWV,
    resG_fRatio ι (hf k) (hf i) _ inf_le_left hWV, ← map_mul]
  exact congrArg _ (frac_mul_eq (by ring))

def formMap (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤) : X ⟶ PSpace ℂ d :=
  (isCoordFamily_fRatio ι f hf hcov).toHom p

variable (p : X ⟶ Sp ℂ) (hcov : ⨆ i, fOpen ι (f i) = ⊤)

theorem formMap_preimage (i : Fin (d + 1)) : formMap ι f hf p hcov ⁻¹ᵁ chart ℂ d i = fOpen ι (f i) :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_preimage p i

theorem formMap_str : formMap ι f hf p hcov ≫ PSpace.str ℂ d = p :=
  (isCoordFamily_fRatio ι f hf hcov).toHom_str p

theorem pullRatio_formMap (i j : Fin (d + 1)) :
    pullRatio (formMap ι f hf p hcov) (fOpen ι (f i)) i (formMap_preimage ι f hf p hcov i).ge j =
      fRatio ι (f j) (f i) (hf j) (hf i) :=
  (isCoordFamily_fRatio ι f hf hcov).pullRatio_toHom p i j

theorem isAffineOpen_fOpen [IsClosedImmersion ι] {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N n)
    (hn : 0 < n) : IsAffineOpen (fOpen ι g) :=
  (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg hn).preimage ι

theorem isFinite_formMap [IsClosedImmersion ι] (hp : ι ≫ PSpace.str ℂ N = p) (hn : 0 < n) :
    IsFinite (formMap ι f hf p hcov) := by
  haveI := isProper_str ℂ N
  haveI := isProper_str ℂ d
  have h1 : IsProper (formMap ι f hf p hcov ≫ PSpace.str ℂ d) := by
    rw [formMap_str, ← hp]; infer_instance
  exact IsFinite.iff_isProper_and_isAffineHom.2 ⟨IsProper.of_comp _ (PSpace.str ℂ d),
    isAffineHom_of_isAffineOpen_preimage_chart _ fun i => by
      rw [formMap_preimage]; exact isAffineOpen_fOpen ι (hf i) hn⟩

theorem germ_appLE {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ U) (x : X) (hx : x ∈ W)
    (s : Γ(Y, U)) : (X.presheaf.germ W x hx).hom ((φ.appLE U W h).hom s) =
      (X.presheaf.germ (φ ⁻¹ᵁ U) x (h hx)).hom ((φ.app U).hom s) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

theorem ratioSec_eq (i j : Fin (d + 1)) : XCover.ratioSec d i j = ratio ℂ d i j :=
  (awayToSection_mk _ 1 _).trans (frac_eq (by ring))

theorem rat_formMap [IsIntegral X] (j : Fin (d + 1)) (hg : genericPoint X ∈ fOpen ι (f 0)) :
    XCover.rat (formMap ι f hf p hcov) 0 j =
      (X.presheaf.germ (fOpen ι (f 0)) (genericPoint X) hg).hom (fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  have hmem : genericPoint X ∈ formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d 0 :=
    (formMap_preimage ι f hf p hcov 0).ge hg
  rw [XCover.rat, dite_eq_left hmem, ← pullRatio_formMap ι f hf p hcov 0 j, pullRatio, germ_appLE, ratioSec_eq]


open XCover in
theorem exists_finCover_of_isFinite {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField] (hinst : inst = ffAlg p) (φ : X ⟶ PSpace ℂ d) [IsFinite φ]
    (hφ : φ ≫ PSpace.str ℂ d = p) (hgen : ∀ i, genericPoint X ∈ φ ⁻¹ᵁ XCover.chart d i) :
    IsFinCover ℂ X.functionField (crd φ) ∧ IsAffCover p (fun i => φ ⁻¹ᵁ XCover.chart d i) (rB ℂ X.functionField (crd φ)) := by
  have hrat := GlobalTheory.T.pulledBackProjCoordinateRatio_overlap_div d X φ
  have h00 : rat φ 0 0 = 1 := by
    obtain ⟨h1, h2⟩ := hrat 0 0 0 (hgen 0) (hgen 0)
    rw [div_self h1] at h2
    exact h2
  have hch := GlobalTheory.T.projective_chart_affine_cover d X φ
  have hne : ∀ I : Finset (Fin (d + 1)), genericPoint X ∈ I.inf fun i => φ ⁻¹ᵁ XCover.chart d i := by
    intro I
    induction I using Finset.induction_on with
    | empty => simp
    | insert a s _ ih => rw [Finset.inf_insert]; exact ⟨hgen a, ih⟩
  have hring : ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ y, y ∈ rB ℂ X.functionField (crd φ) I ↔
      ∃ f : Γ(X, I.inf fun i => φ ⁻¹ᵁ XCover.chart d i), (X.presheaf.germ _ (genericPoint X) (hne I)).hom f = y := by
    intro I hI y
    constructor
    · exact GlobalTheory.T.chart_function_field_integral d X p hinst φ hφ hgen I hI (hne I) y
    · rintro ⟨f, rfl⟩
      exact GlobalTheory.T.genericGerm_chartInter_integral_coordinateRatios d X p hinst φ hφ hgen I hI (hne I) f
  have h1 : crd φ 0 = 1 := Subtype.ext h00
  haveI : CharZero (fld φ) := charZero_of_injective_algebraMap (algebraMap ℂ (fld φ)).injective
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  refine ⟨IsFinCover.of_charZero ⟨?_, ?_, ?_⟩ (GlobalTheory.T.finite_projection_function_field d X p hinst φ hφ hgen) ?_,
    ⟨?_, fun I hI => hch.2 I hI, hch.1, hne, hring⟩⟩
  · intro i h
    exact (hrat 0 i i (hgen 0) (hgen i)).1 (by simpa [crd_val] using congrArg (fun z : fld φ => (z : X.functionField)) h)
  · simp only [h1, div_one]
    exact AlgebraicIndependent.of_comp (fld φ).val (GlobalTheory.T.algebraicIndependent_pulledBackProjCoordinateRatios d X p hinst φ hφ hgen)
  · simp only [h1, div_one]
    rw [eq_top_iff]
    intro z _
    have hle : fld φ ≤ (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => crd φ j.succ)).map (fld φ).val := by
      show IntermediateField.adjoin ℂ _ ≤ _
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨j, rfl⟩
      induction j using Fin.cases with
      | zero => rw [h00]; exact one_mem _
      | succ k => exact (IntermediateField.mem_map _).2 ⟨crd φ k.succ, IntermediateField.subset_adjoin ℂ _ ⟨k, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (IntermediateField.mem_map _).1 (hle z.2)
    have : w = z := Subtype.ext hwz
    rwa [← this]
  · intro i
    exact GlobalTheory.T.affine_germ_subalgebra_smooth X p hinst _ (hch.2 {i} (Finset.singleton_nonempty i)) (hne {i}) _
      (hring {i} (Finset.singleton_nonempty i))
  · subst hinst
    rfl

theorem isFinCover_of_forms : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p]
    [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι →
    ι ≫ PSpace.str ℂ N = p → ∀ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n → (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) →
    ∀ hg : (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)), ∃ (F : IntermediateField ℂ X.functionField)
    (x : Fin (d + 1) → F), IsFinCover ℂ X.functionField x ∧
    IsAffCover p (fun i => GlobalTheory.EtProj.fOpen ι (f i)) (rB ℂ X.functionField x) ∧
    ∀ j, algebraMap F X.functionField (x j) = (X.presheaf.germ (GlobalTheory.EtProj.fOpen ι (f 0)) (genericPoint X) (hg 0)).hom
      (GlobalTheory.EtProj.fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  intro X _ p d _ inst hinst N ι hι hp n f hf hn hcov hg
  haveI : IsFinite (formMap ι f hf p hcov) := isFinite_formMap ι f hf p hcov hp hn
  have hpre := formMap_preimage ι f hf p hcov
  obtain ⟨h1, h2⟩ := exists_finCover_of_isFinite p d hinst (formMap ι f hf p hcov) (formMap_str ι f hf p hcov)
    fun i => (hpre i).ge (hg i)
  have hU : (fun i => formMap ι f hf p hcov ⁻¹ᵁ XCover.chart d i) = fun i => fOpen ι (f i) := funext hpre
  rw [hU] at h2
  exact ⟨_, _, h1, h2, fun j => rat_formMap ι f hf p hcov j (hg 0)⟩

end GlobalTheory.EtProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSmoothFiniteCoverOfFormsNoCommonZeroStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteCover_affineCover_of_forms_no_commonZero : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → ∀ (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ (n : ℕ) (f : Fin (d + 1) → MvPolynomial (Fin (N + 1)) ℂ) (hf : ∀ i, f i ∈ GlobalTheory.ProjSpace.grading ℂ N n), 0 < n → (⨆ i, GlobalTheory.EtProj.fOpen ι (f i) = ⊤) → ∀ hg : (∀ i, genericPoint X ∈ GlobalTheory.EtProj.fOpen ι (f i)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F), IsFinCover ℂ X.functionField x ∧ IsAffCover p (fun i => GlobalTheory.EtProj.fOpen ι (f i)) (rB ℂ X.functionField x) ∧ ∀ j, algebraMap F X.functionField (x j) = (X.presheaf.germ (GlobalTheory.EtProj.fOpen ι (f 0)) (genericPoint X) (hg 0)).hom (GlobalTheory.EtProj.fRatio ι (f j) (f 0) (hf j) (hf 0)) := by
  first | (exact @GlobalTheory.EtProj.isFinCover_of_forms) | (exact GlobalTheory.EtProj.isFinCover_of_forms) | (intros; apply GlobalTheory.EtProj.isFinCover_of_forms  <;> assumption)
end
