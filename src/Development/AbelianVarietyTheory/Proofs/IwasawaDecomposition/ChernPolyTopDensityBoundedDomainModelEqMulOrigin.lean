module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyConjLinearSubstCurvature
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyConjLinearSubstCurvature
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernConj

theorem charpolyRev_map_hom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) : M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_conj {R : Type} [CommRing R] {m : ℕ} (P Q M : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) : (P * M * Q).charpolyRev = M.charpolyRev := by
  have hPQ' : P.map Polynomial.C * Q.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.charpolyRev, Matrix.charpolyRev]
  have e : (1 : Matrix (Fin m) (Fin m) (Polynomial R)) - (Polynomial.X : Polynomial R) • (P * M * Q).map Polynomial.C
      = P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.map_mul, Matrix.map_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

theorem chernPoly_conj_subst : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  intro n r F v v' J S hS h k
  set φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) with hφ
  have hP : (S⁻¹).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : curvPoly F v = (S⁻¹).map C * (curvPoly F v').map φ * S.map C := by
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [curvPoly, h, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, aeval_C, aeval_X, hφ, MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => enter [2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, q]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p, 2, c]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q, 2, p]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q]; rw [Finset.sum_comm]
    conv_rhs => enter [2, a, 2, b, 2, q, 2, c]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hN : -curvPoly F v = (S⁻¹).map C * (-curvPoly F v').map (φ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * S.map C := by
    rw [hA, Matrix.map_neg, Matrix.mul_neg, Matrix.neg_mul]
    · rfl
    · exact fun a => map_neg φ a
  unfold chernPoly
  rw [hN, charpolyRev_conj _ _ _ hP, ← charpolyRev_map_hom, Polynomial.coeff_map]
  rfl

end GlobalTheory.ChernConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyConjLinearSubstCurvatureStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPoly_conj_linearSubst_curvature : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  first | exact @GlobalTheory.ChernConj.chernPoly_conj_subst | exact GlobalTheory.ChernConj.chernPoly_conj_subst | (intros; apply GlobalTheory.ChernConj.chernPoly_conj_subst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbedding
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section ModelCurv

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

def entryCLM (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℂ ℂ a b) ∘ₗ Z)

theorem mContDiffAt_linear {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this]
  exact ((entryCLM Z a b).contDiff.restrict_scalars ℝ).contDiffAt

theorem mdel_linear (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  rw [mdel_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, del_eq_fderiv (entryCLM Z a b).differentiableAt, (entryCLM Z a b).fderiv]
  rfl

theorem mdbar_linear (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  rw [mdbar_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, dbar_eq_zero (entryCLM Z a b).differentiableAt]
  rfl

theorem mdel_one_sub_gram (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => 1 - (Z u)ᴴ * Z u) x ξ = -((Z x)ᴴ * Z ξ) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdel_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 ξ
  rw [mdel_linear, mdel_conjTranspose, mdbar_linear, conjTranspose_zero, Matrix.zero_mul,
    add_zero] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdel_const, zero_add,
    mdel_neg, h]

theorem mdbar_one_sub_gram (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => 1 - (Z u)ᴴ * Z u) x η = -((Z η)ᴴ * Z x) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdbar_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 η
  rw [mdbar_linear, mdbar_conjTranspose, mdel_linear, Matrix.mul_zero, zero_add] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdbar_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdbar_const, zero_add,
    mdbar_neg, h]

theorem inv_one_sub_mul_conjTranspose (z : Matrix (Fin p) (Fin q) ℂ) (hu : IsUnit (1 - zᴴ * z).det) :
    (1 - z * zᴴ)⁻¹ = 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ := by
  apply Matrix.inv_eq_right_inv
  have hAQ : (1 - zᴴ * z) * (1 - zᴴ * z)⁻¹ = 1 := mul_nonsing_inv _ hu
  set Q := (1 - zᴴ * z)⁻¹
  have hQ : Q = 1 + zᴴ * (z * Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at hAQ
    rw [Matrix.mul_assoc] at hAQ
    exact hAQ
  have key : z * (Q * zᴴ) = z * zᴴ + z * (zᴴ * (z * (Q * zᴴ))) := by
    nth_rewrite 1 [hQ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  nth_rewrite 1 [key]
  abel

theorem curv_inv_one_sub_gram (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - (Z u)ᴴ * Z u) x := fun x =>
    (mContDiffAt_const 1).sub ((mContDiffAt_linear Z x).conjTranspose.mul (mContDiffAt_linear Z x))
  have hu : IsUnit (1 - (Z w)ᴴ * Z w).det := hw.det_pos.ne'.isUnit
  have hconn : ∀ x, IsUnit (1 - (Z x)ᴴ * Z x).det →
      conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ = ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ := by
    intro x hx
    have h : (((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ)ᵀ * (1 - (Z x)ᴴ * Z x)⁻¹ =
        mdel (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ := by
      rw [transpose_transpose, mdel_inv ((hA x).of_le one_le_two) hx, mdel_one_sub_gram]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    exact (eq_conn_of_compatible (H := fun u => (1 - (Z u)ᴴ * Z u)⁻¹) (z := x)
      (isUnit_nonsing_inv_det _ hx) h).symm
  have he : (fun x => conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ) =ᶠ[𝓝 w]
      fun x => ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ :=
    ((hA w).eventually_isUnit hu).mono fun x hx => hconn x hx
  have hI : MContDiffAt 1 (fun x => (1 - (Z x)ᴴ * Z x)⁻¹) w := ((hA w).of_le one_le_two).inv hu
  have h1 : MContDiffAt 1 (fun u => Z u) w := mContDiffAt_linear Z w
  rw [curv, mdbar_congr he, mdbar_transpose (fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ),
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ) (B := fun _ => Z ξ)
      (hI.mul h1.conjTranspose) (mContDiffAt_const (Z ξ)), mdbar_const, Matrix.mul_zero, zero_add,
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹) (B := fun x => (Z x)ᴴ) hI h1.conjTranspose,
    mdbar_inv ((hA w).of_le one_le_two) hu, mdbar_one_sub_gram, mdbar_conjTranspose, mdel_linear,
    inv_one_sub_mul_conjTranspose (Z w) hu]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, Matrix.mul_assoc]

end ModelCurv

theorem curv_modelGram_tauBar : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)
    (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef →
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ :=
  fun Z w ξ η hw => curv_inv_one_sub_gram Z w ξ η hw

end GlobalTheory.PointChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbeddingStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η = -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_tauBar | exact GlobalTheory.PointChern.curv_modelGram_tauBar | (intros; apply GlobalTheory.PointChern.curv_modelGram_tauBar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDet
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem posDef_eq_conjTranspose_mul_self_of_isUnit_det :
    ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef →
      ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  intro p P hP
  have h0 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP.posSemidef
  have hB : star (CFC.sqrt P) * CFC.sqrt P = P := by
    rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self P h0]
  refine ⟨CFC.sqrt P, ?_, hB⟩
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  rw [← hB, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDetStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef : ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef → ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  first | exact @GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | exact GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | (intros; apply GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrame
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.ChernReindex

variable {n a b : ℕ}

theorem mdel_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.mdel (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.mdel H z ξ) := by
  ext i j; rfl

theorem conn_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.conn (fun u => Matrix.reindex e e (H u)) z ξ = Matrix.reindex e e (GlobalTheory.HermFrame.conn H z ξ) := by
  rw [GlobalTheory.HermFrame.conn, GlobalTheory.HermFrame.conn, mdel_reindex, Matrix.transpose_reindex, Matrix.transpose_reindex,
    Matrix.inv_reindex, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

theorem curv_reindex (e : Fin a ≃ Fin b) (H : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (z ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.HermFrame.curv (fun u => Matrix.reindex e e (H u)) z ξ η = Matrix.reindex e e (GlobalTheory.HermFrame.curv H z ξ η) := by
  unfold GlobalTheory.HermFrame.curv
  simp_rw [conn_reindex]
  ext i j; rfl

theorem curvPoly_reindex (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.reindex e e (F u)) v = Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v) := by
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, curv_reindex]
  rfl

theorem charpolyRev_reindex {R : Type} [CommRing R] (e : Fin a ≃ Fin b) (M : Matrix (Fin a) (Fin a) R) :
    (Matrix.reindex e e M).charpolyRev = M.charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, Matrix.charpoly_reindex]

theorem chernPoly_reindex : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  intro n a b e F v k
  rw [GlobalTheory.GoodMetric.chernPoly, GlobalTheory.GoodMetric.chernPoly, curvPoly_reindex,
    show -(Matrix.reindex e e (GlobalTheory.GoodMetric.curvPoly F v)) = Matrix.reindex e e (-GlobalTheory.GoodMetric.curvPoly F v) from by
      ext i j; rfl, charpolyRev_reindex]

end GlobalTheory.ChernReindex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrameStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPolyCoeff_reindex_frame : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  first | exact @GlobalTheory.ChernReindex.chernPoly_reindex | exact GlobalTheory.ChernReindex.chernPoly_reindex | (intros; apply GlobalTheory.ChernReindex.chernPoly_reindex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwap
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PosDefSwap


open scoped Matrix.Norms.L2Operator in
theorem one_sub_mul_conjTranspose_posDef {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (h : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).PosDef := by
  have h1 : ‖z‖ < 1 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one z).mp h
  have h2 : ‖zᴴ‖ < 1 := by rwa [Matrix.l2_opNorm_conjTranspose]
  have h3 := (GlobalTheory.MatrixBall.posDef_iff_norm_lt_one zᴴ).mpr h2
  rwa [Matrix.conjTranspose_conjTranspose] at h3

theorem main : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef :=
  fun z h => one_sub_mul_conjTranspose_posDef z h

end GlobalTheory.PosDefSwap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwapStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef := by
  first | exact @GlobalTheory.PosDefSwap.main | exact GlobalTheory.PosDefSwap.main | (intros; apply GlobalTheory.PosDefSwap.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInv
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInv
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section LinearModel

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

noncomputable def linMatEntry (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => Z u a b
      map_add' := fun u v => by simp
      map_smul' := fun c u => by simp }

theorem mContDiffAt_linMat (k : WithTop ℕ∞) (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ((linMatEntry Z a b).restrictScalars ℝ : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem mdel_linMat (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdel_apply, this, del_eq_fderiv (linMatEntry Z a b).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_linMat (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdbar_apply, this, dbar_eq_zero (linMatEntry Z a b).differentiableAt]
  rfl

theorem mdel_linMat_conjTranspose (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => (Z u)ᴴ) x ξ = 0 := by
  rw [mdel_conjTranspose, mdbar_linMat, conjTranspose_zero]

theorem mdbar_linMat_conjTranspose (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => (Z u)ᴴ) x η = (Z η)ᴴ := by
  rw [mdbar_conjTranspose, mdel_linMat]

theorem mdel_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => C - B u) x ξ = -mdel B x ξ := by
  ext a b
  simp only [mdel_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [del_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem mdbar_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => C - B u) x η = -mdbar B x η := by
  ext a b
  simp only [mdbar_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [dbar_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem curv_modelGram_lie (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  have hZ : ∀ x, MContDiffAt 2 (fun u => Z u) x := mContDiffAt_linMat Z 2
  have hB : ∀ x, MContDiffAt 2 (fun u => Z u * (Z u)ᴴ) x :=
    fun x => (hZ x).mul (hZ x).conjTranspose
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - Z u * (Z u)ᴴ) x :=
    fun x => (mContDiffAt_const 1).sub (hB x)
  have hAu : IsUnit (1 - Z w * (Z w)ᴴ).det := by
    rw [det_one_sub_mul_comm]; exact hw.det_pos.ne'.isUnit
  have hH : (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) =
      fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ := by
    funext u
    have e : 1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ = (1 - Z u * (Z u)ᴴ)ᵀ := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]
    rw [e, transpose_nonsing_inv]
  have hconn : ∀ x, IsUnit (1 - Z x * (Z x)ᴴ).det →
      conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ = Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ := by
    intro x hx
    have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) x := (hA x).of_le one_le_two
    have hZ1 : MContDiffAt 1 (fun u => Z u) x := (hZ x).of_le one_le_two
    have hdA : mdel (fun u => 1 - Z u * (Z u)ᴴ) x ξ = -(Z ξ * (Z x)ᴴ) := by
      rw [mdel_const_sub _ ((hB x).of_le one_le_two), mdel_mul hZ1 hZ1.conjTranspose,
        mdel_linMat, mdel_linMat_conjTranspose, Matrix.mul_zero, zero_add]
    rw [conn, transpose_transpose, nonsing_inv_nonsing_inv _ hx,
      mdel_transpose (fun u => (1 - Z u * (Z u)ᴴ)⁻¹), transpose_transpose, mdel_inv h1 hx, hdA]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hx]
  have hev : (fun x => conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ) =ᶠ[𝓝 w]
      fun x => Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ :=
    ((hA w).eventually_isUnit hAu).mono fun x hx => hconn x hx
  have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) w := (hA w).of_le one_le_two
  have hZ1 : MContDiffAt 1 (fun u => Z u) w := (hZ w).of_le one_le_two
  have hdA : mdbar (fun u => 1 - Z u * (Z u)ᴴ) w η = -(Z w * (Z η)ᴴ) := by
    rw [mdbar_const_sub _ ((hB w).of_le one_le_two), mdbar_mul hZ1 hZ1.conjTranspose,
      mdbar_linMat, mdbar_linMat_conjTranspose, Matrix.zero_mul, add_zero]
  rw [hH, curv, mdbar_congr hev,
    mdbar_mul ((mContDiffAt_const (Z ξ)).mul hZ1.conjTranspose) (h1.inv hAu), mdbar_inv h1 hAu,
    mdbar_mul (mContDiffAt_const _) hZ1.conjTranspose, mdbar_linMat_conjTranspose, mdbar_const,
    hdA]
  have hP : (1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹ = 1 := mul_nonsing_inv _ hAu
  have hQ : (1 - (Z w)ᴴ * Z w)⁻¹ = 1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w := by
    apply Matrix.inv_eq_right_inv
    have e : (1 - (Z w)ᴴ * Z w) * (1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w) =
        1 - (Z w)ᴴ * Z w + (Z w)ᴴ * ((1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹) * Z w := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    rw [e, hP, Matrix.mul_one, sub_add_cancel]
  rw [hQ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc, neg_add]
  abel

end LinearModel

end GlobalTheory.PointChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInvStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η = -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_lie | exact GlobalTheory.PointChern.curv_modelGram_lie | (intros; apply GlobalTheory.PointChern.curv_modelGram_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOrigin
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.PointChernScale

open Matrix
open scoped ComplexOrder

theorem curv_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv Z w ξ η hw

theorem curv_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding Z w ξ η hw

theorem exists_factor {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : P.PosDef) :
    ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef P hP

theorem posDef_swap {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap z h

theorem chernPoly_conj {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n)
    (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ a b, curv F v (coordVec a) (coordVec b) =
      S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) (k : ℕ) :
    chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (chernPoly F v' k) := GlobalTheory.T.chernPoly_conj_linearSubst_curvature F v v' J S hS h k

theorem chernPoly_reindex {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) : chernPoly (fun u => reindex e e (F u)) v k = chernPoly F v k := GlobalTheory.T.chernFormPolyCoeff_reindex_frame e F v k

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def zLin {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin Dw.p) (Fin Dw.q) ℂ where
  toFun u := coordOf ix u σ
  map_add' u v := by ext i j; simp [coordOf]
  map_smul' c u := by ext i j; simp [coordOf]

theorem zLin_apply {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) (u : ReciprocityTheory.L2DbarEstimates.V n) : zLin ix σ u = coordOf ix u σ := rfl

def jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun c a =>
  (A (ix c).1 * coordOf ix (coordVec a) (ix c).1 * B (ix c).1) (ix c).2.1 (ix c).2.2

theorem zLin_jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ)
    (σ : GlobalTheory.AllWt.Psi H) (a : Fin n) :
    zLin ix σ (∑ c, jMat ix A B c a • coordVec c) = A σ * zLin ix σ (coordVec a) * B σ := by
  ext i j
  change (∑ c, jMat ix A B c a • coordVec c) (ix.symm (σ, i, j)) = _
  simp [WithLp.ofLp_sum, Finset.sum_apply, jMat, zLin_apply, Pi.single_apply]

theorem conj_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hA : IsUnit A.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w (coordVec a) (coordVec b) =
      A⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) * A := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) =
      -(Z (∑ c, J c a • coordVec c) * (Z (∑ d, J d b • coordVec d))ᴴ) := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 ξ η = -(Z ξ * (Z η)ᴴ) := by
      intro ξ η
      rw [curv_tau Z 0 ξ η h0]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul, Matrix.sum_mul,
      Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]; rfl
  rw [hsum, hJ, hJ, curv_tau Z w _ _ hw, ← hAA, ← hB]
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hA]

theorem conj_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hB0 : IsUnit B.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w (coordVec a) (coordVec b) =
      (Bᵀ)⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) * Bᵀ := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) =
      -((Z (∑ d, J d b • coordVec d))ᴴ * Z (∑ c, J c a • coordVec c))ᵀ := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 ξ η = -((Z η)ᴴ * Z ξ)ᵀ := by
      intro ξ η
      rw [curv_tauBar Z 0 ξ η h0]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_neg,
      Finset.sum_neg_distrib, neg_inj, transpose_sum, transpose_smul]
    simp only [Finset.smul_sum, smul_smul]
    rfl
  rw [hsum, hJ, hJ, curv_tauBar Z w _ _ hw, ← hAA, ← hB, ← transpose_nonsing_inv, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj, ← transpose_mul, ← transpose_mul]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB0]

theorem chernPoly_model_eq_subst {H : Host E} (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n) (hw : InDom (coordOf ix w)) :
    ∃ J : Matrix (Fin n) (Fin n) ℂ, ∀ (τ : E →+* ℂ) (k : ℕ),
      chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) w k =
        aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
          (chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) 0 k) := by
  have hP : ∀ σ, (1 - coordOf ix w σ * (coordOf ix w σ)ᴴ)⁻¹.PosDef := fun σ => (posDef_swap _ (hw σ)).inv
  have hQ : ∀ σ, (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹.PosDef := fun σ => (hw σ).inv
  choose A hA hAA using fun σ => exists_factor _ (hP σ)
  choose A' hA' hAA' using fun σ => exists_factor _ (hQ σ)
  let B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ := fun σ => (A' σ)ᴴ
  have hB : ∀ σ, B σ * (B σ)ᴴ = (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹ := fun σ => by
    simp only [B, conjTranspose_conjTranspose]; exact hAA' σ
  have hB0 : ∀ σ, IsUnit (B σ).det := fun σ => by
    simp only [B, det_conjTranspose]; exact (hA' σ).star
  refine ⟨jMat ix A B, fun τ k => ?_⟩
  by_cases h : τ (H.rt : E) = H.rt0
  · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
        reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
          ((1 - (zLin ix ⟨τ, h⟩ u).map (starRingEnd ℂ) * (zLin ix ⟨τ, h⟩ u)ᵀ)⁻¹) := by
      funext u; simp only [modelGram, dif_pos h]; rfl
    rw [e, chernPoly_reindex, chernPoly_reindex]
    exact chernPoly_conj _ w 0 _ (A ⟨τ, h⟩) (hA _)
      (conj_tau (zLin ix ⟨τ, h⟩) w (A _) (B _) _ (hw _) (hA _) (hAA _) (hB _) (zLin_jMat ix A B _)) k
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
          reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
            ((1 - (zLin ix ⟨conjEmb τ, h'⟩ u)ᴴ * zLin ix ⟨conjEmb τ, h'⟩ u)⁻¹) := by
        funext u; simp only [modelGram, dif_neg h, dif_pos h']; rfl
      rw [e, chernPoly_reindex, chernPoly_reindex]
      exact chernPoly_conj _ w 0 _ (B _)ᵀ (by rw [det_transpose]; exact hB0 _)
        (conj_tauBar (zLin ix ⟨conjEmb τ, h'⟩) w (A _) (B _) _ (hw _) (hB0 _) (hAA _) (hB _)
          (zLin_jMat ix A B _)) k
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun _ => 1 := by
        funext u; simp only [modelGram, dif_neg h, dif_neg h']
      have hc : ∀ v, chernPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v k =
          (1 : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)).coeff k := by
        intro v
        have h0 : curvPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v = 0 := by
          ext i j; simp [curvPoly]
        simp [chernPoly, h0, Matrix.charpolyRev]
      rw [e, hc, hc, Polynomial.coeff_one]
      split_ifs <;> simp

end GlobalTheory.PointChernScale


open GlobalTheory.PointChernScale in
theorem GlobalTheory.PointChern.chernTop_model_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) →
    ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ,
      chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  intro E _ _ _ H Dw n ix w hw
  obtain ⟨J, hJ⟩ := chernPoly_model_eq_subst Dw ix w hw
  refine ⟨Complex.normSq J.det, fun R => ?_⟩
  let φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)
  have hR : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) w x.2) R =
      φ (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) R) := by
    have := congrArg (fun f => f R) (MvPolynomial.comp_aeval (R := ℝ)
      (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (φ.restrictScalars ℝ))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => (aeval f R : MvPolynomial (Fin n × Fin n) ℂ)) (funext fun x => hJ x.1 x.2)
  simp only [chernTop]
  rw [hR, GlobalTheory.GoodMetric.topCoeff_subst_conj, Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOriginStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_boundedDomainModel_eq_mul_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  first | exact @GlobalTheory.PointChern.chernTop_model_eq_mul | exact GlobalTheory.PointChern.chernTop_model_eq_mul | (intros; apply GlobalTheory.PointChern.chernTop_model_eq_mul <;> assumption)
end
