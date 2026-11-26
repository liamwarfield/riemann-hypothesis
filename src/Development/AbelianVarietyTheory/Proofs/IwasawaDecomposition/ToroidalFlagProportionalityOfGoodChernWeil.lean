module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieGramIsGoodMumford
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactDualLinearFormFlagDegreePointClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOrigin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeGramLocalModelAlgebraicChartHolomorphic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralPointPolyCovol

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointwiseHodge
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernDensityLieGramRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnit
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem mContDiffAt_coordOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (σ : GlobalTheory.AllWt.Psi H) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u => coordOf ix u σ) w := fun a b => by
  have : (fun u : ReciprocityTheory.L2DbarEstimates.V n => coordOf ix u σ a b) =
      ((EuclideanSpace.proj (𝕜 := ℂ) (ix.symm (σ, a, b))).restrictScalars ℝ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem one_sub_map_conj_mul_transpose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - z.map (starRingEnd ℂ) * zᵀ) = (1 - z * zᴴ)ᵀ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]

theorem isUnit_det_one_sub_map_conj {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - z.map (starRingEnd ℂ) * zᵀ).det := by
  rw [one_sub_map_conj_mul_transpose, det_transpose, det_one_sub_mul_comm]
  exact (h.det_pos.ne').isUnit

theorem isUnit_det_one_sub_conjTranspose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - zᴴ * z).det :=
  (h.det_pos.ne').isUnit

theorem MContDiffAt.map_conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m n : Type*} {k : WithTop ℕ∞}
    {A : V → Matrix m n ℂ} {z : V} (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => (A x).map (starRingEnd ℂ)) z :=
  fun a b => Complex.conjCLE.contDiff.contDiffAt.comp z (h a b)

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern
open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem modelGram_smooth_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  intro E _ _ _ H Dw n ix w hw τ
  by_cases h : τ (H.rt : E) = H.rt0
  · have hZ := mContDiffAt_coordOf ix ⟨τ, h⟩ w
    have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨τ, h⟩).map (starRingEnd ℂ) * (coordOf ix u ⟨τ, h⟩)ᵀ) w :=
      (mContDiffAt_const 1).sub ((GlobalTheory.PointChern.MContDiffAt.map_conj hZ).mul hZ.transpose)
    have hu := isUnit_det_one_sub_map_conj _ (hw ⟨τ, h⟩)
    simp only [modelGram, dif_pos h]
    refine ⟨?_, ?_⟩
    · simp only [reindex_apply]
      exact (hA.inv hu).submatrix _ _
    · rw [det_reindex_self]
      exact isUnit_nonsing_inv_det_iff.mpr hu
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have hZ := mContDiffAt_coordOf ix ⟨conjEmb τ, h'⟩ w
      have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨conjEmb τ, h'⟩)ᴴ * coordOf ix u ⟨conjEmb τ, h'⟩) w :=
        (mContDiffAt_const 1).sub (hZ.conjTranspose.mul hZ)
      have hu := isUnit_det_one_sub_conjTranspose _ (hw ⟨conjEmb τ, h'⟩)
      simp only [modelGram, dif_neg h, dif_pos h']
      refine ⟨?_, ?_⟩
      · simp only [reindex_apply]
        exact (hA.inv hu).submatrix _ _
      · rw [det_reindex_self]
        exact isUnit_nonsing_inv_det_iff.mpr hu
    · simp only [modelGram, dif_neg h, dif_neg h']
      exact ⟨mContDiffAt_const 1, by simp⟩

end GlobalTheory.PointChern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnitStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomainModelGram_contDiff_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  first | exact @GlobalTheory.PointChern.modelGram_smooth_isUnit | exact GlobalTheory.PointChern.modelGram_smooth_isUnit | (intros; apply GlobalTheory.PointChern.modelGram_smooth_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZero
open scoped Matrix

namespace GlobalTheory.HermFrame

open Matrix Filter Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [DecidableEq m] [Fintype l]

theorem curv_inv_one_sub_mul {P : E → Matrix m l ℂ} {Q : E → Matrix l m ℂ} {z ξ η : E}
    {C : Matrix l m ℂ} (hP : ∀ x, MContDiffAt 2 P x) (hQ : ∀ x, MContDiffAt 2 Q x)
    (hP0 : P z = 0) (hdP : ∀ x, mdel P x ξ = 0) (hdQ : ∀ x, mdel Q x ξ = C) :
    curv (fun x => (1 - P x * Q x)⁻¹) z ξ η = -(mdbar P z η * C)ᵀ := by
  have hK : ∀ x, MContDiffAt 2 (fun x => 1 - P x * Q x) x :=
    fun x => (mContDiffAt_const 1).sub ((hP x).mul (hQ x))
  have hK0 : (1 - P z * Q z) = 1 := by rw [hP0]; simp
  have hd : ∀ x, mdel (fun x => 1 - P x * Q x) x ξ = -(P x * C) := fun x => by
    have h1 := (hP x).of_le one_le_two
    have h2 := (hQ x).of_le one_le_two
    simp only [sub_eq_add_neg]
    rw [mdel_add (mContDiffAt_const 1) (h1.mul h2).neg, mdel_neg, mdel_mul h1 h2, hdP, hdQ]
    simp
  have hdd : mddbar (fun x => 1 - P x * Q x) z ξ η = -(mdbar P z η * C) := by
    rw [← mdbar_mdel (hK z)]
    simp only [hd]
    rw [mdbar_neg, mdbar_mul ((hP z).of_le one_le_two) (mContDiffAt_const C)]
    simp
  have hu : IsUnit (1 - P z * Q z)ᵀ.det := by rw [hK0]; simp
  have e : (fun x => (1 - P x * Q x)⁻¹) = fun x => dualGram (1 - P x * Q x)ᵀ := by
    funext x; rw [dualGram, transpose_nonsing_inv, transpose_transpose]
  rw [e, curv_dual (hK z).transpose hu, curv_eq (hK z).transpose hu,
    mdel_transpose (fun x => 1 - P x * Q x), hd,
    show mddbar (fun x => (1 - P x * Q x)ᵀ) z ξ η = (mddbar (fun x => 1 - P x * Q x) z ξ η)ᵀ from rfl,
    hdd, hK0, hP0]
  simp

end

section

variable {n : ℕ} {a b : Type*}

theorem mContDiffAt_coordMatrix (f : a → b → Fin n) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w := fun i j =>
  ((EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ).contDiff.contDiffAt

theorem mdel_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ =
      Matrix.of fun i j => ξ (f i j) := by
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ := EuclideanSpace.proj (𝕜 := ℂ) (f i j)
  change del L w ξ = L ξ
  rw [del_eq_fderiv L.differentiableAt, L.fderiv]

theorem mdbar_coordMatrix (f : a → b → Fin n) (w ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ = 0 := by
  have h := mdel_add_mdbar (fun u : ReciprocityTheory.L2DbarEstimates.V n => Matrix.of fun i j => u (f i j)) w ξ
  rw [mdel_coordMatrix] at h
  rw [← add_right_inj (Matrix.of fun i j => ξ (f i j)), h, add_zero]
  ext i j
  let L : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (f i j)).restrictScalars ℝ
  change fderiv ℝ L w ξ = L ξ
  rw [L.fderiv]

end

theorem curv_inv_one_sub_conj_mul_transpose_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  intro n r s f g ξ η
  let Z : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (f i j)
  let W : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin s) ℂ := fun u => Matrix.of fun i j => u (g i j)
  have h := curv_inv_one_sub_mul (P := fun u => (Z u)ᴴᵀ) (Q := fun u => (W u)ᵀ) (z := 0) (ξ := ξ)
    (η := η) (C := (W ξ)ᵀ) (fun x => (mContDiffAt_coordMatrix f x).conjTranspose.transpose)
    (fun x => (mContDiffAt_coordMatrix g x).transpose) (by ext i j; simp [Z])
    (fun x => by
      rw [mdel_transpose (fun u => (Z u)ᴴ), mdel_conjTranspose, mdbar_coordMatrix]; simp)
    (fun x => by rw [mdel_transpose W, mdel_coordMatrix])
  rw [mdbar_transpose (fun u => (Z u)ᴴ), mdbar_conjTranspose, mdel_coordMatrix, ← transpose_mul,
    transpose_transpose] at h
  exact h

end GlobalTheory.HermFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInvOneSubConjMulTransposeAtZeroStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero : ∀ {n r s : ℕ} (f g : Fin r → Fin s → Fin n) (ξ η : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.HermFrame.curv (fun u : ReciprocityTheory.L2DbarEstimates.V n => (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 ξ η = -((Matrix.of fun i j => ξ (g i j)) * (Matrix.of fun i j => η (f i j))ᴴ) := by
  first | exact @GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero | exact GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero | (intros; apply GlobalTheory.HermFrame.curv_inv_one_sub_conj_mul_transpose_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer
namespace GlobalTheory

open Polynomial

theorem charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero
    {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ}
    (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R)
    (h : ∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) :
    M.charpolyRev * N.charpolyRev = 1 := by
  set f := M.charpolyRev
  set g := N.charpolyRev
  have hS : (PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
      (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h (k + 1) (Nat.le_add_left 1 k)]
  have hd : derivative (f * g) = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      GroundTheory.Global.coe_derivative_charpolyRev, GroundTheory.Global.coe_derivative_charpolyRev,
      Polynomial.coe_zero]
    calc -(f : PowerSeries R) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) * (g : PowerSeries R) +
          (f : PowerSeries R) * (-(g : PowerSeries R) * PowerSeries.mk fun k => (N ^ (k + 1)).trace)
        = -((f : PowerSeries R) * (g : PowerSeries R)) *
          ((PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
            (PowerSeries.mk fun k => (N ^ (k + 1)).trace)) := by ring
      _ = 0 := by rw [hS, mul_zero]
  have h0 : (f * g).coeff 0 = 1 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, Matrix.eval_charpolyRev,
      mul_one]
  ext k
  rcases k with _ | k
  · rw [h0, Polynomial.coeff_one_zero]
  · have hk := congrArg (fun r => r.coeff k) hd
    simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk
    have hu : IsUnit ((k : R) + 1) := by
      have : ((k : R) + 1) = algebraMap K R ((k : K) + 1) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero k)).map _
    rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact hu.mul_left_eq_zero.mp hk

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero : ∀ {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ} (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R), (∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) → M.charpolyRev * N.charpolyRev = 1 := by
  first | exact @GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | exact GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | (intros; apply GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZero
noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.SuperTrace

variable {n : ℕ}

def Sg (m : ℕ) (z : Big n) : Prop :=
  ∀ a : Fin n, ((1 : Ext n) ⊗ₜ vec n a) * z = (-1) ^ m * (z * ((1 : Ext n) ⊗ₜ vec n a))

theorem sg_zero (m : ℕ) : Sg m (0 : Big n) := by intro a; simp

theorem sg_add {m : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg m w) : Sg m (z + w) := by
  intro a; rw [mul_add, hz a, hw a, add_mul, mul_add]

theorem sg_sum {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → Big n) (h : ∀ i ∈ s, Sg m (f i)) :
    Sg m (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using sg_zero m
  | cons x s hx ih =>
    rw [Finset.sum_cons]
    exact sg_add (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem sg_mul {m l : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg l w) : Sg (m + l) (z * w) := by
  intro a
  have hc : Commute ((-1 : Big n) ^ l) z := (Commute.neg_one_left z).pow_left l
  rw [← mul_assoc, hz a, mul_assoc, mul_assoc, hw a, pow_add, ← mul_assoc z, ← hc.eq]
  simp only [mul_assoc]

theorem sg_one : Sg 0 (1 : Big n) := by intro a; simp

theorem sg_left (x : Ext n) : Sg 0 (x ⊗ₜ (1 : Ext n)) := by
  intro a; simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem sg_right (b : Fin n) : Sg 1 ((1 : Ext n) ⊗ₜ vec n b) := by
  intro a
  simp [Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n a b, TensorProduct.tmul_neg]

def MSg {r s : Type*} (m : ℕ) (M : Matrix r s (Big n)) : Prop := ∀ i j, Sg m (M i j)

theorem msg_mul {r s t : Type*} [Fintype s] {m l : ℕ} {M : Matrix r s (Big n)}
    {N : Matrix s t (Big n)} (hM : MSg m M) (hN : MSg l N) : MSg (m + l) (M * N) := by
  intro i j; rw [Matrix.mul_apply]; exact sg_sum _ _ _ fun k _ => sg_mul (hM i k) (hN k j)

theorem msg_one {r : Type*} [Fintype r] [DecidableEq r] : MSg 0 (1 : Matrix r r (Big n)) := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · exact sg_one
  · exact sg_zero 0

theorem msg_pow {r : Type*} [Fintype r] [DecidableEq r] {M : Matrix r r (Big n)} (hM : MSg 1 M)
    (j : ℕ) : MSg j (M ^ j) := by
  induction j with
  | zero => simpa using (msg_one : MSg 0 (1 : Matrix r r (Big n)))
  | succ j ih => rw [pow_succ]; exact msg_mul ih hM

theorem pow_mul_left {p q : ℕ} {R : Type*} [Semiring R] (A : Matrix (Fin p) (Fin q) R)
    (B : Matrix (Fin q) (Fin p) R) (m : ℕ) : (A * B) ^ m * A = A * (B * A) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc A B A]

theorem trace_swap {p q : ℕ} (A : Matrix (Fin p) (Fin q) (Big n)) (B : Matrix (Fin q) (Fin p) (Big n))
    (hA : MSg 0 A) (hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a) (m : ℕ) :
    ((B * A) ^ (m + 1)).trace = (-1) ^ m * ((A * B) ^ (m + 1)).trace := by
  have hB1 : MSg 1 B := by
    intro b i; obtain ⟨a, ha⟩ := hB b i; rw [ha]; exact sg_right a
  have hY : MSg m (A * (B * A) ^ m) := by
    simpa using msg_mul hA (msg_pow (by simpa using msg_mul hB1 hA) m)
  have h1 : (B * A) ^ (m + 1) = B * (A * (B * A) ^ m) := by
    rw [pow_succ', Matrix.mul_assoc]
  have h2 : (A * B) ^ (m + 1) = (A * (B * A) ^ m) * B := by
    rw [pow_succ, ← Matrix.mul_assoc, pow_mul_left]
  generalize A * (B * A) ^ m = Y at hY h1 h2
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨a, ha⟩ := hB b i
  rw [ha, hY i b a]

theorem val_trace {r : Type*} [Fintype r] (M : Matrix r r (EvenPart n)) :
    ((EvenPart n).val M.trace) = (M.map (EvenPart n).val).trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem val_pow {r : Type*} [Fintype r] [DecidableEq r] (M : Matrix r r (EvenPart n)) (k : ℕ) :
    (M ^ k).map (EvenPart n).val = (M.map (EvenPart n).val) ^ k :=
  map_pow ((EvenPart n).val.toRingHom.mapMatrix) M k

end GlobalTheory.GrassModel.SuperTrace

open GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace in
theorem GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar {n p q : ℕ}
    (e : Fin p × Fin q → Fin n) (k : ℕ) (hk : 1 ≤ k) :
    ((blockPoly e).map (toEven n) ^ k).trace + ((-blockPolyBar e).map (toEven n) ^ k).trace = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set A : Matrix (Fin p) (Fin q) (Big n) := Matrix.of fun i b => vec n (e (i, b)) ⊗ₜ (1 : Ext n)
  set B : Matrix (Fin q) (Fin p) (Big n) := Matrix.of fun b j => (1 : Ext n) ⊗ₜ vec n (e (j, b))
  have hA : MSg 0 A := fun i b => sg_left _
  have hB : ∀ b i, ∃ a, B b i = (1 : Ext n) ⊗ₜ vec n a := fun b i => ⟨e (i, b), rfl⟩
  have hL : ((blockPoly e).map (toEven n)).map (EvenPart n).val = A * B := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, B, blockPoly, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hD : (Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = B * A := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, B, blockPolyBar, toEven, gen, Matrix.mul_apply, map_sum, Algebra.TensorProduct.tmul_mul_tmul]
  have hneg : (-blockPolyBar e).map (toEven n) = -((blockPolyBar e).map (toEven n)) := by
    ext i j; simp
  apply Subtype.val_injective
  show (EvenPart n).val (_ + _) = (EvenPart n).val 0
  rw [map_add (f := _), map_zero, hneg, ← Matrix.trace_transpose (( -_ ) ^ _), Matrix.transpose_pow,
    Matrix.transpose_neg, val_trace, val_trace, val_pow, val_pow, hL]
  rw [show (-Matrix.transpose ((blockPolyBar e).map (toEven n))).map (EvenPart n).val = -(B * A) by
    rw [← hD]; ext i j; simp]
  rcases Nat.even_or_odd (m + 1) with h | h
  · rw [h.neg_pow, trace_swap A B hA hB m]
    have : Odd m := by rcases h with ⟨t, ht⟩; exact ⟨t - 1, by omega⟩
    rw [this.neg_one_pow]; simp
  · rw [h.neg_pow, Matrix.trace_neg, trace_swap A B hA hB m]
    have : Even m := by rcases h with ⟨t, ht⟩; exact ⟨t, by omega⟩
    rw [this.neg_one_pow]; simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero : ∀ {n p q : ℕ} (e : Fin p × Fin q → Fin n) (k : ℕ), 1 ≤ k → ((GlobalTheory.GrassModel.blockPoly e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace + ((-GlobalTheory.GrassModel.blockPolyBar e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace = 0 := by
  first | exact @GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | exact GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | (intros; apply GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZero
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open scoped Matrix

namespace GlobalTheory.PointChernRel

open GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointChern GlobalTheory.GrassModel MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

theorem chernPoly_reindex {n m p : ℕ} (h : p = m) (K : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin p) (Fin p) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => Matrix.reindex (finCongr h) (finCongr h) (K u)) v k = chernPoly K v k := by
  subst h
  simp

theorem curvPoly_model {n r s : ℕ} (f g : Fin r → Fin s → Fin n) :
    curvPoly (fun u : ReciprocityTheory.L2DbarEstimates.V n =>
      (1 - (Matrix.of fun i j => u (f i j)).map (starRingEnd ℂ) * (Matrix.of fun i j => u (g i j))ᵀ)⁻¹) 0 =
      -Matrix.of fun i j => ∑ c, X (g i c, f j c) := by
  refine Matrix.ext fun i j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvPoly, Matrix.of_apply, GlobalTheory.T.chernCurvature_inv_one_sub_conj_mul_transpose_at_zero, Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    coordVec, PiLp.single_apply, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero, map_neg, map_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul, neg_inj]
  have h (x y : Fin n) (c : Fin s) : C (if f j c = y then if g i c = x then (1 : ℂ) else 0 else 0) * X (x, y) =
      if (g i c, f j c) = (x, y) then X (g i c, f j c) else (0 : MvPolynomial (Fin n × Fin n) ℂ) := by
    by_cases h1 : f j c = y <;> by_cases h2 : g i c = x <;> simp [h1, h2]
  simp only [h]
  rw [← Fintype.sum_prod_type' (f := fun x y => ∑ c, if (g i c, f j c) = (x, y) then X (g i c, f j c) else 0), Finset.sum_comm]
  simp

theorem coeff_comp_neg_X' {R : Type} [CommRing R] (p : Polynomial R) (b : ℕ) :
    (p.comp (-Polynomial.X)).coeff b = (-1) ^ b * p.coeff b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, neg_pow,
      ← mul_assoc, show ((-1 : Polynomial R)) ^ m = Polynomial.C ((-1) ^ m) by simp, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

theorem coeff_neg_charpolyRev {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (b : ℕ) :
    (-M).charpolyRev.coeff b = (-1) ^ b * M.charpolyRev.coeff b := by
  have h : (-M).charpolyRev = M.charpolyRev.comp (-Polynomial.X) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    ext a c : 2
    by_cases h : a = c <;> simp [h]
  rw [h, coeff_comp_neg_X']

theorem charpolyRev_map' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem relation_top_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  intro E _ _ _ H Dw n ix τ k hk P
  set e : Fin Dw.p × Fin Dw.q → Fin n := fun x => ix.symm (τ, x.1, x.2) with he
  have hL : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) τ.1) 0 j = (blockPoly e).charpolyRev.coeff j := by
    intro j
    have h1 : (fun u => modelGram H Dw (coordOf ix u) τ.1) = fun u =>
        Matrix.reindex (finCongr (mult_of_mem Dw τ.2).symm) (finCongr (mult_of_mem Dw τ.2).symm)
          ((1 - (Matrix.of fun i c => u (e (i, c))).map (starRingEnd ℂ) * (Matrix.of fun i c => u (e (i, c)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_pos τ.2]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun i c => e (i, c)) (fun i c => e (i, c)), neg_neg]
    rfl
  have hc1 : ¬ conjEmb τ.1 (H.rt : E) = H.rt0 := GlobalTheory.AllWt.conj_not_mem τ
  have hc2 : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have hD : ∀ j, chernPoly (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) 0 j =
      (blockPolyBar e).charpolyRev.coeff j := by
    intro j
    have hτ : (⟨conjEmb (conjEmb τ.1), hc2⟩ : GlobalTheory.AllWt.Psi H) = τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
    have h1 : (fun u => modelGram H Dw (coordOf ix u) (conjEmb τ.1)) = fun u =>
        Matrix.reindex (finCongr (mult_of_not_mem Dw hc1).symm) (finCongr (mult_of_not_mem Dw hc1).symm)
          ((1 - (Matrix.of fun b i => u (e (i, b))).map (starRingEnd ℂ) * (Matrix.of fun b i => u (e (i, b)))ᵀ)⁻¹) := by
      funext u
      simp only [modelGram, dif_neg hc1, dif_pos hc2, hτ]
      rfl
    rw [h1, chernPoly_reindex, chernPoly, curvPoly_model (fun b i => e (i, b)) (fun b i => e (i, b)), neg_neg]
    rfl
  have hrel : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (relPoly τ k) =
      ((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [relPoly, map_sum, map_mul, aeval_X, aeval_C, hL, hD, Polynomial.coeff_mul, coeff_neg_charpolyRev]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_pow, map_neg, map_one]
    ring
  have hzero : toEven n (((blockPoly e).charpolyRev * (-blockPolyBar e).charpolyRev).coeff k) = 0 := by
    have h2 := GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero (K := ℂ) _ _ (GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero e)
    have e1 : ((blockPoly e).map (toEven n)).charpolyRev = (blockPoly e).charpolyRev.map (toEven n).toRingHom :=
      (charpolyRev_map' _ _).symm
    have e2 : ((-blockPolyBar e).map (toEven n)).charpolyRev =
        (-blockPolyBar e).charpolyRev.map (toEven n).toRingHom := (charpolyRev_map' _ _).symm
    rw [e1, e2, ← Polynomial.map_mul] at h2
    have h3 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f k) h2
    simp only [Polynomial.coeff_map, Polynomial.coeff_one, if_neg (show k ≠ 0 by omega)] at h3
    exact h3
  rw [chernTop, map_mul, hrel, GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient, map_mul, hzero, zero_mul]
  simp

end GlobalTheory.PointChernRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZeroStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_grassmannRelation_origin_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  first | exact @GlobalTheory.PointChernRel.relation_top_zero | exact GlobalTheory.PointChernRel.relation_top_zero | (intros; apply GlobalTheory.PointChernRel.relation_top_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernDensityLieGramRelation
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.HodgeRelation

theorem chernTop_lieGram_rel_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk
  obtain ⟨-, hXd⟩ := GlobalTheory.T.flagComponent_dim_and_base_dim E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have hcard : Fintype.card (Fin X.dim) = Fintype.card (GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) := by
    simp [hXd, Fintype.card_prod]
  let ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q := Fintype.equivOfCardEq hcard
  obtain ⟨φ, g, cc, hcc, hφ, hg, hgu, hdom, hev⟩ :=
    GlobalTheory.T.hodgeGram_localModel_algebraicChart_holomorphic E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA ix
  set v := c'.e y
  set M : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => modelGram H Dw (coordOf ix u) with hM
  have hsm := GlobalTheory.T.boundedDomainModelGram_contDiff_isUnit E H Dw ix (φ v) hdom
  have hφr : ContDiffAt ℝ 2 φ v := (hφ.contDiffAt (n := 2)).restrict_scalars ℝ
  have hK2 : ∀ τ, MContDiffAt 2 (fun w => M (φ w) τ) v := fun τ a b => ((hsm τ).1 a b).comp v hφr
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.chernPolyTopDensity_boundedDomainModel_eq_mul_origin E H Dw ix (φ v) hdom
  change chernTop (relPoly τ k' * Q) _ v = 0
  rw [GlobalTheory.T.topChernDensity_invariant_holomorphic_frameChange _ _ (fun w => M (φ w)) g cc v hcc hg hgu hK2 (fun τ => (hsm τ).2) hev,
    GlobalTheory.T.chernPolyTopDensity_comp_holomorphic_normSq_det _ M φ v hφ (fun τ => (hsm τ).1) (fun τ => (hsm τ).2), hκ, GlobalTheory.T.chernPolyTopDensity_grassmannRelation_origin_zero E H Dw ix τ k' hk Q,
    mul_zero, mul_zero]

end GlobalTheory.HodgeRelation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernDensityLieGramRelationStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_chernDensity_lieGram_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  first | exact @GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul | exact GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul | (intros; apply GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrank
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.CMTypeCard

theorem card_psi_eq_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H
  let e : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H :=
    { toFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have h1 : Fintype.card (E →+* ℂ) =
      Fintype.card (GlobalTheory.AllWt.Psi H) + Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm
  have h2 : Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} = Fintype.card (GlobalTheory.AllWt.Psi H) :=
    Fintype.card_congr e
  rw [← NumberField.Embeddings.card E ℂ, h1, h2]
  omega

end GlobalTheory.CMTypeCard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrankStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  first | exact @GlobalTheory.CMTypeCard.card_psi_eq_half | exact GlobalTheory.CMTypeCard.card_psi_eq_half | (intros; apply GlobalTheory.CMTypeCard.card_psi_eq_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityUnitAndAboveRank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityUnitAndAboveRank
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.GoodMetric

open Polynomial in
theorem chernPoly_zero' {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : chernPoly G v 0 = 1 := by
  rw [chernPoly, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

open Polynomial in
theorem chernPoly_above {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) (hk : Fintype.card r < k) : chernPoly G v k = 0 := by
  rw [chernPoly]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [← Matrix.reverse_charpoly]
  calc _ ≤ (Matrix.charpoly (-curvPoly G v)).natDegree := Polynomial.reverse_natDegree_le _
    _ = Fintype.card r := Matrix.charpoly_natDegree_eq_dim _
    _ < k := hk

theorem chernTop_unit : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  intro n ι m G v τ Q
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [chernTop, map_mul, map_sub, map_one, MvPolynomial.aeval_X, chernPoly_zero', sub_self, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]
  · have h := chernPoly_above (fun u => G u τ) v k (by simpa using hk)
    simp only [chernTop, map_mul, MvPolynomial.aeval_X, h, zero_mul,
      topCoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero, Finset.sum_const_zero, Complex.zero_re]

end GlobalTheory.GoodMetric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityUnitAndAboveRankStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (τ : ι) (Q : MvPolynomial (ι × ℕ) ℝ), chernTop ((MvPolynomial.X (τ, 0) - 1) * Q) G v = 0 ∧ ∀ k : ℕ, m τ < k → chernTop (MvPolynomial.X (τ, k) * Q) G v = 0 := by
  first | exact @GlobalTheory.GoodMetric.chernTop_unit | exact GlobalTheory.GoodMetric.chernTop_unit | (intros; apply GlobalTheory.GoodMetric.chernTop_unit <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.PointHodge

theorem chernTop_add {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (P Q : MvPolynomial (ι × ℕ) ℝ) : chernTop (P + Q) G v = chernTop P G v + chernTop Q G v := by
  simp only [chernTop, map_add (f := _), topCoeff, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem chernTop_smul {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (r : ℝ) (P : MvPolynomial (ι × ℕ) ℝ) : chernTop (r • P) G v = r * chernTop P G v := by
  have h : ∀ Q : MvPolynomial (Fin n × Fin n) ℂ, topCoeff (r • Q) = (r : ℂ) * topCoeff Q := fun Q => by
    simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  simp only [chernTop, map_smul, h, Complex.re_ofReal_mul]
  ring

noncomputable def chernLin {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : MvPolynomial (ι × ℕ) ℝ →ₗ[ℝ] ℝ where
  toFun P := chernTop P G v
  map_add' P Q := chernTop_add G v P Q
  map_smul' r P := chernTop_smul G v r P

theorem pointwise_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), chernTop R (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL la R hR y hy c' hyc A hA
  have hD : (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
    rw [Φ.dim_eq k, GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank E H]
  exact GlobalTheory.T.compactDual_linearForm_flagDegree_pointClass E H Dw la R X.dim (Φ.C k).Y.dim (chernLin (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y)) hD hR
    (fun Q d hQ hd => GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim _ _ _ _ _ Q d hQ hd) (fun τ Q => (GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank _ _ _ _ _ τ Q).1) (fun τ k Q hk => (GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank _ _ _ _ _ τ Q).2 k hk)
    (fun τ k' Q hk => GlobalTheory.T.hodgeMetric_chernDensity_lieGram_relation E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk)

end GlobalTheory.PointHodge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegree
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_covol_flagDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) R (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL la R hR
  have h3 := GlobalTheory.LieBase.hasChernIntegral_pointPoly_covol E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have h := GlobalTheory.GoodMetric.hasChernIntegral_of_eq_mul Eb (openPart j) (lieGram e U hj f₀ A₀) R (pointPoly H Dw) _
    (GlobalTheory.TrueCx.covol (U.X k))
    (fun y hy c' hc A hA => GlobalTheory.PointHodge.pointwise_hodge E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
      la R hR y hy c' hc A hA) h3
  rw [mul_comm] at h
  convert h using 3

end GlobalTheory.LieBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegreeStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_chernIntegral_eq_covolume_mul_flagDegree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) R (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  first | exact @GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg | exact GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg | (intros; apply GlobalTheory.LieBase.hasChernIntegral_covol_flagDeg <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_goodBase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp),
      ∃ (X : Var F) (Eb : Fr (ratOf X) Dw.mult 0) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult)
        (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn) (f : (Φ.C k).Y.X ⟶ X.X) (Ob : X.X.Opens)
        (Hm : Mat Dw.mult X.Fn → GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → Mat Dw.mult ℂ),
        Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) ∧ IsMetricOn Eb Ob Hm ∧
          IsGood Eb Ob Hm ∧
          ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ),
            antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^
                (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult →
              HasChernIntegral Eb Ob Hm R
                (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, hB, hR, hG⟩ := GlobalTheory.LieBase.exists_base_of_flagCpt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  refine ⟨X, Eb, E', φ, f, openPart j, lieGram e U hj f₀ A₀, hR, hG,
    GlobalTheory.LieBase.isMetricOn_lieGram E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    GlobalTheory.T.hodgeMetric_lieGram_isGood_mumford E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hB,
    fun la R h => ?_⟩
  convert GlobalTheory.T.hodgeMetric_chernIntegral_eq_covolume_mul_flagDegree E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hB la R h using 3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfInterLwInterPoly
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Member

theorem selfInter_Lw_interPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}
    (C : FlagCpt Z e) (la : GlobalTheory.AllWt.Weight Dw),
    ((C.Y.inter (fun _ => C.Lw la) : ℤ) : ℝ) =
      C.Y.interPoly (fun x : Root Dw.mult => C.gr x.1 x.2)
        ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ C.Y.dim) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C la
  rw [← Fin.prod_const]
  have h := C.Y.interPoly_prod_sum (fun x : Root Dw.mult => C.gr x.1 x.2)
    (fun _ x => -(GlobalTheory.AllWt.exOf Dw la 0 (some x)))
  push_cast at h
  rw [h]
  congr 2
  funext i
  simp [FlagCpt.Lw, FlagCpt.LEx, Finset.sum_neg_distrib]

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.Proportionality

theorem hasChernIntegral_unique {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}
    {E : Fr (ratOf X) m 0} {O : X.X.Opens} {H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ} {R : MvPolynomial (ι × ℕ) ℝ}
    {t t' : ℝ} (h : HasChernIntegral E O H R t) (h' : HasChernIntegral E O H R t') : t = t' :=
  h.2.symm.trans h'.2

theorem mumfordProportionality_of_goodChernWeil (h : GlobalTheory.Published.GoodChernWeil) : GlobalTheory.Published.MumfordProportionality := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k la
  obtain ⟨X, Eb, E', φ, f, Ob, Hm, hf, hg, hH, hG, hint⟩ := GlobalTheory.LieBase.exists_goodBase E H Dw l Xo c O β Y T F e σ U hσ hU Φ k
  obtain ⟨R, hR⟩ := GlobalTheory.AntisymmChern.antisymm_eq_chernRoots_mul_rootDiscr _ Dw.mult
    ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim)
  rw [GlobalTheory.Member.selfInter_Lw_interPoly (Φ.C k) la]
  have key := hasChernIntegral_unique (h.flag hf hg hH hG hR) (hint la R hR)
  convert key using 3 <;> exact Subsingleton.elim _ _

end GlobalTheory.Proportionality
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil : GlobalTheory.Published.GoodChernWeil → GlobalTheory.Published.MumfordProportionality := by
  first | exact @GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil | exact GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil | (intros; apply GlobalTheory.Proportionality.mumfordProportionality_of_goodChernWeil <;> assumption)
end
