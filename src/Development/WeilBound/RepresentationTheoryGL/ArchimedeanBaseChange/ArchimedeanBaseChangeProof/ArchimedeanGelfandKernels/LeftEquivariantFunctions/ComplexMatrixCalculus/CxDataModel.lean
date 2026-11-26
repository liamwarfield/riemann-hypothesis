module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.HasDerivAtConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.SwapLawsOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.RmAnti

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.SumKronLeft
noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.Cxh

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

def cjC (lam : Fin n → ℤ) : Matrix (Ix n lam) (Ix n lam) ℂ →L[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  LinearMap.toContinuousLinearMap ((cjL lam).restrictScalars ℝ)

theorem fderiv_lefFr (hd : DifferentiableAt ℝ (fr0 lam) (1 : Mat n)) (X : Mat n) :
    fderiv ℝ (lefFr n lam) 1 X = cjL lam (fderiv ℝ (fr0 lam) 1 X) := by
  have h : lefFr n lam = (cjC lam) ∘ fr0 lam := rfl
  have h2 := ((cjC lam).hasFDerivAt.comp (1 : Mat n) hd.hasFDerivAt).fderiv
  rw [h]
  exact congrFun (congrArg DFunLike.coe h2) X

theorem sum_kron_left {ι κ μ : Type*} [Fintype κ] [Fintype μ] (s : Finset ι) (A : ι → Matrix κ κ ℂ)
    (B : Matrix μ μ ℂ) : (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext a b
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

theorem kron_neg' {κ μ : Type*} (A : Matrix κ κ ℂ) (B : Matrix μ μ ℂ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext a b; simp [kroneckerMap_apply]

theorem zero_kron {κ μ : Type*} (B : Matrix μ μ ℂ) : (0 : Matrix κ κ ℂ) ⊗ₖ B = 0 := by
  ext a b; simp [kroneckerMap_apply]

theorem hb_eq (p : Fin n × Fin n) : hb p = hbM (finProdFinEquiv p) := by
  simp [hbM]

end PositivityTheory.RgBcC.Cxh

namespace PositivityTheory.RgBcC

open Cxh
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option maxHeartbeats 800000 in
theorem tdOf : TDOf := by
  intro hAvg hOr hSw hFr hWd n lam
  obtain ⟨hu, -, -, -, -⟩ := hAvg n lam
  obtain ⟨-, -, -, hsw, -⟩ := hSw n lam
  obtain ⟨hd, hfr⟩ := hFr n lam
  have hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B) := by
    intro A B
    have hc : clm lam (A * B) = clm lam A * clm lam B := map_mul Matrix.toEuclideanCLM A B
    have hi : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
    change sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) =
      sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))
    rw [hc]
    simp only [mul_assoc]
    rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]
  have hherm : ∀ p : Fin n × Fin n, (hb p).IsHermitian := fun p => by
    rw [hb_eq]
    exact (hOr n).2 _
  let C : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ := fun p => creL n (cf n (hb p))
  let G : Fin n × Fin n → Matrix (Finset (Md n)) (Finset (Md n)) ℂ := fun p =>
    fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p)
  let R : Fin n × Fin n → Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ := fun p =>
    fderiv ℝ (rhoW lam) 1 (hb p)
  have hw : ∑ p, C p * G p = 0 := hWd n
  have e1 : ∀ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) =
      cjL lam ((C p * G p) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) + C p ⊗ₖ R p) := by
    intro p
    rw [fderiv_lefFr hd, hfr _ (hherm p)]
    change cjL lam (C p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) *
      cjL lam (G p ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ) +
        (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ R p) = _
    rw [hmul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]
  have hS : ∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p) = cjL lam (∑ p, C p ⊗ₖ R p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl (fun p _ => e1 p), ← map_sum, Finset.sum_add_distrib, ← sum_kron_left, hw,
      zero_kron, zero_add]
  rw [hS]
  change cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) * _ =
    -(_ * cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam))
  rw [hmul, hmul, ← map_neg]
  refine congrArg (cjL lam) ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    show swapJ lam * R p = -(R p * swapJ lam) from hsw _ (hherm p), Matrix.one_mul, Matrix.mul_one, kron_neg']
end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.FrameInvMulSymZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnChartInv
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

namespace GlobalTheory.CompanionTheory.MatInv

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chart (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiffOn_chartInv (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chart n).symm (Ring.inverse (chart n M)))
      {M | IsUnit (chart n M)} := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (GlobalTheory.CompanionTheory.MatInv.chart n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact ((GlobalTheory.CompanionTheory.MatInv.chart n).symm.contDiff.contDiffAt.comp M
    (h1.comp M (GlobalTheory.CompanionTheory.MatInv.chart n).contDiff.contDiffAt)).contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiffOn_inv : ∀ {n : ℕ}, ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  intro n
  let A : PositivityTheory.RgTw.Mat n →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  let B : (Fin n → Fin n → ℂ) →ₗ[ℝ] PositivityTheory.RgTw.Mat n :=
    (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hA : ContDiff ℝ ∞ A := (LinearMap.toContinuousLinearMap A).contDiff
  have hB : ContDiff ℝ ∞ B := (LinearMap.toContinuousLinearMap B).contDiff
  have key : (fun x : PositivityTheory.RgTw.Mat n => x⁻¹) =
      fun x => B ((GlobalTheory.CompanionTheory.MatInv.chart n).symm (Ring.inverse (GlobalTheory.CompanionTheory.MatInv.chart n (A x)))) := by
    funext x
    rw [Matrix.nonsing_inv_eq_ringInverse]
    rfl
  rw [key]
  refine hB.comp_contDiffOn ((GlobalTheory.CompanionTheory.MatInv.contDiffOn_chartInv n).comp hA.contDiffOn ?_)
  intro x hx
  change IsUnit (x : Matrix (Fin n) (Fin n) ℂ)
  exact (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)

end GlobalTheory.CompanionTheory.MatInv
end
end

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.Cxh

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem frame_inv_mul_sym_zero (hu : IsUnit (sqQ lam)) (hG : GamMul) (x : Mat n) :
    lefFr n lam x⁻¹ * lefS n lam 0 =
      cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ rhoW lam x⁻¹) := by
  have hmul : ∀ A B : Matrix (Ix n lam) (Ix n lam) ℂ, cjL lam A * cjL lam B = cjL lam (A * B) := by
    intro A B
    have hc : clm lam (A * B) = clm lam A * clm lam B := map_mul Matrix.toEuclideanCLM A B
    have hi : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
    change sqQ lam * (clm lam A * Ring.inverse (sqQ lam)) * (sqQ lam * (clm lam B * Ring.inverse (sqQ lam))) =
      sqQ lam * (clm lam (A * B) * Ring.inverse (sqQ lam))
    rw [hc]
    simp only [mul_assoc]
    rw [← mul_assoc (Ring.inverse (sqQ lam)) (sqQ lam), hi, one_mul]
  have h0 : lefS n lam 0 = cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := by
    simp only [lefS, Complex.ofReal_zero, zero_smul]
  rw [h0, lefFr, fr0, hmul, ← Matrix.mul_kronecker_mul, ← (hG n).2, mul_zero, Matrix.mul_one]

theorem clm_entry (M : Matrix (Ix n lam) (Ix n lam) ℂ) (u : EV n lam) (r : Ix n lam) :
    (clm lam M u) r = ∑ c, M r c * u c := by
  have h : (clm lam M u).ofLp = M *ᵥ u.ofLp := by
    rw [clm, ← ContinuousLinearMap.coe_coe, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rfl
  change (clm lam M u).ofLp r = _
  rw [h]
  rfl

theorem clm_apply' (M : Matrix (Ix n lam) (Ix n lam) ℂ) (u : EV n lam) :
    clm lam M u = ∑ i : Ix n lam × Ix n lam, (M i.1 i.2 * u i.2) • EuclideanSpace.single i.1 (1 : ℂ) := by
  rw [Fintype.sum_prod_type (f := fun i : Ix n lam × Ix n lam => (M i.1 i.2 * u i.2) • EuclideanSpace.single i.1 (1 : ℂ))]
  ext r
  rw [clm_entry]
  simp [Finset.sum_apply, Pi.single_apply]

theorem mem_GLs_inv' {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq] at hx ⊢
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hx

theorem mem_GLs_conjInv {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹)ᴴ ∈ GLs n := by
  have h := mem_GLs_inv' hx
  simp only [GLs, Set.mem_ofPred_eq] at h ⊢
  rw [Matrix.det_conjTranspose]
  exact star_ne_zero.2 h

theorem contDiff_conjT : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ (fun _ => ℂ) i).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) j))

theorem contDiffOn_theta : ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹)ᴴ) (GLs n) :=
  contDiff_conjT.comp_contDiffOn GlobalTheory.CompanionTheory.MatInv.contDiffOn_inv

theorem contDiffOn_entry {J : Type} [Fintype J] [DecidableEq J] {f : Mat n → Matrix J J ℂ} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (a b : J) : ContDiffOn ℝ ∞ (fun x => (f x * (1 : Matrix J J ℂ) : Matrix J J ℂ) a b) (GLs n) := by
  simp only [Matrix.mul_one]
  exact ((contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (J → ℂ)) a)).comp_contDiffOn hf

end PositivityTheory.RgBcC.Cxh

namespace PositivityTheory.RgBcC

open Cxh
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option maxHeartbeats 800000 in
theorem eigOf : EigOf := by
  intro hAvg hG hRm hHol hAnti hProd hLoc n lam hlam w
  obtain ⟨hu, -, -, -, -⟩ := hAvg n lam
  obtain ⟨hR1, hRmul, hRc⟩ := hRm n lam
  let G0 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ := gamM (0 : Matrix (Md n) (Md n) ℂ)
  let hh : Ix n lam × Ix n lam → Mat n → ℂ := fun i x =>
    (Rm lam x * 1 : Matrix (Jd n lam) (Jd n lam) ℂ) i.2.2.1 i.1.2.1
  let aa : Ix n lam × Ix n lam → Mat n → ℂ := fun i x =>
    (Rm lam x⁻¹ᴴ * 1 : Matrix (Jd n lam) (Jd n lam) ℂ) i.2.2.2 i.1.2.2
  let vv : Ix n lam × Ix n lam → EV n lam := fun i =>
    (G0 i.1.1 i.2.1 * (Ring.inverse (sqQ lam) w) i.2) • sqQ lam (EuclideanSpace.single i.1 (1 : ℂ))
  have hE := hProd n (infOf lam) (Ix n lam × Ix n lam) (EV n lam) hh aa vv
    (fun i => contDiffOn_entry (f := Rm lam) hRc _ _)
    (fun i => contDiffOn_entry (f := fun x => Rm lam x⁻¹ᴴ)
      (hRc.comp contDiffOn_theta (fun x hx => mem_GLs_conjInv hx)) _ _)
    (fun i g hg => hHol n lam hlam 1 _ _ g hg)
    (fun i g hg => hAnti n lam hlam 1 _ _ g hg)
  refine hLoc n (infOf lam) (EV n lam) _ _ ?_ hE
  intro x hx
  have hdx : IsUnit (det x) := isUnit_iff_ne_zero.2 hx
  have hdx' : IsUnit (det x⁻¹) := isUnit_iff_ne_zero.2 (mem_GLs_inv' hx)
  have hinv : (Rm lam x⁻¹)⁻¹ = Rm lam x := by
    apply Matrix.inv_eq_left_inv
    rw [← hRmul x x⁻¹ hdx hdx', Matrix.mul_nonsing_inv x hdx, hR1]
  symm
  rw [← ContinuousLinearMap.mul_apply, frame_inv_mul_sym_zero hu hG]
  change (sqQ lam * (clm lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ rhoW lam x⁻¹) * Ring.inverse (sqQ lam))) w = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, clm_apply', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  simp only [vv, smul_smul]
  congr 1
  simp only [hh, aa, G0, rhoW, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_one, hinv]
  ring
end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.DifferentiableMt
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.EpowCongr
noncomputable section

open Matrix

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem rd_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (X : Mat n) :
    ∀ x ∈ U, Rd X f x = Rd X f' x := by
  intro x hx
  unfold Rd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h)]

theorem eu_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (a b : Fin n) :
    ∀ x ∈ U, Eu s a b f x = Eu s a b f' x := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [rd_congr hU h (single a b 1) x hx, rd_congr hU h (single a b Complex.I) x hx]

theorem epow_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) :
    ∀ (m : ℕ) (a b : Fin n), ∀ x ∈ U, Epow s m a b f x = Epow s m a b f' x := by
  intro m
  induction m with
  | zero =>
    intro a b x hx
    simp only [Epow.eq_1]
    by_cases hab : a = b <;> simp [hab, h x hx]
  | succ m ih =>
    intro a b x hx
    simp only [Epow.eq_2]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr hU (fun y hy => ih c b y hy) s a c x hx

theorem gel_congr {U : Set (Mat n)} (hU : IsOpen U) {f f' : Mat n → V} (h : ∀ x ∈ U, f x = f' x) (s : Bool) (m : ℕ) :
    ∀ x ∈ U, gel s m f x = gel s m f' x := by
  intro x hx
  simp only [gel]
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr hU h s m a a x hx

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf in
theorem eigLocal : EigLocal := by
  intro n χ V _ _ f f' h hf s m g hg
  rw [← h g hg, ← gel_congr isOpen_GLs h s m g hg]
  exact hf s m g hg

end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.DifferentiableAdjugate
noncomputable section

open Matrix
open scoped Kronecker

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι]

theorem dEntry {F : E → Matrix κ μ ℂ} (h : DifferentiableAt ℝ F x) (i : κ) (j : μ) :
    DifferentiableAt ℝ (fun y => F y i j) x :=
  differentiableAt_pi.1 (differentiableAt_pi.1 h i) j

theorem dMat {F : E → Matrix κ μ ℂ} (h : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x) : DifferentiableAt ℝ F x :=
  differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => h i j

theorem dMul {F : E → Matrix κ ι ℂ} {H : E → Matrix ι μ ℂ} (hF : DifferentiableAt ℝ F x) (hH : DifferentiableAt ℝ H x) :
    DifferentiableAt ℝ (fun y => F y * H y) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun k _ => (dEntry hF i k).mul (dEntry hH k j)

theorem dConjT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᴴ) x := by
  refine dMat fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact (dEntry hF j i).star

theorem dT {F : E → Matrix κ μ ℂ} (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => (F y)ᵀ) x := dMat fun i j => dEntry hF j i

theorem dConst (A : Matrix κ μ ℂ) : DifferentiableAt ℝ (fun _ : E => A) x := differentiableAt_const A

theorem differentiable_det : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.det) := by
  intro A0
  simp only [Matrix.det_apply, Units.smul_def]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_smul ?_ _
  exact (HasFDerivAt.finsetProd fun i _ =>
    (dEntry (differentiableAt_id (x := A0)) (σ i) i).hasFDerivAt).differentiableAt

theorem differentiable_adjugate : Differentiable ℝ (fun A : Matrix ι ι ℂ => A.adjugate) := by
  intro A0
  refine dMat fun i j => ?_
  simp only [Matrix.adjugate_apply]
  have hu : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A.updateRow j (Pi.single i 1)) A0 := by
    refine dMat fun k l => ?_
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hk]
      exact dEntry differentiableAt_id k l
  exact (differentiable_det _).comp A0 hu

theorem differentiableAt_inv (A0 : Matrix ι ι ℂ) (h : A0.det ≠ 0) : DifferentiableAt ℝ (fun A : Matrix ι ι ℂ => A⁻¹) A0 := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((differentiable_det A0).inv h).smul (differentiable_adjugate A0)

end PositivityTheory.RgBcC.Cxf
end
end

noncomputable section

open Matrix
open scoped Kronecker

namespace PositivityTheory.RgBcC.Cxf

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {κ μ : Type} [Fintype κ] [Fintype μ]

def kronLin (κ μ : Type) [Fintype κ] [Fintype μ] :
    Matrix κ κ ℂ →ₗ[ℝ] Matrix μ μ ℂ →ₗ[ℝ] Matrix (κ × μ) (κ × μ) ℂ :=
  LinearMap.mk₂ ℝ (fun A B => A ⊗ₖ B) (fun A A' B => Matrix.add_kronecker A A' B)
    (fun c A B => by rw [Matrix.smul_kronecker]) (fun A B B' => Matrix.kronecker_add A B B')
    (fun c A B => by rw [Matrix.kronecker_smul])

def kronC (κ μ : Type) [Fintype κ] [Fintype μ] :
    Matrix κ κ ℂ →L[ℝ] Matrix μ μ ℂ →L[ℝ] Matrix (κ × μ) (κ × μ) ℂ :=
  LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (Matrix μ μ ℂ →ₗ[ℝ] Matrix (κ × μ) (κ × μ) ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ kronLin κ μ)

variable {n : ℕ}

theorem differentiable_Mt : Differentiable ℝ (Mt (n := n)) := by
  intro y
  refine dMat fun p q => ?_
  have hM : DifferentiableAt ℝ (fun z : Mat n => z * hbM q * zᴴ * hbM p) y :=
    dMul (dMul (dMul differentiableAt_id (dConst _)) (dConjT differentiableAt_id)) (dConst _)
  have ht : DifferentiableAt ℝ (fun z : Mat n => (z * hbM q * zᴴ * hbM p).trace) y := by
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun i _ => dEntry hM i i
  exact (Complex.ofRealCLM.comp Complex.reCLM).differentiableAt.comp y ht

end PositivityTheory.RgBcC.Cxf

namespace PositivityTheory.RgBcC

open Cxf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fr0Der_of (hG : GamDer) (hGm : GamMul) (hM : MtLaws) (hR : RmLaws) : MatrixFrechetDerivativeAtZero := by
  intro n lam
  have hdet1 : (1 : PositivityTheory.RgTw.Mat n).det ≠ 0 := by simp
  have hopen : IsOpen (GLs n) :=
    isOpen_ne_fun (differentiable_det (ι := Fin n)).continuous continuous_const
  have hRm : ∀ y : PositivityTheory.RgTw.Mat n, y.det ≠ 0 → DifferentiableAt ℝ (Rm lam) y := fun y hy =>
    ((hR n lam).2.2.contDiffAt (hopen.mem_nhds (show y ∈ GLs n from hy))).differentiableAt (by simp)
  have hdetR : (Rm lam (1 : PositivityTheory.RgTw.Mat n)).det ≠ 0 := by rw [(hR n lam).1]; simp
  have hgam : ∀ B : Matrix (Md n) (Md n) ℂ, DifferentiableAt ℝ (gamM (n := n)) B := fun B =>
    (((hG n).1.differentiable (by simp)) B).restrictScalars ℝ
  have hFd : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => gamM (Mt x⁻¹)ᵀ) 1 :=
    (hgam _).comp (1 : PositivityTheory.RgTw.Mat n)
      (dT ((differentiable_Mt _).comp (1 : PositivityTheory.RgTw.Mat n) (differentiableAt_inv 1 hdet1)))
  have hA : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => (Rm lam x)⁻¹ᵀ) 1 :=
    dT ((differentiableAt_inv _ hdetR).comp (1 : PositivityTheory.RgTw.Mat n) (hRm 1 hdet1))
  have hB : DifferentiableAt ℝ (fun x : PositivityTheory.RgTw.Mat n => (Rm lam xᴴ)ᵀ) 1 :=
    dT ((hRm _ (by simp)).comp (1 : PositivityTheory.RgTw.Mat n) (dConjT differentiableAt_id))
  have hGd : DifferentiableAt ℝ (rhoW lam) 1 := by
    have h := ((kronC _ _).hasFDerivAt_of_bilinear hA.hasFDerivAt hB.hasFDerivAt).differentiableAt
    exact h
  have key : fr0 lam = fun x => kronC _ _ (gamM (Mt x⁻¹)ᵀ) (rhoW lam x) := rfl
  have hF1 : gamM (Mt (1 : PositivityTheory.RgTw.Mat n)⁻¹)ᵀ = 1 := by
    rw [inv_one, (hM n).1, transpose_one, (hGm n).1]
  have hG1 : rhoW lam (1 : PositivityTheory.RgTw.Mat n) = 1 := by
    simp only [rhoW, conjTranspose_one, (hR n lam).1, inv_one, transpose_one]
    exact Matrix.one_kronecker_one
  refine ⟨?_, fun X _ => ?_⟩
  · rw [key]
    exact ((kronC _ _).hasFDerivAt_of_bilinear hFd.hasFDerivAt hGd.hasFDerivAt).differentiableAt
  · have h := congrArg (fun L => L X) ((kronC _ _).fderiv_of_bilinear hFd hGd)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, hF1, hG1] at h
    rw [key]
    refine h.trans ?_
    rw [add_comm]
    rfl

end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Fr0Laws
namespace PositivityTheory.RgBcC

theorem fr0Laws : MatrixFrechetDerivativeAtZeroLaws := fr0Laws_of rmLaws gamMul mtLaws gamDer

theorem avg : Avg := avg_of fr0Laws

theorem frOne : FrOne := frOne' fr0Laws avg
theorem frMulK : FrMulK := frMulK' fr0Laws avg
theorem frIso : FrIso := frIso' fr0Laws avg
theorem frCont : FrCont := frCont' fr0Laws avg

end PositivityTheory.RgBcC
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataOf
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.LefRho
noncomputable section

namespace PositivityTheory.RgBcC

def lefRho (n : ℕ) (lam : Fin n → ℤ) : Matrix.unitaryGroup (Fin n) ℂ →* (EV n lam →L[ℂ] EV n lam) where
  toFun k := lefFr n lam k.1
  map_one' := frOne n lam
  map_mul' k k' := frMulK n lam k k'

def lefE (n : ℕ) (lam : Fin n → ℤ) : KMod n where
  V := EV n lam
  ρ := lefRho n lam
  iso := frIso n lam
  cont := frCont n lam

end PositivityTheory.RgBcC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KronConjTranspose
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.TraceGammaZeroEqOne
noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem trace_clm (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    LinearMap.trace ℂ (EV n lam) ((clm lam A : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = A.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Ix n lam) ℂ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, clm, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem trace_cj (hu : IsUnit (sqQ lam)) (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    LinearMap.trace ℂ (EV n lam) ((cjL lam A : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = A.trace := by
  rw [cjL_apply, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, LinearMap.trace_mul_comm, ← mul_assoc,
    ← ContinuousLinearMap.coe_mul, ← ContinuousLinearMap.coe_mul, Ring.inverse_mul_cancel _ hu, one_mul, trace_clm]

theorem weylChar_conj (u : Fin n → ℂ) : weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀, map_pow]

theorem trace_gamma_zero_eq_one (hScal : GamScal) : (gamM (0 : Matrix (Md n) (Md n) ℂ)).trace = 1 := by
  have e : (0 : Matrix (Md n) (Md n) ℂ) = (0 : ℂ) • 1 := by rw [zero_smul]
  rw [e, hScal n 0, trace_diagonal, Finset.sum_eq_single (∅ : Finset (Md n))]
  · simp
  · intro A _ hA
    exact zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hA))
  · simp

theorem diag_unit_prod (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z)ᴴ * (diagonal z)⁻¹ = diagonal (fun a => conj (z a ^ 2)) ∧ IsUnit (diagonal z).det ∧
      IsUnit ((diagonal z)ᴴ).det ∧ IsUnit ((diagonal z)⁻¹).det := by
  have hc : ∀ a, z a * conj (z a) = 1 := fun a => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]; simp
  have hinv : (diagonal z)⁻¹ = diagonal fun a => conj (z a) :=
    Matrix.inv_eq_right_inv (by rw [diagonal_mul_diagonal]; simp [hc])
  have hne : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hinv, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1; ext a; simp [pow_two, map_mul]
  · rw [det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hne a)
  · rw [diagonal_conjTranspose, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using hne a)
  · rw [hinv, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using hne a)

theorem char_f (hu : IsUnit (sqQ lam)) (hG : GamMul) (hScal : GamScal) (hS : SwapLaws) (hRL : RmLaws) (hRC : RmChar)
    (hlam : Antitone lam) (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) (hinj : Function.Injective fun a => z a ^ 2) :
    LinearMap.trace ℂ (EV n lam) ((lefS n lam 0 * lefFr n lam (diagonal z) * lefT n lam : EV n lam →L[ℂ] EV n lam) :
      EV n lam →ₗ[ℂ] EV n lam) = conj (weylChar lam fun a => z a ^ 2) := by
  obtain ⟨hprod, hd, hdH, hdi⟩ := diag_unit_prod z hz
  rw [lefS_zero, lefFr_apply, lefT_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, zero_mul, mul_one, one_mul, trace_cj hu, trace_kronecker, trace_gamma_zero_eq_one hScal, one_mul,
    rhoW, (hS n lam).2.2.2.2, ← transpose_mul, trace_transpose]
  have hR := hRL n lam
  have hinvR : (Rm lam (diagonal z))⁻¹ = Rm lam (diagonal z)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hR.2.1 _ _ hd hdi, Matrix.mul_nonsing_inv _ hd, hR.1]
  rw [hinvR, ← hR.2.1 _ _ hdH hdi, hprod]
  have ht : ∀ a, (fun a => conj (z a ^ 2)) a ≠ 0 := fun a h => by
    have : z a ≠ 0 := fun h0 => by simpa [h0] using hz a
    simp only [map_eq_zero] at h
    exact this (pow_eq_zero_iff two_ne_zero |>.mp h)
  have hti : Function.Injective fun a => conj (z a ^ 2) := fun a b h => hinj (by
    have h' : conj (z a ^ 2) = conj (z b ^ 2) := h
    exact (RingHom.injective (starRingEnd ℂ)) h')
  rw [hRC n lam hlam _ ht hti, ← weylChar_conj]

end PositivityTheory.RgBcC
end
end

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

theorem kron_conjTranspose' {ι₁ ι₂ : Type*} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) : (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext i j; simp [kroneckerMap_apply, conjTranspose_apply, mul_comm]

theorem U_mem (hS : SwapLaws) :
    ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) ∈ Matrix.unitaryGroup (Ix n lam) ℂ := by
  have h := (hS n lam).2.1
  rw [Matrix.mem_unitaryGroup_iff] at h ⊢
  rw [Matrix.star_eq_conjTranspose, kron_conjTranspose', conjTranspose_one, ← mul_kronecker_mul, mul_one,
    ← Matrix.star_eq_conjTranspose, h, one_kronecker_one]

theorem Tiso_f (hu : IsUnit (sqQ lam)) (hA : Avg) (hS : SwapLaws) (v : EV n lam) : ‖lefT n lam v‖ = ‖v‖ := by
  set U := (1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam
  have hU := U_mem (lam := lam) hS
  have hc : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U := by
    intro k
    rw [frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one, swap_rhoW_k hu hS k]
  have hcomm := (hA n lam).2.2.2.2 U hU hc
  have e : lefT n lam = clm lam U := by
    rw [lefT_apply, cjL_apply, ← hcomm, mul_assoc, Ring.mul_inverse_cancel _ hu, mul_one]
  rw [e]
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  rw [Unitary.mem_iff]
  have hs : star (clm lam U) = clm lam (star U) := (map_star _ U).symm
  rw [hs, ← clm_mul', ← clm_mul', Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, clm_one']
  exact ⟨rfl, rfl⟩

theorem smooth_f (hF : MatrixFrechetDerivativeAtZeroLaws) : ContDiffOn ℝ ∞ (lefFr n lam) (GLs n) := by
  have h := ((cjL lam).restrictScalars ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn (hF n lam).2.2
  exact h

theorem one_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) : lefFr n lam 1 = 1 := by
  rw [lefFr_apply, (hF n lam).1, cj_one hu]

theorem mul_f (hu : IsUnit (sqQ lam)) (hF : MatrixFrechetDerivativeAtZeroLaws) (x : Mat n) (hx : x ∈ GLs n) (y : Mat n) (hy : y ∈ GLs n) :
    lefFr n lam (x * y) = lefFr n lam x * lefFr n lam y := by
  rw [lefFr_apply, lefFr_apply, lefFr_apply, cj_mul hu,
    (hF n lam).2.1 x y (isUnit_iff_ne_zero.mpr hx) (isUnit_iff_ne_zero.mpr hy)]

theorem lefS_diag (hScal : GamScal) (s : ℝ) : lefS n lam s =
    cjL lam (krL n lam (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card)) := by
  rw [lefS_apply, hScal n]; rfl

theorem Ssmooth_f (hScal : GamScal) : ContDiff ℝ ∞ (lefS n lam) := by
  have e : lefS n lam = fun s : ℝ => (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
      (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  rw [e]
  refine ContinuousLinearMap.contDiff _ |>.comp ?_
  refine contDiff_pi.2 fun A => contDiff_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]; exact (Complex.ofRealCLM.contDiff).pow _
  · simp only [diagonal_apply_ne _ h]; exact contDiff_const

theorem hasDerivAt_diagPow (s : ℝ) : HasDerivAt (fun s : ℝ => (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card))
    (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1)) s := by
  refine hasDerivAt_pi.2 fun A => hasDerivAt_pi.2 fun B => ?_
  by_cases h : A = B
  · subst h; simp only [diagonal_apply_eq]
    exact (hasDerivAt_pow A.card (s : ℂ)).comp_ofReal
  · simp only [diagonal_apply_ne _ h]; exact hasDerivAt_const _ _

theorem Sder_f (hu : IsUnit (sqQ lam)) (hScal : GamScal) (hN : Number) (s : ℝ) :
    deriv (lefS n lam) s = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
  set L := (((cjL lam ∘ₗ krL n lam).restrictScalars ℝ).toContinuousLinearMap)
  have e : lefS n lam = fun s : ℝ => L (Matrix.diagonal fun A : Finset (Md n) => (s : ℂ) ^ A.card) := by
    funext s; rw [lefS_diag hScal]; rfl
  have hd : HasDerivAt (lefS n lam) (L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))) s := by
    rw [e]; exact L.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_diagPow s)
  rw [hd.deriv]
  have hcf : ∀ p : Fin n × Fin n, cf n (hb p) = Pi.single (finProdFinEquiv p) 1 := fun p => by
    have := Cxa.cf_hbM (n := n) (finProdFinEquiv p)
    simpa [hbM] using this
  have key : ∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
      annL n (cf n (hb p)) = Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1) := by
    rw [← hN n (s : ℂ)]
    exact Fintype.sum_equiv finProdFinEquiv _ _ (fun p => by rw [hcf p])
  calc L (Matrix.diagonal fun A : Finset (Md n) => (A.card : ℂ) * (s : ℂ) ^ (A.card - 1))
      = cjL lam (krL n lam (∑ p : Fin n × Fin n, creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [key]; rfl
    _ = ∑ p : Fin n × Fin n, cjL lam (krL n lam (creL n (cf n (hb p)) * gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) *
          annL n (cf n (hb p)))) := by rw [map_sum, map_sum]
    _ = ∑ p, lefε n lam (hb p) * lefS n lam s * lefι n lam (hb p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [lefε_apply, lefι_apply, lefS_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul,
          mul_one, mul_one]
        rfl

end PositivityTheory.RgBcC
end
end

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cxData_of (hCP : CfPair) (hM : MtLaws) (hG : GamMul) (hB : Car) (hC : GamCre) (hScal : GamScal) (hN : Number)
    (hRL : RmLaws) (hRC : RmChar) (hA : Avg) (hF : MatrixFrechetDerivativeAtZeroLaws) (hS : SwapLaws)
    (hTD : ∀ (n : ℕ) (lam : Fin n → ℤ), lefT n lam * (∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) =
      -((∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) * lefT n lam))
    (hEig : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ w : EV n lam,
      IsEig (infOf lam) fun x => lefFr n lam x⁻¹ (lefS n lam 0 w))
    {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hQ : IsUnit (sqQ lam) := (hA n lam).1
  exact
    { smooth := smooth_f hF
      one := one_f hQ hF
      mul := mul_f hQ hF
      onK := fun k => rfl
      car := car_f hQ hB hCP
      frι := frι_f hQ hC hM
      frε := frε_f hQ hC hM
      Γsq := Γsq_f hQ hG
      Γε := Γε_f hQ hG hC
      Γι := Γι_f hQ hG hC
      ΓFr := fun x _ => ΓFr_f hQ hG x
      ΓT := ΓT_f hQ hG
      Tsq := Tsq_f hQ hS
      Tiso := Tiso_f hQ hA hS
      TK := TK_f hQ hS
      Tε := Tε_f hQ hS
      Tι := Tι_f hQ hS
      TD := hTD n lam
      Ssmooth := Ssmooth_f hScal
      S1 := sym_one_eq_one hQ hG
      Sε := Sε_f hQ hG hC
      Sder := Sder_f hQ hScal hN
      SΓ := SΓ_f hQ hG
      S0sq := S0sq_f hQ hG
      S0Γ := S0Γ_f hQ hG
      sym_zero_comm_frame := fun x _ => sym_zero_comm_frame_matrix hQ hG x
      time_comm_sym_zero := time_comm_sym_zero_matrix hQ hG
      S0θ := S0θ_f hQ hS hG
      eig := hEig n lam hlam
      char := char_f hQ hG hScal hS hRL hRC hlam }

end PositivityTheory.RgBcC
end
end

namespace PositivityTheory.RgBcC

theorem cxData_model {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hsw : SwapLaws := swapLaws_of rmLaws
  have hfd : MatrixFrechetDerivativeAtZero := fr0Der_of gamDer gamMul mtLaws rmLaws
  exact cxData_of cfPair mtLaws gamMul car gamCre gamScal number rmLaws rmChar avg fr0Laws hsw
    (tdOf avg hbOrtho hsw hfd (wedgeDer_of gamDer))
    (eigOf avg gamMul rmLaws rmHol rmAnti eigProd eigLocal) lam hlam

theorem cxEx_model : CxEx := fun n lam hlam =>
  ⟨lefE n lam, lefFr n lam, lefε n lam, lefι n lam, lefS n lam, lefΓ n lam, lefT n lam, cxData_model lam hlam⟩

end PositivityTheory.RgBcC
