module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartMixedEnergy {e : ℕ} (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) : ℝ :=
  ∫ y : Fin e → ℂ, (hermChartPot M y - hermChartPot N y) *
    maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y

def ChartEnergy.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k =
      1 / 2 * (Real.log M.det.re - Real.log N.det.re) *
        chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPrimeEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartMassInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartMongeAmpereAffineInvariance

variable {e : ℕ}

theorem mulVec_cons_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (y : Fin e → ℂ) :
    T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) =
      Fin.cons (T 0 0) ((fun i => T i.succ 0) + (T.submatrix Fin.succ Fin.succ) *ᵥ y) := by
  funext p
  refine Fin.cases ?_ (fun i => ?_) p
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, hT]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ]

theorem det_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0) :
    T.det = T 0 0 * (T.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [hT, Fin.succAbove_zero]

theorem hermChartPot_conj (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (ht : T 0 0 ≠ 0) (y : Fin e → ℂ) :
    hermChartPot (Tᴴ * M * T) y =
      hermChartPot M ((T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) +
        Real.log ‖T 0 0‖ := by
  set w : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y with hw
  set u : Fin (e + 1) → ℂ := Fin.cons 1 w with hu
  have hTv : T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) = T 0 0 • u := by
    rw [mulVec_cons_of_row_zero T hT]
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp [u]
    · have hm : (((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) i =
          (T 0 0)⁻¹ * ((T.submatrix Fin.succ Fin.succ) *ᵥ y) i := by
        simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      simp only [u, w, Fin.cons_succ, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hm]
      field_simp
  have hq : star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Tᴴ * M * T) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (Complex.normSq (T 0 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (T 0 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr ht) (Real.sqrt_pos.mpr hx).ne']
  ring

theorem chartMass_conj (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (hdet : T.det ≠ 0) :
    chartMass (Tᴴ * M * T) = chartMass M := by
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set C := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hCdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hC' : C.det ≠ 0 := by
    rw [hCdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfun : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + C *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  unfold chartMass
  rw [hfun]
  simp_rw [maDensity_comp_affine (hermChartPot M) c C hC']
  rw [integral_const_mul, integral_comp_affine (maDensity fun _ => hermChartPot M) c C hC', ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hC').ne', one_mul]

end ChartMongeAmpereAffineInvariance


open ChartMongeAmpereAffineInvariance in
theorem ChartMassInvariant.proof : ChartMassInvariant.Statement := by
  intro e M hM
  let S : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := M
  have hS : S.PosDef := hM
  let P₀ : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := LDL.lowerInv hS
  let P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := P₀
  have hPdet : P.det ≠ 0 := (isUnit_det_of_invertible P₀).ne_zero
  set T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Pᴴ with hTdef
  have hT : ∀ j : Fin e, T 0 j.succ = 0 := fun j => by
    have h := LDL.isLowerTriangular_lowerInv hS (i := OrderDual.toDual j.succ) (j := OrderDual.toDual 0)
      (OrderDual.toDual_lt_toDual.mpr (Fin.succ_pos j))
    rw [hTdef, conjTranspose_apply, show P j.succ 0 = 0 from h, star_zero]
  have hTdet : T.det ≠ 0 := by
    rw [hTdef, det_conjTranspose]
    exact star_ne_zero.mpr hPdet
  let d₀ : (Fin (e + 1))ᵒᵈ → ℂ := LDL.diagEntries hS
  set d : Fin (e + 1) → ℂ := d₀ with hddef
  have hD : Tᴴ * M * T = diagonal d := by
    rw [hTdef, conjTranspose_conjTranspose]
    exact (LDL.diag_eq_lowerInv_conj hS).symm
  have hDpos : (diagonal d).PosDef := by
    rw [← hD]
    exact hM.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hTdet)))
  have hdpos : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  set T' : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := diagonal fun i => ((Real.sqrt (d i).re)⁻¹ : ℝ) with hT'def
  have hT' : ∀ j : Fin e, T' 0 j.succ = 0 := fun j => diagonal_apply_ne _ (Fin.succ_ne_zero j).symm
  have hT'det : T'.det ≠ 0 := by
    rw [hT'def, det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (Complex.pos_iff.mp (hdpos i)).1).ne')
  have h1 : T'ᴴ * diagonal d * T' = 1 := by
    rw [hT'def, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    obtain ⟨hr, him⟩ := Complex.pos_iff.mp (hdpos i)
    set r := (d i).re with hrdef
    have hdi : d i = (r : ℂ) := Complex.ext (by simp [hrdef]) (by simp [← him])
    have key : (Real.sqrt r)⁻¹ * r * (Real.sqrt r)⁻¹ = 1 := by
      have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
      rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hr.le, inv_mul_cancel₀ hr.ne']
    rw [hdi, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast key
  calc chartMass M = chartMass (Tᴴ * M * T) := (chartMass_conj M T hM hT hTdet).symm
    _ = chartMass (diagonal d) := by rw [hD]
    _ = chartMass (T'ᴴ * diagonal d * T') := (chartMass_conj _ T' hDpos hT' hT'det).symm
    _ = chartMass 1 := by rw [h1]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartCutoffEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartCutoff {D : ℕ} (k : ℕ) (y : Fin D → ℂ) : ℝ :=
  Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2)

def ChartCutoffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ), (∀ i, (T i).PosDef) →
    ∃ K : ℝ, ∀ k : ℕ,
      ∫ y : Fin (n + 1) → ℂ,
        ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def LocallyPrincipalCoprime.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : L, x ∈ M ↔ ∃ y ∈ I, (β : L) * x = δ * y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeIsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PGaussLatticeIsLattice

def colBasis {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    Module.Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  (Pi.basisFun ℝ (Fin g)).map
    ((B.toLinearEquiv' (B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hB))).trans
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm)

theorem colBasis_apply {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  rw [colBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

theorem gaussLattice_eq_span {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by
  unfold gaussLattice
  congr 2
  funext i
  exact (colBasis_apply B hB i).symm

end PGaussLatticeIsLattice


open PGaussLatticeIsLattice in
theorem GaussLatticeIsLattice.proof : GaussLatticeIsLattice.Statement := by
  intro g B hB
  have h := gaussLattice_eq_span B hB
  refine ⟨?_, fun {_} => ⟨?_⟩⟩
  · rw [h]; infer_instance
  · rw [h]; exact ZSpan.span_top (colBasis B hB)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaSummandNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace KThetaSummandNorm

lemma im_dot_period {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by
  simp only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp

lemma im_dot_real {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by
  simp [dotProduct, Complex.im_sum]

lemma qf_add {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by
  have h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]
  ring

end KThetaSummandNorm

open KThetaSummandNorm in
theorem ThetaSummandNorm.proof : ThetaSummandNorm.Statement := by
  intro g X Y a b u₁ u₂ k hY
  set w : Fin g → ℝ := intVec k + a with hw
  have hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ) := rfl
  have hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) +
      (fun i => (b i : ℂ)) =
      periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ) := by
    ext i; simp [add_assoc]
  have hre : (π * Complex.I *
      ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) +
      2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re =
      -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁)) := by
    rw [dotProduct_add]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
      im_dot_period, im_dot_real]
    simp only [qf]
    ring
  unfold thetaSummand
  rw [hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  have : intVec k + a + u₁ = w + u₁ := rfl
  rw [this, qf_add Y hY w u₁]
  ring

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace RestCutTransportFirst

end RestCutTransportFirst

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartDensityIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartDensityIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    Integrable (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartHessCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def ChartHessCompare.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∃ C : ℝ, ∀ y : Fin e → ℂ, (cxHessian (hermChartPot M) y).PosDef ∧
      ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartIbpSymm.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    ∫ y : Fin (n + 1) → ℂ, (hermChartPot A y - hermChartPot B y) *
        maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
          fun i => hermChartPot (T i)) y =
      ∫ y : Fin (n + 1) → ℂ, (hermChartPot C y - hermChartPot D y) *
        maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
          fun i => hermChartPot (T i)) y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussFourierSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory
open scoped FourierTransform

namespace PGaussFourierSelf

lemma ofReal_gauss {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end PGaussFourierSelf

theorem GaussFourierSelf.proof : GaussFourierSelf.Statement := by
  intro g w
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    exact PGaussFourierSelf.ofReal_gauss x
  rw [hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hpi, Complex.one_cpow, one_mul]
  congr 1
  field_simp

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDetFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PGaussDetFactor

lemma rpow_neg_half_sq {d : ℝ} (hd : 0 < d) : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  exact Real.rpow_neg_one d

end PGaussDetFactor


open PGaussDetFactor in
theorem GaussDetFactor.proof : GaussDetFactor.Statement := by
  intro g Y B hY hBY
  have hd : 0 < Y.det := hY.det_pos
  have hsq : B.det ^ 2 = (1 / 2 : ℝ) ^ g * Y.det := by
    have := congrArg Matrix.det hBY
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
    rw [sq]; exact this
  have hB0 : 0 < |B.det| := by
    have : B.det ^ 2 ≠ 0 := by rw [hsq]; positivity
    exact abs_pos.mpr (fun h => this (by rw [h]; ring))
  have hL : 0 ≤ |B.det|⁻¹ := (inv_pos.mpr hB0).le
  have hR : 0 ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) := by positivity
  refine (pow_left_inj₀ hL hR (two_ne_zero)).mp ?_
  rw [inv_pow, sq_abs, hsq, mul_pow, rpow_neg_half_sq hd, ← pow_mul, mul_comm g 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_inv, one_div, inv_pow, inv_inv]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussSqrt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussSqrt

theorem eq_eigenvectors_mul_diagonal {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

end PGaussSqrt

theorem GaussSqrt.proof : GaussSqrt.Statement := by
  intro g Y hY
  classical
  set hH := hY.isHermitian
  set U : Matrix (Fin g) (Fin g) ℝ := (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hUdef
  refine ⟨diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ, ?_⟩
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (hY.eigenvalues_pos i).le
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc U * diagonal (fun i => √(hH.eigenvalues i)) * (diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ)
      = U * (diagonal (fun i => √(hH.eigenvalues i)) * diagonal (fun i => √(hH.eigenvalues i)))
          * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal hH.eigenvalues * Uᵀ := by
      have hsq : (fun i => √(hH.eigenvalues i) * √(hH.eigenvalues i)) = hH.eigenvalues :=
        funext fun i => Real.mul_self_sqrt (hnn i)
      rw [diagonal_mul_diagonal, hsq]
    _ = Y := (PGaussSqrt.eq_eigenvectors_mul_diagonal hH).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCoords
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussLatticeCoords

theorem toLp_mulVec_intVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (k : Fin g → ℤ) :
    WithLp.toLp 2 (B *ᵥ intVec k) = ∑ i, k i • WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  have h : intVec k = ∑ i, (k i : ℝ) • (Pi.single i 1 : Fin g → ℝ) := by
    ext j
    simp [intVec, Finset.sum_apply, Pi.single_apply]
  rw [h, Matrix.mulVec_sum, WithLp.toLp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, Int.cast_smul_eq_zsmul]

end PGaussLatticeCoords


open PGaussLatticeCoords in
theorem GaussLatticeCoords.proof : GaussLatticeCoords.Statement := by
  intro g B hB
  refine ⟨fun k => ?_, fun x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [toLp_mulVec_intVec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    exact ⟨c, by rw [toLp_mulVec_intVec, hc]⟩
  · have hk : B *ᵥ intVec k = B *ᵥ intVec k' := hkk'
    have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hB
    have hv : intVec k = intVec k' := by
      have := congrArg (fun v => B⁻¹ *ᵥ v) hk
      simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hu, Matrix.one_mulVec] using this
    funext i
    exact Int.cast_injective (congrFun hv i)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCharIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory

noncomputable section

namespace KThetaCharIntegral

theorem integral_Icc_exp (n : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((n : ℂ) * (t : ℂ))) =
      if n = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hn
  · subst hn; simp
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have h1 : ∀ t : ℝ, 2 * π * Complex.I * ((n : ℂ) * (t : ℂ)) = 2 * π * Complex.I * n * t := by
      intro t; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h2]
    simp

theorem torusChar_eq_prod {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) :
    torusChar m u = ∏ i, Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (u i : ℂ))) := by
  unfold torusChar
  rw [Finset.mul_sum, Complex.exp_sum]

end KThetaCharIntegral

theorem ThetaCharIntegral.proof : ThetaCharIntegral.Statement := by
  intro g m
  have hset : Set.Icc (0 : Fin g → ℝ) 1 = Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 := by
    rw [← Set.pi_univ_Icc]; rfl
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  simp_rw [KThetaCharIntegral.torusChar_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * ((m i : ℂ) * (t : ℂ))))]
  simp_rw [KThetaCharIntegral.integral_Icc_exp]
  by_cases hm : m = 0
  · subst hm; simp
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (funext h)
    rw [if_neg hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDualMin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussDualMin

theorem inner_toLp_eq_dotProduct {g : ℕ} (m w : Fin g → ℝ) :
    inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g)) (WithLp.toLp 2 w) = m ⬝ᵥ w := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

theorem qf_inv_transpose_mulVec {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0)
    (m : Fin g → ℝ) : qf (Bᵀ * B)⁻¹ (Bᵀ *ᵥ m) = m ⬝ᵥ m := by
  have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
  have hBu : IsUnit B.det := hB.isUnit
  have h1 : (Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ m) = B⁻¹ *ᵥ m := by
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hBt,
      Matrix.mul_one]
  unfold qf
  rw [h1, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv _ hBu,
    one_mulVec]

end PGaussDualMin


open PGaussDualMin in
theorem GaussDualMin.proof : GaussDualMin.Statement := by
  intro g B hB μ hμ hμ0
  classical
  obtain ⟨m, rfl⟩ : ∃ m : Fin g → ℝ, μ = WithLp.toLp 2 m := ⟨WithLp.ofLp μ, (WithLp.toLp_ofLp _ μ).symm⟩
  have hdual := GroundTheory.Global.mem_dualLattice.1 hμ
  have hex : ∀ i : Fin g, ∃ k : ℤ, inner ℝ (WithLp.toLp 2 m : EuclideanSpace ℝ (Fin g))
      (WithLp.toLp 2 (B *ᵥ Pi.single i 1)) = k :=
    fun i => hdual _ (Submodule.subset_span ⟨i, rfl⟩)
  choose l hl using hex
  have hlm : intVec l = Bᵀ *ᵥ m := by
    funext i
    change ((l i : ℤ) : ℝ) = _
    rw [← hl i, inner_toLp_eq_dotProduct, dotProduct_mulVec, dotProduct_single_one,
      mulVec_transpose]
  refine ⟨l, ?_, ?_⟩
  · intro hl0
    apply hμ0
    have hBt : IsUnit (Bᵀ).det := by rw [det_transpose]; exact hB.isUnit
    have h0 : Bᵀ *ᵥ m = 0 := by
      rw [← hlm, hl0]; funext i; simp [intVec]
    have hm0 : m = 0 := by
      calc m = (Bᵀ)⁻¹ *ᵥ (Bᵀ *ᵥ m) := by
            rw [mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
        _ = 0 := by rw [h0, mulVec_zero]
    rw [hm0]; rfl
  · rw [hlm, qf_inv_transpose_mulVec B hB, ← real_inner_self_eq_norm_sq,
      inner_toLp_eq_dotProduct]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace PGaussPoissonDual

theorem qf_smul {g : ℕ} (c : ℝ) (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    qf (c • Y) w = c * qf Y w := by
  rw [qf, qf, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_mulVec_self {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℝ) :
    (B *ᵥ w) ⬝ᵥ (B *ᵥ w) = qf (Bᵀ * B) w := by
  rw [qf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w Bᵀ, Matrix.vecMul_transpose]

end PGaussPoissonDual


open PGaussPoissonDual in
theorem GaussPoissonDual.proof (hS : GaussSqrt.Statement) (hP : GaussPoissonBound.Statement)
    (hM : GaussDualMin.Statement) (hD : GaussDetFactor.Statement) :
    GaussPoissonDual.Statement := by
  intro g Y ρ hY hρ hmin u
  have hY2 : ((1 / 2 : ℝ) • Y).PosDef := hY.smul (by norm_num)
  obtain ⟨B, hB⟩ := hS g _ hY2
  have hdetB : B.det ≠ 0 := by
    intro h0
    have h1 : (Bᵀ * B).det = 0 := by rw [det_mul, det_transpose, h0, mul_zero]
    rw [hB] at h1
    exact hY2.det_pos.ne' h1
  have hterm : ∀ k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) =
      Real.exp (-π * ((B *ᵥ (intVec k + u)) ⬝ᵥ (B *ᵥ (intVec k + u)))) := by
    intro k
    rw [dot_mulVec_self, hB, qf_smul]
    ring_nf
  obtain ⟨hsum, -, hle⟩ := hP g B hdetB u
  refine ⟨(summable_congr hterm).2 hsum, GroundTheory.Global.dualLattice (gaussLattice B), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨l, hl0, hl⟩ := hM g B hdetB v hv hv0
    have hYdet : IsUnit Y.det := isUnit_iff_ne_zero.2 hY.det_pos.ne'
    have hinv : (Bᵀ * B)⁻¹ = (2 : ℝ) • Y⁻¹ := by
      rw [hB]
      apply Matrix.inv_eq_left_inv
      rw [smul_mul_smul_comm, Y.nonsing_inv_mul hYdet]
      norm_num
    rw [hinv, qf_smul] at hl
    have h2 := hmin l hl0
    have hq : 0 ≤ qf Y⁻¹ (intVec l) := le_trans (sq_nonneg ρ) h2
    have h3 : ρ ^ 2 ≤ ‖v‖ ^ 2 := by linarith
    nlinarith [norm_nonneg v]
  · rw [tsum_congr hterm, ← hD g Y B hY hB]
    exact hle

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTermBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

namespace PGaussTermBound

theorem pow_le_sqrt_pow_mul_exp (n m : ℕ) (hn : 1 ≤ n) :
    ((m : ℝ) + 1) ^ n ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) := by
  set s := √(n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  have hm : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (s * ((m : ℝ) + 1)) (mul_nonneg hs.le hm) n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hfac] at h1
  have hfac2 : (n.factorial : ℝ) ≤ s ^ n * s ^ n := by
    rw [← mul_pow, hss]
    exact_mod_cast Nat.factorial_le_pow n
  have hE : 0 ≤ Real.exp (s * ((m : ℝ) + 1)) := (Real.exp_pos _).le
  have h2 : s ^ n * ((m : ℝ) + 1) ^ n ≤ s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by
    rw [← mul_pow]
    calc (s * ((m : ℝ) + 1)) ^ n ≤ Real.exp (s * ((m : ℝ) + 1)) * (n.factorial : ℝ) := h1
      _ ≤ Real.exp (s * ((m : ℝ) + 1)) * (s ^ n * s ^ n) := mul_le_mul_of_nonneg_left hfac2 hE
      _ = s ^ n * (s ^ n * Real.exp (s * ((m : ℝ) + 1))) := by ring
  exact le_of_mul_le_mul_left h2 (pow_pos hs n)

theorem exponent_le (n m : ℕ) :
    √(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2 ≤ √(n : ℝ) + n / (2 * π) + -(m : ℝ) := by
  set s := √(n : ℝ) with hs_def
  have hss : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hpi : 0 < π := Real.pi_pos
  have hpi3 : 3 < π := Real.pi_gt_three

  have hA : s * m - π / 2 * (m : ℝ) ^ 2 ≤ n / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (π * m - s)]

  have hB : (m : ℝ) ≤ π / 2 * (m : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  nlinarith

end PGaussTermBound

theorem GaussTermBound.proof : GaussTermBound.Statement := by
  intro n hn m
  have h1 := PGaussTermBound.pow_le_sqrt_pow_mul_exp n m hn
  have h2 := PGaussTermBound.exponent_le n m
  have hE : 0 ≤ Real.exp (-π * (m : ℝ) ^ 2) := (Real.exp_pos _).le
  calc ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)
      ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1)) * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hE
    _ = √(n : ℝ) ^ n * Real.exp (√(n : ℝ) * ((m : ℝ) + 1) + -π * (m : ℝ) ^ 2) := by
        rw [Real.exp_add]; ring
    _ ≤ √(n : ℝ) ^ n * Real.exp (√(n : ℝ) + n / (2 * π) + -(m : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)
    _ = √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ)) := by
        rw [Real.exp_add, Real.exp_add]; ring

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSymplStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem SymplStep.proof (h1 : SymplFirstRow.Statement) (h2 : SymplGramMem.Statement)
    (h3 : SymplReduceMem.Statement) (h4 : SymplReducePosDef.Statement)
    (h5 : SymplReduceStep.Statement) : SymplStep.Statement := by
  intro n B G hG hGpd hind
  obtain ⟨ρsq, hleast, hpos, hle, P₁, hP₁, hP₁e⟩ := h1 n G hG hGpd
  obtain ⟨hHmem, hHpd, hcomp, -⟩ := h2 (n + 1) P₁ G hP₁ hG hGpd
  have hHe : symplGram P₁ G (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    rw [hP₁e]; exact hpos.ne'
  obtain ⟨Q, hQ, hQB⟩ :=
    hind (symplReduce (symplGram P₁ G)) (h3 n _ hHmem hHe) (h4 n _ hHpd)
  obtain ⟨Q', hQ', hQ'e, hQ'det⟩ := h5 n (symplGram P₁ G) Q hHe hQ
  refine ⟨ρsq, hleast, hpos, hle, Q' * P₁, Submonoid.mul_mem _ hQ' hP₁, ?_, ?_⟩
  · rw [hcomp Q', hQ'e, hP₁e]
  · rw [hcomp Q', hQ'det, hP₁e]
    exact mul_le_mul_of_nonneg_left hQB hpos.le

end GroundTheory.Heights₂.Heights
end
