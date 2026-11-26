module

public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPiQuotCokerFiniteLength
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramPolar
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Finset
open ReciprocityTheory.ChartRestriction.G.Geo (mixedDisc)

theorem ChartGram.sum_neg_one_pow_card_pow (D : ℕ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
  have h1 := fwdDiff_iter_eq_sum_shift (h := (1 : ℂ)) (fun r : ℂ => r ^ D) D 0
  rw [fwdDiff_iter_eq_factorial] at h1
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := fun m => (-1 : ℂ) ^ (D - m) * (m : ℂ) ^ D)]
  simp only [Finset.card_univ, Fintype.card_fin]
  have h2 : ((D.factorial : ℂ → ℂ) 0) = (D.factorial : ℂ) := rfl
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

theorem ChartGram.mixedDisc_const {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  unfold mixedDisc
  have h : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h, ← Finset.sum_mul, ChartGram.sum_neg_one_pow_card_pow]
  have : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  field_simp

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChartGramSchur
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

theorem ChartGram.det_eq_corner_mul_schur {K : Type*} [Field K] {e : ℕ}
    (M : Matrix (Fin (e + 1)) (Fin (e + 1)) K) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      (Matrix.of fun i j : Fin e => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0).det := by
  set c : Fin (e + 1) → K := fun i => if i = 0 then 0 else -(M i 0 / M 0 0) with hc
  set B : Matrix (Fin (e + 1)) (Fin (e + 1)) K := Matrix.of fun i j => M i j + c i * M 0 j with hB
  have hdet : B.det = M.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [hc]) (fun i j => by simp [hB])
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin e, B i.succ 0 = 0 := by
    intro i
    simp only [hB, hc, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    field_simp
    ring
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  congr 1
  · simp [hB, hc]
  · congr 1
    ext i j
    simp only [hB, hc, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    ring

end GroundTheory.Heights₂.Heights
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity cxHessian)

theorem ChartGramMA.proof : ChartGramMA.Statement := by
  intro e n v y hv h0

  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hv
  have han : AnalyticOnNhd ℂ v t := by
    have hd : DifferentiableOn ℂ v t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  set L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm with hL
  set u : (Fin e → ℂ) → EuclideanSpace ℂ (Fin n) := fun y' => L (v y') with hu_def
  have hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y' := by
    filter_upwards [hto.mem_nhds hyt] with y' hy'
    exact (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).analyticAt _ |>.comp (han y' hy')
  have hu0 : u y ≠ 0 := by
    simpa [hu_def, hL, PiLp.coe_symm_continuousLinearEquiv] using h0
  have hDu : ∀ b, fderiv ℂ u y b = L (fderiv ℂ v y b) := fun b => by
    have hc := (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp y
      (hv.self_of_nhds).hasFDerivAt
    have hc' : HasFDerivAt u _ y := hc
    rw [hc'.fderiv]
    rfl

  have hφ : (fun (_ : Fin e) (y' : Fin e → ℂ) => Real.log ‖WithLp.toLp 2 (v y')‖) =
      fun _ y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re := by
    funext _ y'
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (u y')
    have h' : (⟪u y', u y'⟫_ℂ).re = ‖u y'‖ ^ 2 := h
    rw [h', Real.log_pow]
    simp [hu_def, hL]

  set w : Fin (e + 1) → EuclideanSpace ℂ (Fin n) :=
    Fin.cons (u y) fun j => fderiv ℂ u y (Pi.single j 1) with hw
  set G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Matrix.of fun a b => ⟪w a, w b⟫_ℂ with hG_def
  have hmat : G = Matrix.of fun a b => ∑ i,
      star ((Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) a i) *
        (Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) b i := by
    ext a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [hG_def, hw, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hDu] <;>
      simp only [PiLp.inner_apply, RCLike.inner_apply'] <;>
      simp [hu_def, hL]
  have hgram : gramVol v y = G.det.re := by
    rw [hmat]; rfl
  have hG00 : G 0 0 ≠ 0 := by
    simpa [hG_def, hw] using hu0
  have hcx : cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y =
      (2 * G 0 0)⁻¹ • Matrix.transpose (Matrix.of fun i j : Fin e =>
        G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) := by
    ext i j
    rw [ChartGram.cxHessian_half_log hu hu0]
    simp only [hG_def, hw, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
    have : ⟪u y, u y⟫_ℂ ≠ 0 := by simpa [hG_def, hw] using hG00
    field_simp
  have hS := ChartGram.det_eq_corner_mul_schur G hG00
  have hN : G 0 0 = ((‖u y‖ ^ 2 : ℝ) : ℂ) := by
    simp [hG_def, hw]
  have hNpos : 0 < ‖u y‖ := norm_pos_iff.2 hu0
  unfold maDensity
  rw [hφ, ChartGram.mixedDisc_const, hcx, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin,
    hgram, hS]
  generalize (Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0).det = Z
  rw [hN]
  have hnorm : ‖WithLp.toLp 2 (v y)‖ = ‖u y‖ := rfl
  rw [hnorm]
  generalize ‖u y‖ = r at hNpos ⊢
  rw [show ((2 : ℂ) * ((r ^ 2 : ℝ) : ℂ))⁻¹ ^ e = (((2 * r ^ 2)⁻¹ ^ e : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, pow_mul]
  have hpi : Real.pi ^ e * Real.pi⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  have hr : r ^ (e * 2) * r⁻¹ ^ (e * 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  have h2 : (1 / 2 : ℝ) ^ e * 2 ^ e = 1 := by
    rw [← mul_pow]; norm_num
  field_simp
  linear_combination (r ^ 2 * Z.re * r ^ (e * 2) * r⁻¹ ^ (e * 2) * (1 / 2) ^ e * 2 ^ e) * hpi +
    (r ^ 2 * Z.re * (1 / 2) ^ e * 2 ^ e) * hr + (r ^ 2 * Z.re) * h2

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSlab
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeSlabBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖}) ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealSeparate.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P Q : Ideal (MvPolynomial (Fin n) F)),
    IsProjPrime P → IsProjPrime Q → incIdeal Q k ≠ ⊥ → incIdeal Q k ≤ incIdeal P k → Q ≤ P

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMeetNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMeetNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W W' : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime → W'.IsPrime →
    W ≠ W' → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W') ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 2 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I →
        chowDegree I (e + 2) = (divCycle I u).sum fun W m => m * chowDegree W (e + 1)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecFiniteUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecFiniteUnit.Statement : Prop :=
  ∀ (k R : Type) [Field k] [CommRing R] [Algebra k R] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → R), IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      IsUnit (eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k R) g y)) →
        Module.Finite R (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k R))) y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMassOfFibre.Statement : Prop :=
  ∀ (n m δ : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsProjPrime J →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = δ) →
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf y) q = 0} =
        (δ : ENNReal) * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeGe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [PerfectField k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      eval (fun j => y (.inr j)) (Vertical.specRest (algebraMap k E) g y) ≠ 0 →
        Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ∧
          δ ≤ Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem finsum_log_gaussNorm_mul {ι : Type*} {f g : MvPolynomial ι K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (f * g)) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g) := by
  rw [← finsum_add_distrib (log_gaussNorm_support_finite hf) (log_gaussNorm_support_finite hg)]
  refine finsum_congr fun v => ?_
  rw [gaussNorm_mul, Real.log_mul (gaussNorm_pos v hf).ne' (gaussNorm_pos v hg).ne']

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecRankSpecialize
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecRankSpecialize.Statement : Prop :=
  ∀ (R K κ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field κ] [Algebra R κ] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Vertical.Par e n → R),
    Function.Surjective (algebraMap R κ) → Module.Finite R (Vertical.SecAlg Q y) →
      Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) ≤
        Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SecDegreeLe.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e δ : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Vertical.Par e n → E),
    IsProjPrime Q → IsChowForm Q (e + 1) g → IsMultiHomog δ g →
      Module.Finite E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      IsDomain (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Algebra.IsSeparable E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) →
      Vertical.specRest (algebraMap k E) g y ≠ 0 →
        Module.finrank E (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y) ≤ δ

namespace SecDegreeLe

end SecDegreeLe

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapArea
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapArea.Statement : Prop :=
  ∀ (n e : ℕ) (ι : Type) [Countable ι] (U D : ι → Set (Fin e → ℂ))
    (v : ι → (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    (∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i)) →
    Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
              {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∑' i, ∫⁻ x in D i, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPolyLocalGenerators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

def polyTangent {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ q ∈ S, ∑ j, eval p (pderiv j q) * v j = 0}
  add_mem' {v w} hv hw q hq := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at hv hw ⊢
    rw [hv q hq, hw q hq, add_zero]
  zero_mem' q _ := by simp
  smul_mem' c v hv q hq := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum] at hv ⊢
    rw [hv q hq, mul_zero]

def PolyLocalGenerators.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = m →
    ∀ p : Fin n → ℂ, (∀ q ∈ J, eval p q = 0) →
      finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) = m →
      ∃ (q : Fin (n - m) → MvPolynomial (Fin n) ℂ) (g : MvPolynomial (Fin n) ℂ),
        (∀ i, q i ∈ J) ∧ eval p g ≠ 0 ∧ finrank ℂ (polyTangent (Set.range q) p) = m ∧
        ∀ r ∈ J, g * r ∈ Ideal.span (Set.range q)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionLengthSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace SectionLengthSum

theorem prime_between {A : Type*} [CommRing A] [IsNoetherianRing A] {J W Q : Ideal A} {f : A}
    (hWP : ∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    [hQ : Q.IsPrime] (hJQ : J ≤ Q) (hQW : Q ≤ W) : Q ∈ J.minimalPrimes ∨ Q = W := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hPp : P.IsPrime := hP.1.1
  rcases eq_or_lt_of_le hPQ with h | hlt
  · exact Or.inl (h ▸ hP)
  rcases eq_or_lt_of_le hQW with h | hlt2
  · exact Or.inr h
  exfalso
  have hW := hWP P hP (hPQ.trans hQW)
  have hWp : W.IsPrime := hW.1.1
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set g := Ideal.Quotient.mk P
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = P := Ideal.mk_ker
  have hcm : ∀ I : Ideal A, P ≤ I → (I.map g).comap g = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective g hsurj, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hI]
  have : (Q.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ)
  have : (W.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ.trans hQW)
  have : (W.map g).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have : (Q.map g).FiniteHeight :=
    ⟨Or.inr ((Ideal.height_mono (Ideal.map_mono hQW)).trans_lt (h1.trans_lt (WithTop.coe_lt_top 1))).ne⟩
  have hbot : (⊥ : Ideal (A ⧸ P)) < Q.map g := by
    refine lt_of_le_of_ne bot_le fun h => hlt.ne ?_
    rw [← hcm Q hPQ, ← h, ← RingHom.ker_eq_comap_bot, hker]
  have hQW' : Q.map g < W.map g := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun h => hlt2.ne ?_
    rw [← hcm Q hPQ, h, hcm W (hPQ.trans hQW)]
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQW'
  have h3 := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := ⊥) hbot
  have h4 : (Q.map g).height < 1 := h2.trans_le h1
  rw [Order.lt_one_iff] at h4
  rw [h4] at h3
  exact absurd h3 (not_lt_of_ge bot_le)

theorem length_ne_top_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by
  have : IsArtinianRing (B ⧸ I) := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian B (B ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem proof (hLoc : LocalSectionLengthSum.Statement) : SectionLengthSum.Statement := by
  intro A _ _ J W f hJ hf hW hWP
  classical
  have hWp : W.IsPrime := hW.1.1
  let B := Localization.AtPrime W
  let φ := algebraMap A B
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing W.primeCompl B inferInstance
  have hmin : ∀ Q : Ideal B, Q ∈ (J.map φ).minimalPrimes ↔ Q.comap φ ∈ J.minimalPrimes := fun Q => by
    rw [IsLocalization.minimalPrimes_map W.primeCompl B J]
    rfl
  have hcomapW : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ ≤ W := fun Q hQ x hx => by
    by_contra hxW
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units B (⟨x, hxW⟩ : W.primeCompl)))
  have hmapcomap : ∀ Q : Ideal B, (Q.comap φ).map φ = Q := fun Q =>
    IsLocalization.map_under W.primeCompl B Q
  have hcomapmap : ∀ P : Ideal A, P.IsPrime → P ≤ W → (P.map φ).comap φ = P := fun P hP hPW =>
    IsLocalization.under_map_of_isPrime_disjoint W.primeCompl B hP
      (Set.disjoint_left.mpr fun x hx hxP => hx (hPW hxP))
  have hJ' : (J.map φ).IsRadical := by
    show (J.map φ).radical ≤ J.map φ
    rw [← IsLocalization.map_radical W.primeCompl B J, hJ.radical]
  have hf' : ∀ Q ∈ (J.map φ).minimalPrimes, φ f ∉ Q := fun Q hQ hfQ => hf _ ((hmin Q).1 hQ) hfQ
  have hdim : ∀ Q : Ideal B, Q.IsPrime → J.map φ ≤ Q →
      Q ∈ (J.map φ).minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B := by
    intro Q hQ hJQ
    have : (Q.comap φ).IsPrime := hQ.comap φ
    rcases prime_between hWP (Ideal.map_le_iff_le_comap.mp hJQ) (hcomapW Q hQ) with h | h
    · exact Or.inl ((hmin Q).2 h)
    · right
      rw [← hmapcomap Q, h]
      exact IsLocalization.AtPrime.map_eq_maximalIdeal W B
  have key := hLoc B (J.map φ) (φ f) hJ' hf' hdim
  have hsup : ∀ I : Ideal A, (I ⊔ Ideal.span {f}).map φ = I.map φ ⊔ Ideal.span {φ f} := fun I => by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hlm : ∀ I : Ideal A, localMult (I ⊔ Ideal.span {f}) W =
      (Module.length B (B ⧸ (I.map φ ⊔ Ideal.span {φ f}))).toNat := fun I => by
    unfold localMult
    rw [dite_eq_left hWp, hsup]
  have hfW : φ f ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W B]
    exact Ideal.mem_map_of_mem φ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have hfin : ∀ Q ∈ (J.map φ).minimalPrimes,
      Module.length B (B ⧸ (Q ⊔ Ideal.span {φ f})) ≠ ⊤ := by
    intro Q hQ
    refine length_ne_top_of_mem_minimalPrimes _ ⟨⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime,
      sup_le (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hfW)⟩,
      fun Q₂ hQ₂ _ => ?_⟩
    rcases hdim Q₂ hQ₂.1 (hQ.1.2.trans (le_sup_left.trans hQ₂.2)) with h | h
    · exact absurd (hQ₂.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) (hf' Q₂ h)
    · exact h.ge
  rw [hlm J, key, ENat.toNat_sum (fun Q hQ => hfin Q ((Set.Finite.mem_toFinset _).mp hQ))]
  symm
  refine Finset.sum_nbij' (fun P => P.map φ) (fun Q => Q.comap φ) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    rw [Set.Finite.mem_toFinset, hmin, hcomapmap P hP.1.1.1 hP.2]
    exact hP.1
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨(hmin Q).1 hQ, hcomapW Q hQ.1.1⟩
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact hcomapmap P hP.1.1.1 hP.2
  · intro Q _
    exact hmapcomap Q
  · intro P _
    exact hlm P

end SectionLengthSum

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointConeCoord
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointConeCoord.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → y i ≠ 0

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointChartField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointChartField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      IsField (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ∧
        Module.Finite F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughTwoPointsTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughTwoPointsTrdeg.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] (n k : ℕ) [Algebra K Ω]
    [Algebra (MvPolynomial (Fin k × Fin n) K) Ω] [IsScalarTower K (MvPolynomial (Fin k × Fin n) K) Ω],
    Function.Injective (algebraMap (MvPolynomial (Fin k × Fin n) K) Ω) →
    ∀ x c : Fin n → K, ∑ j, c j * x j = 1 →
    ∀ (y : Fin n → Ω) (j : Fin n), y j ≠ 0 → (∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m)) →
      (∀ i, ∑ m, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (genSubst x c (i, m)) * y m = 0) →
        (k : Cardinal) ≤ Algebra.trdeg K (Algebra.adjoin K (Set.range fun m => y m * (y j)⁻¹))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapAreaOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapAreaOne.Statement : Prop :=
  ∀ (n e : ℕ) (U D : Set (Fin e → ℂ)) (v : (Fin e → ℂ) → (Fin n → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsOpen U → MeasurableSet D → D ⊆ U → DifferentiableOn ℂ v U →
    Set.InjOn (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) {q | q.1 ∈ D ∧ q.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ''
              {q | q.1 ∈ D ∧ q.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x in D, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)

end GroundTheory.Heights₂.Heights
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsHolomorphicImplicitGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

def HolomorphicImplicitGraph.Statement : Prop :=
  ∀ (n m : ℕ) (f : Fin (n - m) → EuclideanSpace ℂ (Fin n) → ℂ) (y : EuclideanSpace ℂ (Fin n))
    (V : Set (EuclideanSpace ℂ (Fin n))),
    (∀ i, ContDiff ℂ 1 (f i)) → IsOpen V → y ∈ V → (∀ i, f i y = 0) →
    finrank ℂ ↥(⨅ i, LinearMap.ker (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin n))) = m →
      ∃ (e : Fin n ≃ Fin m ⊕ Fin (n - m)) (Ω : Set (EuclideanSpace ℂ (Fin m)))
        (Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)))
        (U : Set (EuclideanSpace ℂ (Fin n))),
        IsOpen U ∧ y ∈ U ∧ U ⊆ V ∧ IsOpen Ω ∧ DifferentiableOn ℂ Φ Ω ∧
        graphPt e Φ '' Ω = {z | z ∈ U ∧ ∀ i, f i z = 0} ∧
        ∀ x ∈ Ω, LinearMap.range (fderiv ℂ (graphPt e Φ) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) =
          ⨅ i, LinearMap.ker (fderiv ℂ (f i) (graphPt e Φ x) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMinimalPrimeComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MinimalPrimeComap.flat (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    letI := σ.toAlgebra
    letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L) := inferInstance
  exact Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out

theorem MinimalPrimeComap.proof : MinimalPrimeComap.Statement := by
  intro K L _ _ σ ι I hI P hP
  letI := σ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have := MinimalPrimeComap.flat K L σ ι
  have halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ := rfl
  have : P.IsPrime := hP.1.1
  have hle : I ≤ P.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hP.1.2
  by_contra hne
  have hlt : I < P.under (MvPolynomial ι K) := lt_of_le_of_ne hle (fun h => hne h.symm)
  have : (P.under (MvPolynomial ι K)).IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (P.under (MvPolynomial ι K)) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQI⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt
  have hIQ : I.map (MvPolynomial.map σ) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]
  exact (not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeAvoid
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem BaseChangeAvoid.comap_eq_of_mem_minimalPrimes {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    {W : Ideal (MvPolynomial (Fin n) L)} (hW : W ∈ (I.map (MvPolynomial.map σ)).minimalPrimes) :
    W.comap (MvPolynomial.map σ) = I := by
  let : Algebra K L := σ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) := algebraMvPolynomial
  have : Module.Free K L := Module.Free.of_divisionRing K L
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange K (MvPolynomial (Fin n) K) L (MvPolynomial (Fin n) L)
      Algebra.IsPushout.out
  have halg : algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) = MvPolynomial.map σ :=
    rfl
  obtain ⟨⟨hWp, hIW⟩, hmin⟩ := hW
  have := hWp
  have hIP : I ≤ W.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hIW
  have : (W.comap (MvPolynomial.map σ)).IsPrime := Ideal.comap_isPrime _ W
  have : W.LiesOver (W.comap (MvPolynomial.map σ)) := ⟨by rw [Ideal.under_def, halg]⟩
  obtain ⟨W', hW'W, hW'p, hW'I⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := I) W hIP
  have hI' : I = W'.comap (MvPolynomial.map σ) := by rw [hW'I.over, Ideal.under_def, halg]
  have hIW' : I.map (MvPolynomial.map σ) ≤ W' := Ideal.map_le_iff_le_comap.mpr hI'.le
  have hWW' : W ≤ W' := hmin ⟨hW'p, hIW'⟩ hW'W
  rw [hI', le_antisymm hW'W hWW']

theorem BaseChangeAvoid.proof : BaseChangeAvoid.Statement := by
  intro K _ _ n I u σ hI hu W hW h
  have hW' : W ∈ relComps (I.map (MvPolynomial.map σ)) := by
    by_contra hn
    rw [Finsupp.mem_support_iff] at hW
    exact hW (by simp [fundCycle, Finsupp.onFinset_apply, hn])
  have := hI.isPrime
  have hc := BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I hW'.1
  apply hu
  rw [← hc, Ideal.mem_comap]
  convert h using 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum]

end GroundTheory.Heights₂.Heights
end
