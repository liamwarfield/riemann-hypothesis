module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianJetsAtOriginEqFockVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableConjMonomialBargmannGaussian
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableConjMonomialBargmannGaussian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_vcx_prod {ι : Type} [Fintype ι] {a b : ℕ} (g : ι → Fin b → Fin a → ℂ → ℂ)
    (hg : ∀ τ i j, Integrable (g τ i j)) :
    Integrable fun z : VCx ι a b => ∏ τ, ∏ i, ∏ j, g τ i j (z τ i j) := by
  have h1 : ∀ τ i, Integrable (fun w : Fin a → ℂ => ∏ j, g τ i j (w j)) := fun τ i =>
    Integrable.fintype_prod (f := fun j (w : ℂ) => g τ i j w) (hg τ i)
  have h2 : ∀ τ, Integrable (fun w : Fin b → Fin a → ℂ => ∏ i, ∏ j, g τ i j (w i j)) := fun τ =>
    Integrable.fintype_prod (f := fun i (w : Fin a → ℂ) => ∏ j, g τ i j (w j)) (h1 τ)
  exact Integrable.fintype_prod (f := fun τ (w : Fin b → Fin a → ℂ) => ∏ i, ∏ j, g τ i j (w i j)) h2

theorem exp_gq_eq_prod {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z : VCx ι a b) :
    (Real.exp (-gq c z / 2) : ℂ) = ∏ τ, ∏ i, ∏ j, (Real.exp (-(c τ * ‖z τ i j‖ ^ 2) / 2) : ℂ) := by
  have h : -gq c z / 2 = ∑ τ, ∑ i, ∑ j, (-(c τ * ‖z τ i j‖ ^ 2) / 2) := by
    simp [gq, Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  rw [h]
  simp only [Real.exp_sum]
  push_cast
  rfl

theorem integrable_conj_pow_mul_gauss (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => conj w ^ n * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq (E := ℂ) n (b := c / 2) (by positivity)
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_of_eq
  congr 2
  ring

theorem integrable_exp_bargmann_mul_gauss (u : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable fun w : ℂ => Complex.exp ((c : ℂ) * u * conj w) * (Real.exp (-(c * ‖w‖ ^ 2) / 2) : ℂ) := by
  have h := (GlobalTheory.integrable_exp_neg_mul_norm_sq (E := ℂ) (b := c / 4) (by positivity)).const_mul
    (Real.exp (c * ‖u‖ ^ 2))
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun w => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : ((c : ℂ) * u * conj w).re ≤ c * (‖u‖ * ‖w‖) := by
    calc _ ≤ ‖(c : ℂ) * u * conj w‖ := Complex.re_le_norm _
      _ = c * (‖u‖ * ‖w‖) := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hc.le]
        ring
  have h2 : ‖u‖ * ‖w‖ ≤ ‖u‖ ^ 2 + ‖w‖ ^ 2 / 4 := by nlinarith [sq_nonneg (‖u‖ - ‖w‖ / 2)]
  have h3 := mul_le_mul_of_nonneg_left h2 hc.le
  nlinarith

theorem integrable_conjMono_bargmann_gauss : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) →
    (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧
      ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  intro ι _ a b c hc
  constructor
  · intro m
    have h := integrable_vcx_prod (fun τ i j w => conj w ^ m (τ, i, j) * (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ))
      (fun τ i j => integrable_conj_pow_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [conjMono, exp_gq_eq_prod, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Fintype.prod_prod_type, Finset.prod_mul_distrib]
  · intro z₀
    have h := integrable_vcx_prod (fun τ i j w => Complex.exp ((c τ : ℂ) * z₀ τ i j * conj w) *
      (Real.exp (-(c τ * ‖w‖ ^ 2) / 2) : ℂ)) (fun τ i j => integrable_exp_bargmann_mul_gauss _ (hc τ))
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only
    rw [bk, exp_gq_eq_prod]
    simp only [Complex.exp_sum, Finset.prod_mul_distrib]

end GlobalTheory.FockTransl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableConjMonomialBargmannGaussianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → (∀ m : DVar ι a b →₀ ℕ, Integrable fun z => conjMono m z * (Real.exp (-gq c z / 2) : ℂ)) ∧ ∀ z₀ : VCx ι a b, Integrable fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) := by
  first | exact @GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss | exact GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss | (intros; apply GlobalTheory.FockTransl.integrable_conjMono_bargmann_gauss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockBargmannReproducingFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockTaylor

def curryL (ι : Type) (a b : ℕ) : (DVar ι a b → ℂ) →ₗ[ℂ] VCx ι a b where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curryL_single {ι : Type} [DecidableEq ι] {a b : ℕ} (k : DVar ι a b) :
    curryL ι a b (Pi.single k 1) = Formalism.L2.Ker.coordX k := by
  funext τ i j
  obtain ⟨x, y, z⟩ := k
  simp [curryL, Formalism.L2.Ker.coordX, Pi.single_apply, Prod.ext_iff]

theorem derivAt0_eq_pderivIter {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (G : VCx ι a b → ℂ) (hG : Differentiable ℂ G) (m : DVar ι a b →₀ ℕ) :
    derivAt0 G m = GlobalTheory.pderivIter m (fun w => G (curryL ι a b w)) 0 := by
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [derivAt0, GlobalTheory.pderivIter, GlobalTheory.pderivList, GlobalTheory.lineDerivList_comp_linearMap,
    ← GlobalTheory.lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curryL_single]

theorem coeff_taylor_eq_pderivIter {σ : Type} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (GlobalTheory.taylor f) = GlobalTheory.pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
  rw [GlobalTheory.coeff_taylor, GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList (l := α.toMultiset.toList)
    (by simp) _ hf, Nat.cast_prod, div_eq_inv_mul]
  rfl

end GlobalTheory.FockTaylor


open GlobalTheory.FockTaylor in
theorem GlobalTheory.FockTaylor.hasSum_derivAt0 : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (G : VCx ι a b → ℂ), Differentiable ℂ G → ∀ z₀ : VCx ι a b, HasSum (fun m : DVar ι a b →₀ ℕ => (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) (G z₀) := by
  intro ι _ a b G hG z₀
  classical
  let L := LinearMap.toContinuousLinearMap (curryL ι a b)
  have hf : Differentiable ℂ (fun w => G (L w)) := hG.comp L.differentiable
  have hfa : AnalyticAt ℂ (fun w => G (L w)) 0 :=
    SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  let c : (DVar ι a b →₀ ℕ) → ℂ := fun m => derivAt0 G m / ∏ j, ((m j).factorial : ℂ)
  have hne : ∀ m : DVar ι a b →₀ ℕ, (∏ j, ((m j).factorial : ℂ)) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc : ∀ m, (∏ j, ((m j).factorial : ℂ)) * c m = GlobalTheory.pderivIter m (fun w => G (L w)) 0 :=
    fun m => by
      rw [mul_div_cancel₀ _ (hne m), derivAt0_eq_pderivIter G hG m]
      rfl
  have hc' : ∀ m, c m = MvPowerSeries.coeff m (GlobalTheory.taylor fun w => G (L w)) := fun m => by
    rw [coeff_taylor_eq_pderivIter hfa]
    show derivAt0 G m / _ = _
    rw [derivAt0_eq_pderivIter G hG m]
    rfl
  let w : DVar ι a b → ℂ := fun k => z₀ k.1 k.2.1 k.2.2
  have hs := GlobalTheory.EntireTaylor.summable_of_entire hf c hc w
  have ht := GlobalTheory.ProdThetaConj.tsum_of_entire hf c hc hc' w
  have hterm : ∀ m : DVar ι a b →₀ ℕ,
      (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m
        = c m * ∏ j, w j ^ m j := fun m => by
    rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_div_distrib]
    simp only [c, w]
    ring
  have hGz : G z₀ = G (L w) := rfl
  rw [hGz, ← ht]
  exact (hs.hasSum).congr_fun hterm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (G : VCx ι a b → ℂ), Differentiable ℂ G → ∀ z₀ : VCx ι a b, HasSum (fun m : DVar ι a b →₀ ℕ => (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) (G z₀) := by
  first | exact @GlobalTheory.FockTaylor.hasSum_derivAt0 | exact GlobalTheory.FockTaylor.hasSum_derivAt0 | (intros; apply GlobalTheory.FockTaylor.hasSum_derivAt0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

theorem integrable_exp_lin_sub_sq_norm_complex {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    Integrable fun w : ℂ => Real.exp (r * ‖w‖ - c * ‖w‖ ^ 2 / 2) := by
  have hg : Integrable fun w : ℂ => Real.exp (-(c / 4) * ‖w‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := ((c / 4 : ℝ) : ℂ))
      (by simp; linarith) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  refine (hg.const_mul (Real.exp (r ^ 2 / c))).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : r ^ 2 / c + -(c / 4) * ‖w‖ ^ 2 - (r * ‖w‖ - c * ‖w‖ ^ 2 / 2)
      = (r - c * ‖w‖ / 2) ^ 2 / c := by
    field_simp
    ring
  have : 0 ≤ (r - c * ‖w‖ / 2) ^ 2 / c := by positivity
  linarith

theorem integrable_exp_lin_sub_gq (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ)
    (z₀ : VCx ι a b) :
    Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  have key : ∀ z : VCx ι a b, Real.exp ((∑ k : DVar ι a b,
      ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2)
      = ∏ τ, ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖z τ i j‖ - c τ * ‖z τ i j‖ ^ 2 / 2) := by
    intro z
    simp only [← Real.exp_sum, gq, DVar, Fintype.sum_prod_type, Finset.sum_div,
      ← Finset.sum_sub_distrib]
  simp_rw [key]
  refine Integrable.fintype_prod (f := fun τ (x : Fin b → Fin a → ℂ) =>
    ∏ i, ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖x i j‖ - c τ * ‖x i j‖ ^ 2 / 2)) fun τ => ?_
  refine Integrable.fintype_prod (f := fun i (y : Fin a → ℂ) =>
    ∏ j, Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖y j‖ - c τ * ‖y j‖ ^ 2 / 2)) fun i => ?_
  refine Integrable.fintype_prod (f := fun j (w : ℂ) =>
    Real.exp (‖(c τ : ℂ) * z₀ τ i j‖ * ‖w‖ - c τ * ‖w‖ ^ 2 / 2)) fun j => ?_
  exact integrable_exp_lin_sub_sq_norm_complex (hc τ) (norm_nonneg _)

end GlobalTheory.FockTransl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableGaussianExpLinearNormTermComplexMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ z₀ : VCx ι a b, Integrable fun z : VCx ι a b => Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
  first | exact @GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | exact GlobalTheory.FockTransl.integrable_exp_lin_sub_gq | (intros; apply GlobalTheory.FockTransl.integrable_exp_lin_sub_gq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExp
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory

theorem hasSum_pow_div_factorial_exp (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

theorem hasSum_fin_prod_pow_div_factorial_exp : ∀ (n : ℕ) (x : Fin n → ℂ),
    HasSum (fun f : Fin n → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro n
  induction n with
  | zero =>
    intro x
    have := hasSum_unique (fun f : Fin 0 → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
    simpa using this
  | succ n ih =>
    intro x
    have h := hasSum_pow_div_factorial_exp (x 0)
    have ht := ih (Fin.tail x)
    have h1 : Summable (fun i => ‖x 0 ^ i / (i.factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 h.summable
    have h2 : Summable (fun f : Fin n → ℕ => ‖∏ k, Fin.tail x k ^ f k / ((f k).factorial : ℂ)‖) :=
      (summable_norm_iff (E := ℂ)).2 ht.summable
    have h0 := summable_mul_of_summable_norm h1 h2
    have h3 := HasSum.mul h ht h0
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff, Fin.sum_univ_succ,
      Complex.exp_add]
    convert h3 using 1
    all_goals first
      | rfl
      | (funext p; simp [Fin.prod_univ_succ, Fin.consEquiv, Fin.tail] <;> ring)

theorem hasSum_finsupp_prod_pow_div_factorial_exp : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ),
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
  intro κ _ x
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hA := hasSum_fin_prod_pow_div_factorial_exp (Fintype.card κ) (fun i => x (e.symm i))
  have hsum : (∑ i, x (e.symm i)) = ∑ k, x k := Equiv.sum_comp e.symm x
  rw [hsum] at hA
  have hB : HasSum (fun f : κ → ℕ => ∏ k, x k ^ f k / ((f k).factorial : ℂ))
      (Complex.exp (∑ k, x k)) := by
    rw [← ((Equiv.arrowCongr e (Equiv.refl ℕ)).symm).hasSum_iff]
    convert hA using 1
    funext g
    simp only [Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
      Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, Function.comp_def, id]
    exact (Equiv.prod_comp e.symm (fun k => x k ^ g (e k) / ((g (e k)).factorial : ℂ))).symm.trans
      (by simp)
  rw [← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).symm.hasSum_iff]
  convert hB using 1
  funext f
  simp only [Function.comp_apply]
  rw [Finsupp.prod_fintype]
  · simp
  · intro i; simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumFinsuppProdPowDivFactorialExpStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum : ∀ (κ : Type) [Fintype κ] (x : κ → ℂ), HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℂ)) (Complex.exp (∑ k, x k)) := by
  first | exact @GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp | exact GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp | (intros; apply GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockBargmannReproducingFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockRepr

theorem expand_real (κ : Type) [Fintype κ] (x : κ → ℝ) :
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℝ)) (Real.exp (∑ k, x k)) := by
  have h := GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum κ (fun k => (x k : ℂ))
  rw [← Complex.ofReal_sum, ← Complex.ofReal_exp] at h
  refine Complex.hasSum_ofReal.mp ?_
  convert h using 1
  funext m
  simp [Finsupp.prod]

theorem conjMono_continuous {ι : Type} [Fintype ι] {a b : ℕ} (m : DVar ι a b →₀ ℕ) : Continuous (conjMono m) := by
  unfold conjMono Finsupp.prod; fun_prop

theorem gq_continuous {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) : Continuous (gq (a := a) (b := b) c) := by
  unfold gq; fun_prop

theorem bargmann_repr : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ z₀
  have hbk : ∀ z, bk c z₀ z = ∑ k : DVar ι a b, (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2) := by
    intro z; simp only [bk, Fintype.sum_prod_type]
  let coef : (DVar ι a b →₀ ℕ) → ℂ := fun m => m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2) ^ n / (n.factorial : ℂ)
  have hcm : ∀ (m : DVar ι a b →₀ ℕ) z, coef m * conjMono m z = m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ) := by
    intro m z
    simp only [coef, conjMono, ← Finsupp.prod_mul]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
  let F : (DVar ι a b →₀ ℕ) → VCx ι a b → ℂ := fun m z => coef m * (conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hlim : ∀ z, HasSum (fun m => F m z) (Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) := by
    intro z
    have := (GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum (DVar ι a b) (fun k => (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2))).mul_right ((Real.exp (-gq c z) : ℂ) * G z)
    rw [← hbk] at this
    have e : (fun m => F m z) = fun m => (m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ)) * ((Real.exp (-gq c z) : ℂ) * G z) := by
      funext m
      rw [← hcm]
      simp only [F]
      ring
    rw [e, mul_assoc]
    exact this
  have hnorm : ∀ m z, ‖F m z‖ = (m.prod fun k n => (‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) ^ n / (n.factorial : ℝ)) * (Real.exp (-gq c z) * ‖G z‖) := by
    intro m z
    have e1 : F m z = (coef m * conjMono m z) * ((Real.exp (-gq c z) : ℂ) * G z) := by simp only [F]; ring
    rw [e1, hcm, norm_mul, norm_mul, Finsupp.prod, Finsupp.prod, norm_prod, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hnsum : ∀ z, HasSum (fun m => ‖F m z‖) (Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)) := by
    intro z
    simp only [hnorm]
    exact (expand_real (DVar ι a b) _).mul_right _
  have hGc : Continuous G := hG.continuous
  have hFc : ∀ m, Continuous (F m) := by
    intro m
    have h1 := conjMono_continuous m
    have h2 := gq_continuous (a := a) (b := b) c
    simp only [F]
    fun_prop
  have hS : Continuous fun z : VCx ι a b => ∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖ := by
    fun_prop
  have hint : Integrable (fun z => ∑' m, ‖F m z‖) := by
    have e : (fun z => ∑' m, ‖F m z‖) = fun z => Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖) := by
      funext z; exact (hnsum z).tsum_eq
    rw [e]
    refine ((GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix ι a b c hc z₀).const_mul M).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h2 := gq_continuous (a := a) (b := b) c
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hz := hM z
      calc Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)
          ≤ Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * (M * Real.exp (gq c z / 2))) := by
            gcongr
        _ = M * Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
            rw [show (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2
              = (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) + (-gq c z) + gq c z / 2 by ring,
              Real.exp_add, Real.exp_add]
            ring
  have hsumI : HasSum (fun m => ∫ z, F m z) (∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) :=
    hasSum_integral_of_dominated_convergence (fun m z => ‖F m z‖) (fun m => (hFc m).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall fun z => le_rfl) (Filter.Eventually.of_forall fun z => (hnsum z).summable)
      hint (Filter.Eventually.of_forall hlim)
  set P : ℝ := ∏ τ, (Real.pi / c τ) ^ (a * b) with hP
  have hFm : ∀ m, ∫ z, F m z = (P : ℂ) * ((m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) := by
    intro m
    simp only [F]
    rw [MeasureTheory.integral_const_mul, GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient ι a b c hc G hG ⟨M, hM⟩ m]
    have hc' : coef m * (((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ)) : ℂ) = m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ) := by
      simp only [coef, Finsupp.prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (c k.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hc k.1).ne'
      push_cast
      rw [mul_pow, mul_div_assoc, mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ this, one_pow, one_mul]
    rw [← hc']
    ring
  have hT := (GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace ι a b G hG z₀).mul_left (P : ℂ)
  simp only [← hFm] at hT
  have heq := hsumI.unique hT
  rw [heq, ← mul_assoc]
  have h1 : (∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) * P = 1 := by
    rw [hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← mul_pow]
    have : c τ ≠ 0 := (hc τ).ne'
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [show c τ / Real.pi * (Real.pi / c τ) = 1 by field_simp, one_pow]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

end GlobalTheory.FockRepr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockBargmannReproducingFormulaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_bargmann_reproducing_formula : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  first | exact @GlobalTheory.FockRepr.bargmann_repr | exact GlobalTheory.FockRepr.bargmann_repr | (intros; apply GlobalTheory.FockRepr.bargmann_repr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMoments
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMoments
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

section BargmannUnique

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem bk_smul_left (c : ι → ℝ) (u : ℂ) (z₀ z : VCx ι a b) : bk c (u • z₀) z = u * bk c z₀ z := by
  unfold bk
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem conjMono_add (m m' : DVar ι a b →₀ ℕ) (z : VCx ι a b) :
    conjMono (m + m') z = conjMono m z * conjMono m' z := by
  unfold conjMono
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem conjMono_single_one (k : DVar ι a b) (z : VCx ι a b) :
    conjMono (Finsupp.single k 1) z = conj (z k.1 k.2.1 k.2.2) := by
  unfold conjMono; simp [Finsupp.prod_single_index]

abbrev monoSpan (ι : Type) [Fintype ι] (a b : ℕ) : Submodule ℂ (VCx ι a b → ℂ) :=
  Submodule.span ℂ (Set.range fun m : DVar ι a b →₀ ℕ => conjMono m)

theorem monoSpan_mul {P Q : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) (hQ : Q ∈ monoSpan ι a b) :
    P * Q ∈ monoSpan ι a b := by
  have h := Submodule.mul_mem_mul hP hQ
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
  exact ⟨m + m', funext fun z => conjMono_add m m' z⟩

theorem bk_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) : (fun z => bk c z₀ z) ∈ monoSpan ι a b := by
  have : (fun z => bk c z₀ z) = ∑ τ, ∑ i, ∑ j,
      ((c τ : ℂ) * z₀ τ i j) • conjMono (Finsupp.single (τ, i, j) 1) := by
    funext z
    simp only [bk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conjMono_single_one]
  rw [this]
  exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem bk_pow_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) (n : ℕ) :
    (fun z => bk c z₀ z ^ n) ∈ monoSpan ι a b := by
  induction n with
  | zero =>
    have : (fun z : VCx ι a b => bk c z₀ z ^ 0) = conjMono 0 := by funext z; simp [conjMono]
    rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have := monoSpan_mul ih (bk_mem_monoSpan c z₀)
    convert this using 1
    funext z; simp [pow_succ]

theorem exp_norm_le_four (w : ℂ) : Real.exp ‖w‖ ≤ Real.exp ((1 - Complex.I) * w).re +
    Real.exp ((1 + Complex.I) * w).re + Real.exp ((-1 - Complex.I) * w).re + Real.exp ((-1 + Complex.I) * w).re := by
  have h1 : ((1 - Complex.I) * w).re = w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h2 : ((1 + Complex.I) * w).re = w.re + -w.im := by simp [Complex.mul_re] <;> ring
  have h3 : ((-1 - Complex.I) * w).re = -w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h4 : ((-1 + Complex.I) * w).re = -w.re + -w.im := by simp [Complex.mul_re] <;> ring
  rw [h1, h2, h3, h4]
  have key : Real.exp ‖w‖ ≤ Real.exp |w.re| * Real.exp |w.im| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (Complex.norm_le_abs_re_add_abs_im w)
  have hre : Real.exp |w.re| ≤ Real.exp w.re + Real.exp (-w.re) := by
    rcases abs_cases w.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.re, Real.exp_pos (-w.re)]
  have him : Real.exp |w.im| ≤ Real.exp w.im + Real.exp (-w.im) := by
    rcases abs_cases w.im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.im, Real.exp_pos (-w.im)]
  calc Real.exp ‖w‖ ≤ (Real.exp w.re + Real.exp (-w.re)) * (Real.exp w.im + Real.exp (-w.im)) :=
        key.trans (mul_le_mul hre him (by positivity) (by positivity))
    _ = _ := by simp only [add_mul, mul_add, ← Real.exp_add]; ring

theorem integral_moment_span_eq_zero {c : ι → ℝ} (hc : ∀ τ, 0 < c τ) {F : VCx ι a b → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ z, ‖F z‖ ≤ M)
    (hmom : ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0)
    {P : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) :
    Integrable (fun z => P z * (Real.exp (-gq c z / 2) : ℂ) * F z) ∧
      ∫ z, P z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).1 m).mul_bdd hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hM), hmom m⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (fun z => (x + y) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => x z * (Real.exp (-gq c z / 2) : ℂ) * F z + y z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul r x _ hx =>
    have e : (fun z => (r • x) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => r * (x z * (Real.exp (-gq c z / 2) : ℂ) * F z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact ⟨hx.1.const_mul r, by rw [integral_const_mul, hx.2, mul_zero]⟩

theorem integral_bargmann_eq_zero_of_moments : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  intro ι _ a b c hc F hF hMex hmom z₀
  obtain ⟨M, hM⟩ := hMex
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x) := fun x => by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hgq : Continuous (fun z : VCx ι a b => gq c z) := by unfold gq; fun_prop
  have hbk : Continuous (fun z : VCx ι a b => bk c z₀ z) := by unfold bk; fun_prop
  have hg : Continuous (fun z : VCx ι a b => ((Real.exp (-gq c z / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hgq.neg.div_const 2))
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (f := fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (fun n z => ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M))
    (fun n => ((((hbk.pow n).div_const _).mul hg).mul hF).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc]
      gcongr
      exact hM z)
    (Filter.Eventually.of_forall fun z => (hexpR ‖bk c z₀ z‖).summable.mul_right _)
    (by
      have htsum : (fun z => ∑' n : ℕ, ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M)) =
          fun z => Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M) := by
        funext z; rw [tsum_mul_right, (hexpR _).tsum_eq]
      rw [htsum]
      have hI : ∀ u : ℂ, Integrable fun z : VCx ι a b =>
          ‖Complex.exp (bk c (u • z₀) z) * (Real.exp (-gq c z / 2) : ℂ)‖ :=
        fun u => ((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).2 (u • z₀)).norm
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      refine Integrable.mono' ((((hI (1 - Complex.I)).add (hI (1 + Complex.I))).add
        (hI (-1 - Complex.I))).add (hI (-1 + Complex.I)) |>.const_mul M)
        ((Real.continuous_exp.comp (continuous_norm.comp hbk)).mul
          ((Real.continuous_exp.comp (hgq.neg.div_const 2)).mul continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, bk_smul_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by positivity)]
      have h4 := exp_norm_le_four (bk c z₀ z)
      have he := Real.exp_pos (-gq c z / 2)
      calc Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M)
          = (M * Real.exp (-gq c z / 2)) * Real.exp ‖bk c z₀ z‖ := by ring
        _ ≤ (M * Real.exp (-gq c z / 2)) * (Real.exp ((1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((1 + Complex.I) * bk c z₀ z).re + Real.exp ((-1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((-1 + Complex.I) * bk c z₀ z).re) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun z => by
      simpa only [mul_assoc] using (hexpC (bk c z₀ z)).mul_right ((Real.exp (-gq c z / 2) : ℂ) * F z))
  have h0 : ∀ n : ℕ, ∫ z, bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
    intro n
    have := (integral_moment_span_eq_zero hc hF hM hmom
      (Submodule.smul_mem _ ((Nat.factorial n : ℂ)⁻¹) (bk_pow_mem_monoSpan c z₀ n))).2
    have e : (fun z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => ((Nat.factorial n : ℂ)⁻¹ • fun z => bk c z₀ z ^ n) z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact this
  simp only [h0] at hsum
  exact hsum.unique hasSum_zero

end BargmannUnique

end GlobalTheory.FockTransl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMomentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_exp_bk_mul_eq_zero_of_moments_zero : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  first | exact @GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments | exact GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments | (intros; apply GlobalTheory.FockTransl.integral_bargmann_eq_zero_of_moments <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslates
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FockTransl

open Formalism.L2.Ker (VCx DVar derivAt0)

theorem tame_kills_real_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ →
    ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) →
    ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  intro D ψ θ hψ hθ S T A B ℓ hℓ f hf hP w hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hcont, hsurj, htr⟩ := GlobalTheory.T.fockRealPoint_transport_continuous_integral D θ σ hσ S T A B
  obtain ⟨z₀, rfl⟩ := hsurj w hw
  have hth := hf.1
  set F : VCx D.what₂.Tau S.rank T.rank → ℂ := fun z => ℓ (heisO ψ S T (fockPt σ A B z) f) with hFdef
  have hFc : Continuous F := (hℓ.cont f hth).comp hcont
  obtain ⟨M, hM⟩ := hℓ.bdd f hth
  have hFb : ∃ M : ℝ, ∀ z, ‖F z‖ ≤ M := ⟨M, fun z => hM _⟩
  have key : ∀ g : VCx D.what₂.Tau S.rank T.rank → ℂ, Integrable g →
      IsThetaFunO ψ S T (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) →
      ℓ (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = ∫ z, g z * F z := by
    intro g hg hthg
    obtain ⟨m, α, hm, hα, hH⟩ := htr g hg
    have e1 : (fun x => ∫ z, g z * heisO ψ S T (fockPt σ A B z) f x) = fun x => ∫ w, α w * heisO ψ S T w f x ∂m := by
      funext x; exact (hH fun w => heisO ψ S T w f x).symm
    rw [e1] at hthg ⊢
    rw [hℓ.sup f hth m α hα hthg]
    exact hH fun w => ℓ (heisO ψ S T w f)
  obtain ⟨C, hC⟩ := ((GlobalTheory.ThetaSquare.squareIntegrable hψ) f hth).2.1
  have hG : ∀ x, ∃ M : ℝ, ∀ z, ‖rd ψ σ A B f x z‖ ≤ M * Real.exp (gq (fw D) z / 2) := by
    intro x
    refine ⟨C, fun z => ?_⟩
    rw [rd, norm_mul, GlobalTheory.ThetaSquare.norm_heisO hψ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  have hent := GlobalTheory.T.fockGaussianReading_differentiable D ψ θ σ hψ hσ S T A B f hf
  have hc : ∀ τ, 0 < fw D τ := fw_pos D
  obtain ⟨hint1, hint2⟩ := GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian D.what₂.Tau S.rank T.rank (fw D) hc
  have hgq : ∀ z : VCx D.what₂.Tau S.rank T.rank, ∀ x, (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z =
      (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x := by
    intro z x
    rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring

  obtain ⟨Cj, hCj⟩ := GlobalTheory.T.fock_gaussian_jets_at_origin_eq_fock_vectors D ψ θ σ hψ hσ S T A B
  have hpt : ∀ P, IsThetaFunO ψ S T (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    fun P => GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hth P
  have hmom : ∀ m : DVar D.what₂.Tau S.rank T.rank →₀ ℕ,
      ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * F z = 0 := by
    intro m
    set K : ℂ := ((∏ τ, (Real.pi / fw D τ) ^ (S.rank * T.rank) : ℝ) : ℂ) *
      ((m.prod fun k n => (fw D k.1)⁻¹ ^ n : ℝ) : ℂ) with hK
    have e : (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
        (K * Cj m) • GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) := by
      funext x
      have h1 := GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) m
      rw [hCj f hf x m] at h1
      have h2 : (fun z => conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z) f x) =
          fun z => conjMono m z * (Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z := by
        funext z; rw [mul_assoc, mul_assoc, hgq]
      rw [h2, h1, Pi.smul_apply, smul_eq_mul]
      ring
    have hthe : IsThetaFunO ψ S T (fun x => ∫ z, conjMono m z * (Real.exp (-gq (fw D) z / 2) : ℂ) *
        heisO ψ S T (fockPt σ A B z) f x) := by
      rw [e]
      exact GlobalTheory.OrientedHeis.theta_smul _ (hpt _)
    have := key _ (hint1 m) hthe
    rw [← this, e, hℓ.smul _ _ (hpt _), hP, mul_zero]

  have hU := GlobalTheory.T.integral_exp_bk_mul_eq_zero_of_moments_zero D.what₂.Tau S.rank T.rank (fw D) hc F hFc hFb hmom z₀
  set K' : ℂ := ((∏ τ, (fw D τ / Real.pi) ^ (S.rank * T.rank) : ℝ) : ℂ) * (Real.exp (-gq (fw D) z₀ / 2) : ℂ) with hK'
  have e : (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) = heisO ψ S T (fockPt σ A B z₀) f := by
    funext x
    have h1 := GlobalTheory.T.fock_bargmann_reproducing_formula D.what₂.Tau S.rank T.rank (fw D) hc (rd ψ σ A B f x) (hent x) (hG x) z₀
    have h2 : heisO ψ S T (fockPt σ A B z₀) f x = (Real.exp (-gq (fw D) z₀ / 2) : ℂ) * rd ψ σ A B f x z₀ := by
      rw [rd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      rw [show -gq (fw D) z₀ / 2 + gq (fw D) z₀ / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [h2, h1]
    have h3 : (fun z => (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
        heisO ψ S T (fockPt σ A B z) f x) = fun z => K' * (Complex.exp (bk (fw D) z₀ z) *
          ((Real.exp (-gq (fw D) z) : ℂ) * rd ψ σ A B f x z)) := by
      funext z; rw [hgq]; ring
    rw [h3, integral_const_mul, hK']
    simp only [mul_assoc]
    ring
  have hthe : IsThetaFunO ψ S T (fun x => ∫ z, (K' * (Complex.exp (bk (fw D) z₀ z) * (Real.exp (-gq (fw D) z / 2) : ℂ))) *
      heisO ψ S T (fockPt σ A B z) f x) := by
    rw [e]; exact (GlobalTheory.ThetaSquare.heisUnitary hψ).2.2.1 _ _ hth
  have := key _ ((hint2 z₀).const_mul K') hthe
  rw [e] at this
  change ℓ (heisO ψ S T (fockPt σ A B z₀) f) = 0
  rw [this]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  simp_rw [← mul_assoc] at hU ⊢
  rw [hU, mul_zero]

end GlobalTheory.FockTransl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalKillsFockVacuumRealTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameFunctional_kills_fockVacuum_realTranslates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (ℓ : (WO S T → ℂ) → ℂ), Tame ψ S T ℓ → ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → (∀ P, ℓ (GlobalTheory.ChainFr.ptF ψ θ A B f P) = 0) → ∀ w : WO S T, w.map (finPart D) = 0 → ℓ (heisO ψ S T w f) = 0 := by
  first | exact @GlobalTheory.FockTransl.tame_kills_real_translates | exact GlobalTheory.FockTransl.tame_kills_real_translates | (intros; apply GlobalTheory.FockTransl.tame_kills_real_translates <;> assumption)
end
