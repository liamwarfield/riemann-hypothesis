module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionOfSubCoefficients

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology

noncomputable section

section Param

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type} [Fintype ι]

private theorem norm_fderiv_le_of_differentiableOn_ball_of_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : F → ℂ} {x0 x : F} {ρ C : ℝ} (hρ : 0 < ρ) (hf : DifferentiableOn ℂ f (ball x0 ρ))
    (hC : ∀ z ∈ ball x0 ρ, ‖f z‖ ≤ C) (hx : x ∈ ball x0 (ρ / 2)) :
    ‖fderiv ℂ f x‖ ≤ C / (ρ / 2) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x0 (mem_ball_self hρ))
  have hx1 : ‖x - x0‖ < ρ / 2 := mem_ball_iff_norm.mp hx
  have hxd : DifferentiableAt ℂ f x :=
    hf.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R := ρ / 2 / ‖v‖ with hRdef
  have hR : 0 < R := by positivity
  have hRv : R * ‖v‖ = ρ / 2 := div_mul_cancel₀ _ hvpos.ne'
  have hmem : ∀ w : ℂ, ‖w‖ ≤ R → x + w • v ∈ ball x0 ρ := by
    intro w hw
    rw [mem_ball_iff_norm]
    have h2 : ‖w • v‖ ≤ ρ / 2 := by
      rw [norm_smul, ← hRv]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg v)
    have h3 : x + w • v - x0 = (x - x0) + w • v := by abel
    rw [h3]
    calc _ ≤ ‖x - x0‖ + ‖w • v‖ := norm_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add_of_lt_of_le hx1 h2
      _ = ρ := by ring
  have hgd : DifferentiableOn ℂ (fun w : ℂ => f (x + w • v)) (closedBall 0 R) := by
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    have hfa : DifferentiableAt ℂ f (x + w • v) :=
      hf.differentiableAt (isOpen_ball.mem_nhds (hmem w hw'))
    exact (hfa.comp w ((differentiableAt_id.smul_const v).const_add x)).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun w : ℂ => f (x + w • v)) (ball 0 R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    exact hgd
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (le_of_eq (mem_sphere_zero_iff_norm.mp hz))))
  have hline : HasDerivAt (fun w : ℂ => x + w • v) ((1 : ℂ) • v) 0 :=
    ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hfd : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact hxd.hasFDerivAt
  have hg := hfd.comp_hasDerivAt (0 : ℂ) hline
  rw [one_smul] at hg
  have hder : deriv (fun w : ℂ => f (x + w • v)) 0 = fderiv ℂ f x v := hg.deriv
  rw [hder] at hcau
  calc ‖fderiv ℂ f x v‖ ≤ C / R := hcau
    _ = C / (ρ / 2) * ‖v‖ := by
      rw [hRdef]
      field_simp

theorem diffOn_param_bdd {K : Set (ι → ℝ)} (hKv : volume K < ⊤)
    (A : (ι → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (ι → ℝ) → ℂ) (he : Continuous e) (he1 : ∀ t, ‖e t‖ ≤ 1)
    (hbd : ∀ x0 ∈ U, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ U ∧
      ∀ t, ∀ z ∈ closedBall x0 ρ, ‖G (A t z)‖ ≤ C) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  obtain ⟨ρ, hρ, C, hsub, hC⟩ := hbd x0 hx0
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hKv.ne
  have hballU : ball x0 ρ ⊆ U := ball_subset_closedBall.trans hsub
  have hslice : ∀ t, DifferentiableOn ℂ (fun z => G (A t z)) U := fun t =>
    hG.comp (A t).differentiable.differentiableOn (fun z hz => hAU t z hz)
  have hAx : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  have hcont : ∀ x ∈ U, Continuous fun t => G (A t x) * e t := fun x hx =>
    (hG.continuousOn.comp_continuous (hAx x) (fun t => hAU t x hx)).mul he
  have hfd : ∀ t, ∀ x ∈ U, HasFDerivAt (fun z => G (A t z) * e t)
      (e t • fderiv ℂ (fun z => G (A t z)) x) x := fun t x hx =>
    ((hslice t).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.mul_const (e t)
  have hF'eq : (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0) =
      fun t => e t • (fderiv ℂ G (A t x0)).comp (A t) := by
    funext t
    congr 1
    have hGd : DifferentiableAt ℂ G (A t x0) := hG.differentiableAt (hU.mem_nhds (hAU t x0 hx0))
    exact fderiv_comp x0 hGd (A t).differentiableAt |>.trans (by rw [(A t).fderiv])
  have hmeasF' : AEStronglyMeasurable (fun t => e t • fderiv ℂ (fun z => G (A t z)) x0)
      (volume.restrict K) := by
    rw [hF'eq]
    refine he.aestronglyMeasurable.smul ?_
    letI : MeasurableSpace (F →L[ℂ] ℂ) := borel _
    haveI : BorelSpace (F →L[ℂ] ℂ) := ⟨rfl⟩
    have hm : Measurable (fderiv ℂ G) := measurable_fderiv ℂ G
    have h1 : AEStronglyMeasurable (fun t => fderiv ℂ G (A t x0)) (volume.restrict K) :=
      (hm.comp (hAx x0).measurable).aestronglyMeasurable
    exact (ContinuousLinearMap.compL ℂ F F ℂ).aestronglyMeasurable_comp₂ h1 hA.aestronglyMeasurable
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t) (F' := fun x t => e t • fderiv ℂ (fun z => G (A t z)) x)
    (bound := fun _ => C / (ρ / 2)) (x₀ := x0) (ball_mem_nhds x0 (half_pos hρ))
    (Filter.eventually_of_mem (hU.mem_nhds hx0) fun x hx => (hcont x hx).aestronglyMeasurable)
    ((integrable_const C).mono' (hcont x0 hx0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        calc ‖G (A t x0)‖ * ‖e t‖ ≤ C * 1 :=
              mul_le_mul (hC t x0 (mem_closedBall_self hρ.le)) (he1 t) (norm_nonneg _)
                ((norm_nonneg _).trans (hC t x0 (mem_closedBall_self hρ.le)))
          _ = C := mul_one C))
    hmeasF'
    (Filter.Eventually.of_forall fun t x hx => by
      rw [norm_smul]
      have hb := norm_fderiv_le_of_differentiableOn_ball_of_norm_le hρ ((hslice t).mono hballU)
        (fun z hz => hC t z (ball_subset_closedBall hz)) hx
      have hC0 : 0 ≤ C / (ρ / 2) := (norm_nonneg _).trans hb
      calc ‖e t‖ * ‖fderiv ℂ (fun z => G (A t z)) x‖ ≤ 1 * (C / (ρ / 2)) :=
            mul_le_mul (he1 t) hb (norm_nonneg _) zero_le_one
        _ = C / (ρ / 2) := one_mul _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun t x hx =>
      hfd t x (hballU (ball_subset_ball (by linarith) hx)))
  exact key.differentiableAt.differentiableWithinAt

end Param

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def flowL (ξ : Fin r → E) (s : X.Ψ → ℝ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.flow ξ (fun τ => (s τ : ℂ))
      map_add' x y := by
        funext τ
        show X.flowMat ξ τ (s τ : ℂ) * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.flowMat ξ τ (s τ : ℂ) * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }

lemma flowL_apply (ξ : Fin r → E) (s : X.Ψ → ℝ) (x : Frame X.Ψ r) :
    flowL X ξ s x = X.flow ξ (fun τ => (s τ : ℂ)) x := rfl

lemma cont_flowL (ξ : Fin r → E) : Continuous fun s => flowL X ξ s := by
  apply continuous_clm_apply.mpr
  intro x
  simp only [flowL_apply]
  unfold Data.flow
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.mul_apply, Data.flowMat, Matrix.of_apply]
  first
  | fun_prop
  | continuity

lemma cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor
  apply Continuous.matrix_det
  apply Continuous.matrix_submatrix
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gram, Matrix.of_apply, hermC, col, mat]
  first
  | fun_prop
  | continuity

lemma continuousAt_nfac (la : Wt X.Ψ r) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ContinuousAt (X.nfac la) x0 := by
  have h : ∀ (τ : X.Ψ) (i : Fin r), ContinuousAt (fun x : Frame X.Ψ r =>
      ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)) x0 := by
    intro τ i
    have hd1 := (cont_dmin X τ i.succ).continuousAt (x := x0)
    have hd2 := (cont_dmin X τ i.castSucc).continuousAt (x := x0)
    have hne1 := FlowCoefficientBounds.dmin_ne X hx0 τ i.succ
    have hne2 := FlowCoefficientBounds.dmin_ne X hx0 τ i.castSucc
    exact (hd1.div hd2 hne2).norm.rpow_const (Or.inl (norm_ne_zero_iff.mpr (div_ne_zero hne1 hne2)))
  unfold Data.nfac
  exact tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => h τ i

private theorem isOpen_dom_upper_bounds : IsOpen X.dom := by
  have hset : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [Data.dom, GG]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun
      ((show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det)
      continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (cont_dmin X τ i)))

lemma fj_hbd (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) : ∀ x0 ∈ X.dom, ∃ ρ > 0, ∃ C, closedBall x0 ρ ⊆ X.dom ∧
      ∀ t : X.Ψ → ℝ, ∀ z ∈ closedBall x0 ρ, ‖P (flowL X ξ t z)‖ ≤ C := by
  intro x0 hx0
  obtain ⟨-, C, hC⟩ := hP
  have hpos := FlowCoefficientBounds.nfac_pos X hx0 la
  have hcont := continuousAt_nfac X la hx0
  have hev : ∀ᶠ z in 𝓝 x0, X.nfac la x0 / 2 < X.nfac la z ∧ z ∈ X.dom :=
    (hcont.eventually (lt_mem_nhds (by linarith : X.nfac la x0 / 2 < X.nfac la x0))).and
      ((isOpen_dom_upper_bounds X).mem_nhds hx0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ρ / 2, by positivity, 2 * C / X.nfac la x0, ?_, ?_⟩
  · intro z hz
    exact (hball (Metric.closedBall_subset_ball (by linarith) hz)).2
  · intro t z hz
    have hz' := hball (Metric.closedBall_subset_ball (by linarith) hz)
    obtain ⟨hfd, hfn⟩ := FlowCoefficientBounds.flow_real X hξ hz'.2 t la
    have h1 := hC _ hfd
    rw [flowL_apply]
    have h2 : X.pnorm la P (X.flow ξ (fun τ => (t τ : ℂ)) z) =
        ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z := by
      rw [← hfn]
      rfl
    rw [h2] at h1
    have h3 : ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * (X.nfac la x0 / 2) ≤
        ‖P (X.flow ξ (fun τ => (t τ : ℂ)) z)‖ * X.nfac la z :=
      mul_le_mul_of_nonneg_left hz'.1.le (norm_nonneg _)
    rw [le_div_iff₀ hpos]
    linarith

theorem fj_diffOn (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) : DifferentiableOn ℂ (X.fj la ξ ν P) X.dom := by
  unfold Data.fj
  split_ifs with h1 h2
  · apply DifferentiableOn.const_mul
    have he1 : ∀ s : X.Ψ → ℝ, ‖cexp (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ))‖ ≤ 1 := by
      intro s
      have hre : -(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ) =
          ((-(4 * Real.pi * ∑ τ, ν τ * s τ) : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [hre, Complex.norm_exp_ofReal_mul_I]
    have hec : Continuous fun s : X.Ψ → ℝ => cexp (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)) := by
      first
      | fun_prop
      | continuity
    exact diffOn_param_bdd h2.choose_spec.2.2.2 (flowL X ξ) (cont_flowL X ξ) (isOpen_dom_upper_bounds X)
      (fun t x hx => (FlowCoefficientBounds.flow_real X hξ hx t la).1) P hP.1.1 _ hec he1 (fj_hbd X la P hP hξ)
  · exact differentiableOn_const 0
  · exact differentiableOn_const 0

end Frame

end

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionHolds
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficientConvolution_holds : CoefficientConvolution (E := E) :=
  PeriodLatticeMembership.coefficientConvolution_of_subCoefficients (fun r X la P hP ξ hξ x hx ω hωp hωi k ν hk =>
    SublatticeCoefficients.subCoeff X la P hP ξ hξ x hx ω hωp hωi k ν hk)

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowBlock
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NsqMulVecLeOpN
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def nsq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2

lemma nsq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v := by
  unfold nsq
  positivity

lemma nsq_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) * nsq v := by
  unfold nsq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖A.mulVec v i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  calc ‖A.mulVec v i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma opN_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    BddAbove {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
      t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
  refine ⟨Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2), ?_⟩
  rintro t ⟨v, -, rfl⟩
  have hF : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  have key := nsq_mulVec_le A v
  have hb : 0 ≤ nsq v := nsq_nonneg v
  unfold nsq at key hb
  rcases hb.eq_or_lt with h | h
  · rw [← h]
    simp
  · rw [div_le_iff₀ (Real.sqrt_pos.2 h), ← Real.sqrt_mul hF]
    exact Real.sqrt_le_sqrt key

lemma opN_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro t ⟨v, -, rfl⟩
  positivity

lemma nsq_mulVec_le_opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ Data.opN A ^ 2 * nsq v := by
  by_cases hv : v = 0
  · subst hv
    simp [nsq, Matrix.mulVec_zero]
  have hmem : Real.sqrt (nsq (A.mulVec v)) / Real.sqrt (nsq v) ≤ Data.opN A :=
    le_csSup (opN_bdd A) ⟨v, hv, rfl⟩
  have hpos : 0 < nsq v := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    unfold nsq
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2)
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j))
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)] at hmem
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hmem 2
  rwa [mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt hpos.le] at h2

lemma opN_le_zN {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Z : X.Coord) (τ : X.Ψ) : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
  unfold Data.zN
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma sum_split (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  set g : ℕ → ℂ := fun i => if h : i < r then f ⟨i, h⟩ else 0 with hg
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, dif_pos j.isLt]
  have e2 : ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range (X.p0 + (r - X.p0)), g i := by
    rw [Nat.add_sub_cancel' X.p0_le]
  rw [e1, e2, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha : (a : ℕ) < r := lt_of_lt_of_le a.isLt X.p0_le
    simp only [hg, dif_pos ha]
    rfl
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; have := X.p0_le; omega
    simp only [hg, dif_pos hm]

def nI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩

private lemma nI_val_eq_p0_add (m : Fin (r - X.p0)) : ((nI X m : Fin r) : ℕ) = X.p0 + m := rfl

lemma L_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) = if a = c then 1 else 0 := by
  have ha := a.isLt
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0) := by
    simp only [Fin.val_castLE]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : a = c
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.castLE_injective X.p0_le e))]

lemma L_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (nI X m) = 0 := by
  have ha := a.isLt
  have h1 : (Fin.castLE X.p0_le a : Fin r) ≠ nI X m := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((nI X m : Fin r) : ℕ) < X.p0) := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_neg h2, add_zero]

lemma L_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    X.lowBlock Z τ (nI X m) (Fin.castLE X.p0_le c) = Z τ m c := by
  have hc := c.isLt
  have h1 : nI X m ≠ (Fin.castLE X.p0_le c : Fin r) := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_pos h2, zero_add]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [nI_val_eq_p0_add])) (Fin.ext (by simp))

lemma L_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    X.lowBlock Z τ (nI X m) (nI X m') = if m = m' then 1 else 0 := by
  have h2 : ¬ (X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((nI X m' : Fin r) : ℕ) < X.p0) := by
    rw [nI_val_eq_p0_add, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : m = m'
  · subst h
    simp
  · have h1 : nI X m ≠ nI X m' := by
      intro e
      have h' := congrArg Fin.val e
      rw [nI_val_eq_p0_add, nI_val_eq_p0_add] at h'
      exact h (Fin.ext (by omega))
    rw [if_neg h, if_neg h1]

lemma sgn_p (a : Fin X.p0) : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, a.isLt]

lemma sgn_n (m : Fin (r - X.p0)) : sgn X.p0 ((nI X m : Fin r) : ℕ) = -1 := by
  rw [nI_val_eq_p0_add]
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn]

def Gp (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (X.lowBlock Z τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
    (X.lowBlock Z τ).map (starRingEnd ℂ)

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma gram_xZ {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := by
  have h := ho τ
  rw [gram_eq_upper_bounds] at h
  have hm : mat (X.xZ x Z) τ = mat x τ * X.lowBlock Z τ := rfl
  rw [gram_eq_upper_bounds, hm, Gp, ← h, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

lemma Gp_apply (Z : X.Coord) (τ : X.Ψ) (a c : Fin r) :
    Gp X Z τ a c = ∑ j, X.lowBlock Z τ j a * ((sgn X.p0 (j : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ j c) := by
  rw [Gp, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

private lemma sum_eq_sum_castLE_add_sum_nI (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) :=
  sum_split X f

lemma Gp_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    Gp X Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) =
      (if a = c then 1 else 0) - ∑ m, Z τ m a * conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_np X, sgn_p X, sgn_n X]
  by_cases hac : a = c
  · subst hac
    simp [sub_eq_add_neg]
  · simp [hac, Ne.symm hac, sub_eq_add_neg]

lemma Gp_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    Gp X Z τ (nI X m) (Fin.castLE X.p0_le c) = -conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

lemma Gp_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    Gp X Z τ (Fin.castLE X.p0_le a) (nI X m) = -Z τ m a := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

lemma Gp_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    Gp X Z τ (nI X m) (nI X m') = -(if m = m' then 1 else 0) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_nn X, sgn_p X, sgn_n X]
  by_cases h : m = m'
  · subst h
    simp
  · simp [h, Ne.symm h]

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end
