module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
noncomputable section

namespace GlobalTheory.SUChartSection

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def gsU (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  FrameDegreeData.uMat (PoinPf.Gw X w τ)

def gsS (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) : ℝ :=
  (Real.sqrt |(((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re|)⁻¹

def gsB (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  gsU X w τ * Matrix.diagonal fun k => ((gsS X w τ k : ℝ) : ℂ)

def yM (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat (nmat X w) τ * gsB X w τ

def yF (X : Data E r) (w : V (nd X)) : X.Ψ → Fin r → Fin r → ℂ := fun τ a b => yM X w τ a b

def dY (X : Data E r) : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) := fderiv ℝ (yF X) 0

def secM (X : Data E r) (x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat x τ * yM X w τ * (mat x τ)⁻¹

theorem gram_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (cpt X x w) τ) = PoinPf.Gw X w τ := by
  show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

theorem bOf_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) :
    FrameDegreeData.bOf X (cpt X x w) = fun τ => gsB X w τ := by
  funext τ
  simp only [FrameDegreeData.bOf, FrameDegreeData.uOf, gram_cpt X hx, gsB, gsU]
  refine congrArg (fun d => FrameDegreeData.uMat (PoinPf.Gw X w τ) * Matrix.diagonal d) ?_
  funext k
  simp only [FrameDegreeData.sOf, FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsS, gsU]

theorem det_ne_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (hx τ)
  rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
  exact_mod_cast PoinPf.sgn_ne _ _

theorem mem_dom_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) : x ∈ X.dom := by
  intro τ
  refine ⟨det_ne_of_orth X hx τ, fun i => ?_⟩
  have h := PoinPf.dmin_cpt_orth X hx 0 τ i
  rw [PoinPf.cpt_zero, PoinPf.Gw_zero, PoinPf.lminor_Jd] at h
  rw [h, Complex.ofReal_re]
  exact mul_self_pos.2 (PoinPf.psgn_ne _ _)

theorem exists_ball (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    ∃ R > 0, ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom := by
  obtain ⟨R, hR, h⟩ := PoinPf.good_ball X 0
  exact ⟨R, hR, fun w hw => PoinPf.cpt_mem_dom X (mem_dom_of_orth X hx) hx (h w hw).1 (h w hw).2.1⟩

theorem gsU_zero (X : Data E r) (τ : X.Ψ) : gsU X 0 τ = 1 := by
  ext j c
  simp only [gsU, PoinPf.Gw_zero, FrameDegreeData.uMat, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · rfl
  · have : FrameDegreeData.rowc (PoinPf.Jd X) c = 0 := by
      funext m
      simp only [FrameDegreeData.rowc, PoinPf.Jd, Pi.zero_apply]
      rw [Matrix.diagonal_apply_ne]
      intro hc
      have : ((Fin.castLE c.isLt.le m : Fin r) : ℕ) < c := m.isLt
      rw [← hc] at this
      exact lt_irrefl _ this
    rw [this, Matrix.zero_vecMul, Pi.zero_apply, neg_zero]
  · rfl

theorem gsB_zero (X : Data E r) (τ : X.Ψ) : gsB X 0 τ = 1 := by
  have hS : ∀ k, gsS X 0 τ k = 1 := by
    intro k
    simp only [gsS, gsU_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one, PoinPf.Gw_zero, PoinPf.Jd, Matrix.diagonal_apply_eq, Complex.ofReal_re, PoinPf.abs_sgn,
      Real.sqrt_one, inv_one]
  rw [gsB, gsU_zero, Matrix.one_mul]
  simp only [hS, Complex.ofReal_one, Matrix.diagonal_one]

theorem yM_zero (X : Data E r) (τ : X.Ψ) : yM X 0 τ = 1 := by
  rw [yM, PoinPf.nmat_zero, gsB_zero, Matrix.one_mul]

theorem secM_zero (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : secM X x 0 τ = 1 := by
  rw [secM, yM_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))]

theorem gsB_lower (X : Data E r) (w : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : b < a) : gsB X w τ a b = 0 := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_upper _ h, zero_mul]

theorem gsB_diag (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    gsB X w τ a a = ((gsS X w τ a : ℝ) : ℂ) := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_diag, one_mul]

end GlobalTheory.SUChartSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactor
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection.GSSmooth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Mat

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : Set W}

theorem cdo_det {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) : ContDiffOn ℝ ∞ (fun w => (f w).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem cdo_inv {m : Type} [Fintype m] [DecidableEq m] (f : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hd : ∀ w ∈ s, (f w).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((cdo_det f hf).inv hd).mul (cdo_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem cdo_mul {m : Type} [Fintype m] (f g : W → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun w => f w i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w => g w i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun w => (f w * g w) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

end Mat

theorem contDiff_nmat (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => mat (nmat X w) τ a b := by
  show ContDiff ℝ ∞ fun w : V (nd X) => nmat X w τ a b
  unfold nmat
  split_ifs
  · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_Gw (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℝ ∞ fun w : V (nd X) => PoinPf.Gw X w τ a b := by
  simp only [PoinPf.Gw, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul
    (ContDiff.sum fun l _ => (contDiff_nmat X τ l a).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_nmat X τ k b)

theorem blk_det_on (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (c : Fin r) :
    ∀ w ∈ {w : V (nd X) | cpt X x w ∈ X.dom}, (FrameDegreeData.blk (PoinPf.Gw X w τ) c).det ≠ 0 := by
  intro w hw
  have h := FrameDegreeData.blk_det X hw τ c
  rwa [gram_cpt X hx] at h

theorem cdo_gsU (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (j c : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsU X w τ j c) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  simp only [gsU, FrameDegreeData.uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact contDiffOn_const
  · refine ContDiffOn.neg ?_
    simp only [Matrix.vecMul, dotProduct]
    refine ContDiffOn.sum fun m _ => ContDiffOn.mul ?_ ?_
    · exact (contDiff_Gw X τ c (Fin.castLE c.isLt.le m)).contDiffOn
    · exact cdo_inv (fun w => FrameDegreeData.blk (PoinPf.Gw X w τ) c)
        (fun a b => (contDiff_Gw X τ (Fin.castLE c.isLt.le a) (Fin.castLE c.isLt.le b)).contDiffOn)
        (blk_det_on X hx τ c) _ _
  · exact contDiffOn_const

theorem cdo_q (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ContDiffOn ℝ ∞ (fun w => ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) i j)
      {w : V (nd X) | cpt X x w ∈ X.dom} := by
  refine cdo_mul _ _ (fun a b => cdo_mul _ _ (fun a' b' => ?_) (fun a' b' => (contDiff_Gw X τ a' b').contDiffOn) a b)
    (fun a b => ?_) i j
  · exact cdo_gsU X hx τ b' a'
  · exact Complex.conjCLE.contDiff.comp_contDiffOn (cdo_gsU X hx τ a b)

theorem q_eq_dOf (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) :
    ((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k = FrameDegreeData.dOf X (cpt X x w) τ k := by
  simp only [FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsU]

theorem cdo_gsS (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (k : Fin r) :
    ContDiffOn ℝ ∞ (fun w => gsS X w τ k) {w : V (nd X) | cpt X x w ∈ X.dom} := by
  set S := {w : V (nd X) | cpt X x w ∈ X.dom}
  have hpos : ∀ w ∈ S, 0 < sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re := by
    intro w hw
    rw [q_eq_dOf X hx w τ k]
    exact FrameDegreeData.sgn_dOf_pos X hw τ k
  have hf : ContDiffOn ℝ ∞ (fun w => sgn X.p0 k *
      (((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re) S :=
    contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn (cdo_q X hx τ k k))
  refine ContDiffOn.congr (ContDiffOn.inv (hf.sqrt fun w hw => (hpos w hw).ne')
    fun w hw => (Real.sqrt_pos.2 (hpos w hw)).ne') fun w hw => ?_
  have h := hpos w hw
  simp only [gsS]
  congr 2
  rcases FrameDegreeData.sgn_sq X.p0 k with hs | hs <;> rw [hs] at h ⊢
  · rw [one_mul] at h ⊢
    exact abs_of_pos h
  · rw [neg_one_mul] at h ⊢
    exact abs_of_neg (neg_pos.1 h)

theorem gsB_contDiffOn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r},
    IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  intro E _ _ _ r X x hx τ a b
  have e : (fun w => gsB X w τ a b) = fun w => gsU X w τ a b * ((gsS X w τ b : ℝ) : ℂ) := by
    funext w
    simp only [gsB, Matrix.mul_diagonal]
  rw [e]
  exact (cdo_gsU X hx τ a b).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (cdo_gsS X hx τ b))

end GlobalTheory.SUChartSection.GSSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnGramSchmidtUpperTriangularFactorStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (τ : X.Ψ) (a b : Fin r), ContDiffOn ℝ ∞ (fun w => gsB X w τ a b) {w | cpt X x w ∈ X.dom} := by
  first | exact @GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn | exact GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn | (intros; apply GlobalTheory.SUChartSection.GSSmooth.gsB_contDiffOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAt
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_hasStrictFDerivAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : IsOrth X x) : HasStrictFDerivAt (yF X) (dY X) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hnhds : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) fun w hw => hball w hw
  have hB : ∀ τ k b, ContDiffAt ℝ ∞ (fun w => gsB X w τ k b) 0 := fun τ k b =>
    (GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ k b).contDiffAt hnhds
  have hN : ∀ τ a k, ContDiffAt ℝ ∞ (fun w : V (nd X) => nmat X w τ a k) 0 := fun τ a k =>
    have h1 : ContDiff ℂ ∞ (fun w : V (nd X) => nmat X w τ a k) := by
      unfold nmat
      split_ifs
      · exact ((EuclideanSpace.proj _ : V (nd X) →L[ℂ] ℂ)).contDiff
      · exact contDiff_const
      · exact contDiff_const
    (h1.restrict_scalars ℝ).contDiffAt
  have hY : ContDiffAt ℝ ∞ (yF X) 0 := by
    rw [contDiffAt_pi]; intro τ
    rw [contDiffAt_pi]; intro a
    rw [contDiffAt_pi]; intro b
    show ContDiffAt ℝ ∞ (fun w => (mat (nmat X w) τ * gsB X w τ) a b) 0
    simp only [Matrix.mul_apply]
    refine ContDiffAt.sum fun k _ => ?_
    exact (hN τ a k).mul (hB τ k b)
  exact hY.hasStrictFDerivAt_fderiv (by simp)

end GlobalTheory.SUChartSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAtStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → HasStrictFDerivAt (yF X) (dY X) 0 := by
  first | exact @GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | exact GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | (intros; apply GlobalTheory.SUChartSection.yF_hasStrictFDerivAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonal
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_apply_sum (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    yF X w τ a b = ∑ k, nmat X w τ a k * gsB X w τ k b := by
  simp [yF, yM, Matrix.mul_apply, mat]

theorem gsB_differentiableAt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w => gsB X w τ a b) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hs : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) (fun w hw => hball w hw)
  exact ((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).contDiffAt hs).differentiableAt (by simp)

theorem nmat_differentiableAt (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ a b) 0 :=
  ((PoinPf.diff_nmat X τ a b).restrictScalars ℝ) 0

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    nmat X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  have h := congrFun (congrFun (PoinPf.nmat_zero X τ) a) b
  simpa [mat] using h

theorem gsB_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    gsB X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  rw [gsB_zero]

theorem dY_lower (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ)
    (a b : Fin r) (hba : b < a) : dY X z τ a b = nmat X z τ a b := by
  have hS := (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx).hasFDerivAt
  have h1 := hasFDerivAt_pi'.1 hS τ
  have h2 := hasFDerivAt_pi'.1 h1 a
  have h3 := hasFDerivAt_pi'.1 h2 b
  have hT : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) 0 :=
    HasFDerivAt.fun_sum (fun k _ =>
      (nmat_differentiableAt X τ a k).hasFDerivAt.mul (gsB_differentiableAt X hx τ k b).hasFDerivAt)
  have h3' : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      ((ContinuousLinearMap.proj b).comp ((ContinuousLinearMap.proj a).comp
        ((ContinuousLinearMap.proj τ).comp (dY X)))) 0 := by
    have : (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b) = fun w => yF X w τ a b := by
      funext w; rw [yF_apply_sum]
    rw [this]; exact h3
  have hU := congrArg (fun L => L z) (h3'.unique hT)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hU
  rw [hU]
  have hB0 : (fun w : V (nd X) => gsB X w τ a b) = fun _ => 0 := by
    funext w; exact gsB_lower X w τ hba
  set e := (Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), hba⟩⟩
  have hN : (fun w : V (nd X) => nmat X w τ a b) =
      ⇑((EuclideanSpace.proj e : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext w; simp [nmat, hba, e]; rfl
  have hsum : (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) =
      fderiv ℝ (fun w => gsB X w τ a b) 0 + fderiv ℝ (fun w => nmat X w τ a b) 0 := by
    simp only [nmat_zero_apply, gsB_zero_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum, ContinuousLinearMap.add_apply]
  rw [hB0, hN, fderiv_const_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.zero_apply, zero_add]
  simp [nmat, hba, e] <;> rfl

end GlobalTheory.SUChartSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFderivBelowDiagonalStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a b : Fin r), b < a → dY X z τ a b = nmat X z τ a b := by
  first | exact @GlobalTheory.SUChartSection.dY_lower | exact GlobalTheory.SUChartSection.dY_lower | (intros; apply GlobalTheory.SUChartSection.dY_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkew
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkew
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_gram_entry (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {R : ℝ}
    (hR : ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom) {w : V (nd X)}
    (hw : w ∈ Metric.ball (0 : V (nd X)) R) (τ : X.Ψ) (a b : Fin r) :
    ∑ k, yF X w τ k a * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) * conj (yF X w τ k b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h1 := FrameDegreeData.ortho_bOf X (hR w hw) τ
  rw [bOf_cpt X hx w] at h1
  have h2 : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [h2, FrameDegreeData.gram_mul, hx τ] at h1
  have h3 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply] at h3
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply] at h3
  rw [← h3]
  rfl

theorem dY_skew (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  obtain ⟨R, hR, hdom⟩ := exists_ball X hx
  set ε : Fin r → ℂ := fun k => ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) with hε
  have hY : HasFDerivAt (yF X) (dY X) 0 := hd.hasFDerivAt
  let P : Fin r → Fin r → (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ := fun k c =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) c).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : ∀ k c, HasFDerivAt (fun w => yF X w τ k c) ((P k c).comp (dY X)) 0 :=
    fun k c => (P k c).hasFDerivAt.comp 0 hY
  have hcc : ∀ k c, HasFDerivAt (fun w => conj (yF X w τ k c))
      ((Complex.conjCLE.toContinuousLinearMap).comp ((P k c).comp (dY X))) 0 :=
    fun k c => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 (hc k c)
  have hf := HasFDerivAt.sum (u := Finset.univ) fun k _ => ((hc k a).mul_const (ε k)).mul (hcc k b)
  have hconst : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b))
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    refine (hasFDerivAt_const (if a = b then ε a else 0) (0 : V (nd X))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with w hw
    exact yF_gram_entry X hx hdom hw τ a b
  have hf' : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b)) _ 0 :=
    hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [Finset.sum_apply])
  have key := congrArg (fun L => L z) (hf'.unique hconst)
  have h0 : ∀ k c, yF X 0 τ k c = if k = c then 1 else 0 := by
    intro k c
    show yM X 0 τ k c = _
    rw [yM_zero, Matrix.one_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, h0] at key
  simp only [ite_mul, one_mul, zero_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at key
  linear_combination key

end GlobalTheory.SUChartSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkewStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a b : Fin r), dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  first | exact @GlobalTheory.SUChartSection.dY_skew | exact GlobalTheory.SUChartSection.dY_skew | (intros; apply GlobalTheory.SUChartSection.dY_skew <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrix
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem det_secM_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  intro E _ _ _ r X x hx w hw τ
  have hG := FrameDegreeData.ortho_bOf X hw τ
  rw [bOf_cpt X hx w] at hG
  have hm : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [hm, FrameDegreeData.gram_mul, hx τ] at hG
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hc : ((yM X w τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (yM X w τ).det :=
    (RingHom.map_det (starRingEnd ℂ) (yM X w τ)).symm
  rw [hc] at hd
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast PoinPf.sgn_ne _ _
  have hY : (yM X w τ).det = ((∏ k, gsS X w τ k : ℝ) : ℂ) := by
    rw [yM, Matrix.det_mul, gsB, Matrix.det_mul, Matrix.det_diagonal]
    rw [Matrix.det_of_lowerTriangular _ (fun a b hab => ?_)]
    · rw [gsU, Matrix.det_of_upperTriangular (FrameDegreeData.uMat_upper _)]
      simp only [FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul]
      have : ∀ i, mat (nmat X w) τ i i = 1 := fun i => by
        simp [mat, nmat]
      simp only [this, Finset.prod_const_one, one_mul]
      push_cast; rfl
    · show nmat X w τ a b = 0
      simp only [nmat]
      have hab' : a < b := hab
      have h1 : ¬ b < a := not_lt.2 (le_of_lt hab')
      rw [dite_eq_right h1, if_neg (ne_of_lt hab')]
  set t : ℝ := ∏ k, gsS X w τ k with ht
  have hpos : 0 ≤ t := Finset.prod_nonneg fun k _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hY, Complex.conj_ofReal] at hd
  have htt : ((t * t : ℝ) : ℂ) = 1 := by
    have h2 : (t : ℂ) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det * (t : ℂ) =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [hd, one_mul]
    push_cast
    have h3 : ((t : ℂ) * t) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [← h2]; ring
    exact mul_right_cancel₀ hJ h3
  have htt' : t * t = 1 := by exact_mod_cast htt
  have ht1 : t = 1 := by nlinarith
  rw [secM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))) (yM X w τ), hY, ht1, Complex.ofReal_one]

end GlobalTheory.SUChartSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrixStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  first | exact @GlobalTheory.SUChartSection.det_secM_eq_one | exact GlobalTheory.SUChartSection.det_secM_eq_one | (intros; apply GlobalTheory.SUChartSection.det_secM_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebra
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

theorem conj_mem_realLie : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  intro E _ _ _ r X x hx Y hY hd
  intro τ
  set A : Matrix (Fin r) (Fin r) ℂ := mat x τ with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  set D : Matrix (Fin r) (Fin r) ℂ := A * Y τ * A⁻¹ with hDdef
  have hDA : D * A = A * Y τ := by
    rw [hDdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · change (A * Y τ * A⁻¹).trace = 0
    rw [Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
    simp only [Matrix.trace, Matrix.diag, hd, Finset.sum_const_zero]
  · intro u w
    change hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) = 0
    clear_value D
    set Gt : Matrix (Fin r) (Fin r) ℂ := X.Gm.map τ.1 with hGt
    have hform : ∀ u v : Fin r → ℂ, hermC τ.1 X.Gm u v = u ⬝ᵥ (Gt *ᵥ (fun b => conj (v b))) := by
      intro u v
      simp only [hermC, dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [hGt, Matrix.map_apply]
      ring
    have hconj : ∀ v : Fin r → ℂ, (fun b => conj ((D *ᵥ v) b)) = D.map (starRingEnd ℂ) *ᵥ (fun b => conj (v b)) := by
      intro v
      funext b
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    set M : Matrix (Fin r) (Fin r) ℂ := Dᵀ * Gt + Gt * D.map (starRingEnd ℂ) with hMdef
    have hsum : hermC τ.1 X.Gm (D *ᵥ u) w + hermC τ.1 X.Gm u (D *ᵥ w) =
        u ⬝ᵥ (M *ᵥ (fun b => conj (w b))) := by
      rw [hform, hform, hconj, hMdef, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
      congr 1
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
    have hJ : Aᵀ * Gt * A.map (starRingEnd ℂ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
      rw [hGt, ← FrameDegreeData.gram_eq]
      exact hx τ
    have hkey : Aᵀ * M * A.map (starRingEnd ℂ) = 0 := by
      have e1 : Aᵀ * M * A.map (starRingEnd ℂ) =
          (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) := by
        rw [hMdef, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      have e2 : (D * A)ᵀ * Gt * A.map (starRingEnd ℂ) + Aᵀ * Gt * (D * A).map (starRingEnd ℂ) =
          (Y τ)ᵀ * (Aᵀ * Gt * A.map (starRingEnd ℂ)) + (Aᵀ * Gt * A.map (starRingEnd ℂ)) * (Y τ).map (starRingEnd ℂ) := by
        rw [hDA, Matrix.transpose_mul, Matrix.map_mul]
        simp only [Matrix.mul_assoc]
      rw [e1, e2, hJ]
      ext a b
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.map_apply, Matrix.zero_apply]
      exact hY τ a b
    have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
    have hAc : IsUnit (A.map (starRingEnd ℂ)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact hA.map _
    have hM : M = 0 := by
      calc M = Aᵀ⁻¹ * (Aᵀ * M * A.map (starRingEnd ℂ)) * (A.map (starRingEnd ℂ))⁻¹ := by
            rw [Matrix.mul_assoc Aᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hAt,
              Matrix.mul_nonsing_inv_cancel_right _ _ hAc]
        _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]
    rw [hsum, hM, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory.SUChartSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSkewMemProductSpecialUnitaryLieAlgebraStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_skew_mem_productSpecialUnitaryLieAlgebra : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (Y : X.Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ a b, Y τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (Y τ a b) = 0) → (∀ τ a, Y τ a a = 0) → (fun τ => ((mat x τ * Y τ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ)) ∈ realLie X.Ψ X.Gm := by
  first | exact @GlobalTheory.SUChartSection.conj_mem_realLie | exact GlobalTheory.SUChartSection.conj_mem_realLie | (intros; apply GlobalTheory.SUChartSection.conj_mem_realLie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagIm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagIm
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_expand {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (w : V (nd X)) (τ : X.Ψ) (k j : Fin r) :
    yF X w τ k j = (∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m j) + gsB X w τ k j := by
  simp only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]
  have hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0 := by simp
  rw [Finset.sum_filter, hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy m k with h | h | h
  · simp [h, h.ne']
  · subst h; simp [nmat]
  · have h1 : ¬ m < k := not_lt.2 h.le
    have h2 : k ≠ m := h.ne
    simp [nmat, h1, h2]

theorem diagreal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (_hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    (dY X z τ a a).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  have hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0 := by
    intro k j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j
  have hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0 := fun k m =>
    ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ
  have hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a -
          ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a := by
        funext w; rw [yF_expand]; ring
      rw [hrepr]
      refine (hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))
      have := (Finset.mem_filter.1 hm).2
      rw [Fin.lt_def] at this
      omega
  have hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0 := by
    intro m hm
    have := congrFun (congrFun (PoinPf.nmat_zero X τ) a) m
    simp only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this
    exact this
  have hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0 := by
    intro m hm
    rw [gsB_zero, Matrix.one_apply, if_neg hm.ne]
  have hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    have h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
        (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 +
          gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0 :=
      HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)
    convert h using 1
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    rw [hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]
  have him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum
    rw [ContinuousLinearMap.comp_zero] at h
    have hf : (fun w => (yF X w τ a a).im) =
        ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a := by
      funext w
      simp only [Function.comp_apply, Complex.imCLM_apply]
      rw [yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]
    rw [hf]; exact h
  let L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0 :=
    Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)
  have := congrArg (fun L => L z) (hc.unique him)
  simpa [L] using this

end GlobalTheory.SUChartSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagImStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), (dY X z τ a a).im = 0 := by
  first | exact @GlobalTheory.SUChartSection.diagreal | exact GlobalTheory.SUChartSection.diagreal | (intros; apply GlobalTheory.SUChartSection.diagreal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSection
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun l => conj (v l)) := by
  simp only [hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ)
    (u v : Fin r → ℂ) :
    hermC τ G (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ (gram τ G M *ᵥ fun l => conj (v l)) := by
  have hc : (fun l => conj ((M *ᵥ v) l)) = M.map (starRingEnd ℂ) *ᵥ fun l => conj (v l) := by
    funext l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dot, hc, FrameDegreeData.gram_eq, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem gram_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (secM X x w τ) = gram τ.1 X.Gm 1 := by
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have hgx : secM X x w τ * mat x τ = mat (rmul (cpt X x w) (FrameDegreeData.bOf X (cpt X x w))) τ := by
    rw [secM, Matrix.nonsing_inv_mul_cancel_right _ _ hu, bOf_cpt X hx, yM, ← Matrix.mul_assoc]
    rfl
  have key : (mat x τ)ᵀ * gram τ.1 X.Gm (secM X x w τ) * (mat x τ).map (starRingEnd ℂ) =
      (mat x τ)ᵀ * gram τ.1 X.Gm 1 * (mat x τ).map (starRingEnd ℂ) := by
    rw [← FrameDegreeData.gram_mul, hgx, FrameDegreeData.ortho_bOf X hw τ, ← hx τ, ← FrameDegreeData.gram_mul, Matrix.one_mul]
  have huT : IsUnit (mat x τ)ᵀ.det := by rwa [Matrix.det_transpose]
  have huC : IsUnit ((mat x τ).map (starRingEnd ℂ)).det := by
    rw [show (mat x τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat x τ) from rfl, ← RingHom.map_det, isUnit_iff_ne_zero, map_ne_zero]
    exact det_ne_of_orth X hx τ
  have h2 := congrArg (fun M => ((mat x τ)ᵀ)⁻¹ * M * ((mat x τ).map (starRingEnd ℂ))⁻¹) key
  simp only [Matrix.mul_assoc] at h2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ huT, Matrix.mul_nonsing_inv_cancel_right _ _ huC,
    ← Matrix.mul_assoc] using h2

theorem hermC_secM (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {w : V (nd X)}
    (hw : cpt X x w ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  rw [hermC_mulVec, gram_secM X hx hw τ, ← hermC_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]

end GlobalTheory.SUChartSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHermitianFormUnitaryChartSectionStatement
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHermitianForm_unitaryChartSection : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ (τ : X.Ψ) (u v : Fin r → ℂ), hermC τ.1 X.Gm (secM X x w τ *ᵥ u) (secM X x w τ *ᵥ v) = hermC τ.1 X.Gm u v := by
  first | exact @GlobalTheory.SUChartSection.hermC_secM | exact GlobalTheory.SUChartSection.hermC_secM | (intros; apply GlobalTheory.SUChartSection.hermC_secM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularCha
noncomputable section

namespace GlobalTheory.SUChartSection
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal ComplexConjugate ContDiff

theorem exists_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  intro E _ _ _ r X x hx
  classical
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hdet1 : ∀ w, cpt X x w ∈ X.dom → ∀ τ, (secM X x w τ).det ≠ 0 := fun w hw τ => by
    rw [GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ]; exact one_ne_zero
  let secU : ∀ w, cpt X x w ∈ X.dom → realSU X.Ψ X.Gm := fun w hw =>
    ⟨fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (secM X x w τ) (hdet1 w hw τ),
      fun τ => ⟨GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx hw τ, GlobalTheory.T.complexHermitianForm_unitaryChartSection X hx hw τ⟩⟩
  have hsecU : ∀ w (hw : cpt X x w ∈ X.dom) τ,
      ((((secU w hw : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun _ _ _ => rfl
  let σ : V (nd X) → realSU X.Ψ X.Gm := fun w => if h : w ∈ Metric.ball (0 : V (nd X)) R then secU w (hball w h) else 1
  have hσ : ∀ w (h : w ∈ Metric.ball (0 : V (nd X)) R) τ,
      ((((σ w : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        secM X x w τ := fun w h τ => by
    simp only [σ, dif_pos h]; rfl
  have hx0 : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ)
  have h0 : (0 : V (nd X)) ∈ Metric.ball (0 : V (nd X)) R := Metric.mem_ball_self hR
  let Cx : (X.Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        have e : Matrix.of ((Y + Z) τ) = Matrix.of (Y τ) + Matrix.of (Z τ) := rfl
        simp only [e, Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        have e : Matrix.of ((c • Y) τ) = c • Matrix.of (Y τ) := rfl
        simp only [e, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let C := LinearMap.toContinuousLinearMap Cx
  have hC : ∀ Y τ, C Y τ = (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) := fun _ _ => rfl
  refine ⟨σ, R, C.comp (dY X), hR, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subtype.ext (funext fun τ => Units.ext ?_)
    rw [hσ 0 h0 τ, secM_zero X hx τ]; rfl
  · rw [continuousOn_iff_continuous_restrict]
    have hg : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => gsB X w τ := fun τ => by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      exact ((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).continuousOn.mono (fun w hw => hball w hw)).restrict
    have hM : ∀ τ, Continuous fun w : Metric.ball (0 : V (nd X)) R => secM X x w τ := fun τ => by
      refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
      exact ((PoinPf.cont_nmatm X τ).comp continuous_subtype_val).matrix_mul (hg τ)
    refine continuous_induced_rng.2 (continuous_pi fun τ => Units.continuous_iff.2 ⟨?_, ?_⟩)
    · refine (hM τ).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      exact (hσ w w.2 τ).symm
    · refine ((hM τ).matrix_adjugate).congr fun w => ?_
      simp only [Function.comp_apply, Set.restrict_apply]
      rw [Matrix.coe_units_inv, hσ w w.2 τ, Matrix.inv_def, GlobalTheory.T.det_unitaryChartSectionConjugatedMatrix X hx (hball w w.2) τ, Ring.inverse_one, one_smul]
  · intro z hz
    refine ⟨FrameDegreeData.bOf X (cpt X x z), FrameDegreeData.bOf_mem X (hball z hz), ?_⟩
    funext τ
    show (((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) = (mat (cpt X x z) τ * mat (FrameDegreeData.bOf X (cpt X x z)) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [hσ z hz τ, bOf_cpt X hx z]
    show mat x τ * yM X z τ * (mat x τ)⁻¹ * mat x τ = mat x τ * mat (nmat X z) τ * gsB X z τ
    rw [Matrix.mul_assoc _ (mat x τ)⁻¹, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one, yM, Matrix.mul_assoc]
  · have h1 : HasStrictFDerivAt (fun z => C (yF X z)) (C.comp (dY X)) 0 :=
      C.hasStrictFDerivAt.comp 0 (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with z hz
    funext τ a b
    rw [hσ z hz τ, hC]
    rfl
  · intro z
    have hdiag : ∀ τ a, dY X z τ a a = 0 := fun τ a => by
      have h6 := congrArg Complex.re (GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a a)
      have h7 := GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_diag_im X hx z τ a
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
        Complex.conj_im, h7, Complex.zero_re, mul_zero, sub_zero, zero_mul, neg_zero] at h6
      have hs := PoinPf.sgn_ne X.p0 (a : ℕ)
      have hre : (dY X z τ a a).re = 0 := by
        have : 2 * sgn X.p0 (a : ℕ) * (dY X z τ a a).re = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (by linarith : sgn X.p0 (a : ℕ) = 0) hs
        · exact h
      exact Complex.ext hre h7
    have hIF : ∀ τ, inFrame x (C.comp (dY X) z) τ = Matrix.of (dY X z τ) := fun τ => by
      show (mat x τ)⁻¹ * Matrix.of (C (dY X z) τ) * mat x τ = _
      rw [hC]
      show (mat x τ)⁻¹ * (mat x τ * Matrix.of (dY X z τ) * (mat x τ)⁻¹) * mat x τ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hx0 τ), Matrix.mul_one]
    refine ⟨?_, fun τ a b h => ?_, fun τ a => ?_⟩
    · exact GlobalTheory.T.conj_skew_mem_productSpecialUnitaryLieAlgebra X hx (fun τ => Matrix.of (dY X z τ)) (fun τ a b => GlobalTheory.T.unitaryChartSectionFrameEntriesFDeriv_skew X hx z τ a b) hdiag
    · rw [hIF]; exact GlobalTheory.T.unitaryChartSection_fderiv_below_diagonal X hx z τ a b h
    · rw [hIF]; exact hdiag τ a
end GlobalTheory.SUChartSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularChaStatement
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (σ : V (nd X) → realSU X.Ψ X.Gm) (ρ : ℝ) (D₁ : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), 0 < ρ ∧ σ 0 = 1 ∧ ContinuousOn σ (Metric.ball 0 ρ) ∧ (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) ∧ HasStrictFDerivAt (fun z => (fun τ a b => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) D₁ 0 ∧ ∀ z, D₁ z ∈ realLie X.Ψ X.Gm ∧ (∀ τ a b, b < a → inFrame x (D₁ z) τ a b = nmat X z τ a b) ∧ ∀ τ a, inFrame x (D₁ z) τ a a = 0 := by
  first | exact @GlobalTheory.SUChartSection.exists_section | exact GlobalTheory.SUChartSection.exists_section | (intros; apply GlobalTheory.SUChartSection.exists_section <;> assumption)
end
