module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TrdegPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ortho_holds : OrthoStatement (E := E) := by
  intro r X x hx

  have hBor := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem (X := X) hx
  refine ⟨ReciprocityTheory.ChartRestriction.G.FD.rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x),
    ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf (X := X) hx,
    fun τ => ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹ :
      Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    haveI : Invertible (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ) :=
      Matrix.invertibleOfIsUnitDet _ hdet
    have hM : (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).BlockTriangular id :=
      fun i j hij => (hBor τ).2 i j hij
    have hMi := Matrix.blockTriangular_inv_of_blockTriangular hM
    refine ⟨?_, fun a c hca => hMi hca⟩
    show ((ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹).det ≠ 0
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).ne_zero
  · funext τ
    have hdet : IsUnit (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ).det :=
      isUnit_iff_ne_zero.mpr (hBor τ).1
    show ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat x τ *
      ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ *
      (ReciprocityTheory.ChartRestriction.G.FD.mat (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) τ)⁻¹
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem cd_nmat (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
    | fun_prop
    | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
  · simp only [dif_neg h]
    exact contDiff_const

theorem cd_cpt_entry (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => cpt X x0 z τ a b := by
  have he : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ c, x0 τ a c * nmat X z τ c b := by
    funext z
    simp [cpt, rmul, mat, Matrix.mul_apply]
  rw [he]
  exact ContDiff.sum fun c _ => contDiff_const.mul (cd_nmat X τ c b)

theorem cd_cpt : ContDiff ℂ ∞ (cpt X x0) := contDiff_pi.mpr fun τ => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
  cd_cpt_entry X x0 τ a b

theorem hol_comp {f : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom) :
    DifferentiableOn ℂ (fun z => f (cpt X x0 z)) (OmF X x0) := hf.comp ((cd_cpt X x0).differentiable (by simp)).differentiableOn (fun _ hz => hz)

theorem isOpen_OmF : IsOpen (OmF X x0) := by
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_matrix fun a b => (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hent : ∀ (τ : X.Ψ) (a b : Fin r), Continuous fun x : Frame X.Ψ r => x τ a b := fun τ a b =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdmin : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
    refine continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
    exact ((hent τ c _).mul continuous_const).mul (Complex.continuous_conj.comp (hent τ d _))
  have hGG : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [GG]
  have hopen : IsOpen (GG X.Ψ X.Gm X.p0) := by
    rw [hGG]
    refine isOpen_iInter_of_finite fun τ => ?_
    refine IsOpen.inter (isOpen_ne_fun (hmat τ).matrix_det continuous_const)
      (isOpen_iInter_of_finite fun i => ?_)
    exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))
  exact (cd_cpt X x0).continuous.isOpen_preimage _ hopen

theorem cd_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
  have hE : ∀ (τ : X.Ψ) (a b : Fin r), ContDiff ℝ ∞ fun z : V (nd X) => cpt X x0 z τ a b :=
    fun τ a b => (cd_cpt_entry X x0 τ a b).restrict_scalars ℝ
  have hC : ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiff ℝ ∞ fun z : V (nd X) => starRingEnd ℂ (cpt X x0 z τ a b) := by
    intro τ a b
    have h := Complex.conjCLE.contDiff.comp (hE τ a b)
    simpa [Function.comp_def] using h
  unfold dmin lminor
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun k _ => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
  exact ((hE τ c _).mul contDiff_const).mul (hC τ d _)

variable {X x0}

theorem dmin_ne {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := (hz τ).2 i
  rw [h0, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

variable (X x0)

def LD (z : V (nd X)) : ℝ :=
  ∑ τ, ∑ i : Fin r, (-2) * Real.log ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖

variable {X x0}

theorem densF_pos {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < densF X x0 z := by
  unfold densF
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_
  exact zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _

theorem log_densF {z : V (nd X)} (hz : z ∈ OmF X x0) : Real.log (densF X x0 z) = LD X x0 z := by
  have hp : ∀ (τ : X.Ψ) (i : Fin r), 0 < ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ) :=
    fun τ i => zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _
  unfold densF LD
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => hp τ i).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (hp τ i).ne')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_zpow]
  norm_num

theorem LD_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (LD X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold LD
  exact ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => contDiffAt_const.mul (hd τ i.castSucc)

theorem logDens_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z := by
  refine (LD_contDiffAt hz).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using log_densF hw

theorem densF_continuousOn : ContinuousOn (densF X x0) (OmF X x0) := by
  intro z hz
  have h := Real.continuous_exp.continuousAt.comp (logDens_contDiffAt hz).continuousAt
  refine (ContinuousAt.congr h ?_).continuousWithinAt
  filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using Real.exp_log (densF_pos hw)

theorem rhF_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold rhF
  exact (ContDiffAt.sum fun τ _ => hd τ _).neg

theorem ka_contDiffAt (bb : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (kaF X x0 bb) z := by
  unfold kaF
  exact Real.contDiff_exp.contDiffAt.comp z (contDiffAt_const.mul (rhF_contDiffAt hz))

theorem levi_rh_nonneg (hGrad : RhGradFStatement (E := E)) (hx0 : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
  have hG := hGrad r X x0 hx0 z hz ξ
  by_cases hC : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) = 0
  · have hwd : ∀ w ∈ OmF X x0, ∀ j,
        wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw j
      have h := hGrad r X x0 hx0 w hw (Pi.single j 1)
      rw [hC, zero_mul] at h
      have h' := le_antisymm h (Complex.normSq_nonneg _)
      rw [Complex.normSq_eq_zero] at h'
      simpa [Pi.single_apply] using h'
    have hwdb : ∀ w ∈ OmF X x0, ∀ k,
        wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw k
      have hd : DifferentiableAt ℝ (rhF X x0) w := (rhF_contDiffAt hw).differentiableAt (by simp)
      have hf : ∀ v, fderiv ℝ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w v =
          ((fderiv ℝ (rhF X x0) w v : ℝ) : ℂ) := by
        intro v
        have hh : HasFDerivAt (fun w => ((rhF X x0 w : ℝ) : ℂ))
            (Complex.ofRealCLM.comp (fderiv ℝ (rhF X x0) w)) w :=
          Complex.ofRealCLM.hasFDerivAt.comp w hd.hasFDerivAt
        rw [hh.fderiv]
        rfl
      have h0 := hwd w hw k
      simp only [wd, hf] at h0
      simp only [wdb, hf]
      set p := fderiv ℝ (rhF X x0) w (bas (nd X) k)
      set q := fderiv ℝ (rhF X x0) w (Complex.I • bas (nd X) k)
      have h2 : (p : ℂ) - Complex.I * (q : ℂ) = 0 := by
        rcases div_eq_zero_iff.mp h0 with h0 | h0
        · exact h0
        · norm_num at h0
      have hp : p = 0 := by
        have h3 := congrArg Complex.re h2
        simpa using h3
      have hq : q = 0 := by
        have h3 := congrArg Complex.im h2
        simpa using h3
      rw [hp, hq]
      simp
    have hL : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ = 0 := by
      unfold leviV
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      have hev : wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using hwdb w hw k
      have hfd : fderiv ℝ (wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ))) z = 0 := by
        rw [hev.fderiv_eq]
        simp
      simp [wd, hfd]
    rw [hL]
    simp
  · have hCpos : (0 : ℝ) < ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hC)
    have h0 : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) * 0 ≤
        ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
          (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
      rw [mul_zero]
      exact le_trans (Complex.normSq_nonneg _) hG
    exact le_of_mul_le_mul_left h0 hCpos

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsInvFn (X : Data E r) (ph : Frame X.Ψ r → ℝ) : Prop :=
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ph (lact γ (rmul x b)) = ph x

def leviM (X : Data E r) (g : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((g (cpt X x0 w) : ℝ) : ℂ)) z ξ).re

def cfwM (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  (∃ C A' : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x)) ∧
  ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ C A' : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ x τ) →
    ps x ≤ C + A' * Real.log (1 + 1 / X.la1 x) - 8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ

structure ArchInM (X : Data E r) where
  L : Wt X.Ψ r
  de : Wt X.Ψ r
  Fp : Wt X.Ψ r
  T : ℕ
  i : ℕ
  g0 : ℕ
  N : ℕ
  c : ℝ
  c1 : ℝ
  a1 : ℝ
  rr : ℝ
  n_ge : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 1 ≤ i
  genus_pos : 1 ≤ g0
  c_pos : 0 < c
  frame_theta_const_pos : 0 < c1
  frame_theta_weight_pos : 0 < a1
  rr_nonneg : 0 ≤ rr
  Tcg0 : (T : ℝ) * c * g0 ≤ 1
  rr_le : rr * (1 + c1 / a1) ≤ 2 * T
  w : Fin N → Frame X.Ψ r → ℂ
  w_van : ∀ k, w k ∈ X.SSgt L 0
  w_nz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0
  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInvFn X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x
  p1 : ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x
  p2 : ∀ x ∈ X.dom, (T : ℝ) * c * ph x ≤ c1 / X.la1 x ^ 2
  p3 : ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2
  et : Frame X.Ψ r → ℂ
  genus_even : Even g0
  et_sec : X.IsSec ((i * (g0 / 2)) • de) et
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  p4 : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm ((i * (g0 / 2)) • de) et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))
  th1 : Frame X.Ψ r → ℂ
  firstTheta_vanishes : th1 ∈ X.SSgt (2 • L - de) 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  th2 : Frame X.Ψ r → ℂ
  secondTheta_vanishes : th2 ∈ X.SSgt ((nd X + 4) • L - Fp) 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp : Frame X.Ψ r → ℂ
  thp_van : thp ∈ X.SSgt Fp 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0
  ps0 : Frame X.Ψ r → ℝ
  potential_invariant : IsInvFn X ps0
  potential_smooth : ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}
  base_psi_levi_lower_bound : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
    -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ
  base_psi_weighted_cf : cfwM X ps0 a1
  posL : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X L) x0 z ξ
  posLde : ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    0 < leviM X (phla X (2 • L - de)) x0 z ξ
  posF : ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T →
    ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ

structure FlatM (X : Data E r) (Xa : ArchInM X) where
  w0 : Frame X.Ψ r → ℂ
  s : Fin (nd X) → Frame X.Ψ r → ℂ
  weightForm_vanishes : w0 ∈ X.SSgt Xa.L 0
  s_van : ∀ k, s k ∈ X.SSgt Xa.L 0
  δ : ℕ
  xs : Fin δ → Frame X.Ψ r
  xs_mem : ∀ j, xs j ∈ X.dom
  S_eq : ∀ x ∈ X.dom, (∀ k, s k x = 0) ↔
    ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)
  xs_inj : ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j'
  w0_ne : ∀ j, w0 (xs j) ≠ 0
  coord : ∀ j, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
    s k (cpt X (xs j) z) / w0 (cpt X (xs j) z) : V (nd X))) 0).det ≠ 0
  w_le : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
    K * (X.pnorm Xa.L w0 x ^ 2 + ∑ k, X.pnorm Xa.L (s k) x ^ 2)

  denom_le_family : ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm Xa.L w0 x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2
  s_le_w : ∃ K : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm Xa.L (s k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2

  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ j, xs j ∈ U) →
    (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
    ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ U → ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (s k) x ^ 2

def monoM {n : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (α : Fin n → ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ k, s k x ^ α k

def leadM {n δ : ℕ} (X : Data E r) (s : Fin n → Frame X.Ψ r → ℂ) (w0 : Frame X.Ψ r → ℂ)
    (t : Fin δ → Frame X.Ψ r → ℂ) (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt n a0, ∑ k, cc α k * monoM X s α x * w0 x ^ (T - ∑ q, α q) * t k x

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfA

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def sf (p0 : ℕ) (α β : Fin r → ℂ) : ℂ :=
  ∑ k : Fin r, ((sgn p0 (k : ℕ) : ℝ) : ℂ) * α k * conj (β k)

def cl (N : Fin r → Fin r → ℂ) (a : Fin r) : Fin r → ℂ := fun k => N k a

noncomputable def Ag (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Matrix (Fin p0) (Fin p0) ℂ :=
  Matrix.of fun a b => sf p0 (cl N (Fin.castLE hp a)) (cl N (Fin.castLE hp b))

noncomputable def Ms (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) * (Ag p0 hp N)⁻¹ a b *
    conj (sf p0 v (cl N (Fin.castLE hp b)))).re - (sf p0 v v).re

private lemma hermC_eq_dotProduct_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (v b)) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Y = Yᵀ * G.map τ * Y.map conj := by
  ext i j
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma hermC_mulVec_eq_dotProduct_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) (w n : Fin r → ℂ) :
    hermC τ G (Y *ᵥ w) (Y *ᵥ n) = w ⬝ᵥ (gram τ G Y *ᵥ fun b => conj (n b)) := by
  have hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b) := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private lemma det_ne_zero_of_gram_eq_diagonal_sgn (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hY
  rw [gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm

theorem maj_chart (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by
  have hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n := by
    intro u' n
    rw [hermC_mulVec_eq_dotProduct_gram, hY]
    simp only [sf, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetY := det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY
  have hv : v = Y *ᵥ (Y⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]
  have hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a := by
    intro a
    rw [hw]
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hgp : X.gramPos w τ = Ag X.p0 X.p0_le N := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]
    rw [hcol, hcol, hS]
  unfold Data.maj Data.posPart Ms
  rw [hgp]
  conv_lhs => rw [hv]
  simp only [hcol, hS]

theorem dom_of_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) : u ∈ X.dom := by
  intro τ
  have hY := hu τ
  refine ⟨det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 _ hY, fun i => ?_⟩
  have hd : dmin X.Gm u τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hY, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp only [Function.comp_apply, Fin.coe_castLE, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

theorem maj_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj u τ v = ∑ a, ‖((mat u τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hY := hu τ
  set N : Fin r → Fin r → ℂ := fun i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hN
  have hw : mat u τ = mat u τ * Matrix.of N := by
    rw [show Matrix.of N = 1 from rfl, Matrix.mul_one]
  rw [maj_chart X hY N hw v]
  set w := (mat u τ)⁻¹ *ᵥ v
  have hsf : ∀ (α : Fin r → ℂ) (b : Fin r), sf X.p0 α (cl N b) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * α b := by
    intro α b
    unfold sf cl
    rw [Finset.sum_eq_single b]
    · simp [hN]
    · intro k _ hk
      simp [hN, Matrix.one_apply_ne hk]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hAg : Ag X.p0 X.p0_le N = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, hsf]
    by_cases hab : a = b
    · subst hab
      simp [cl, hN, sgn]
    · have hne : (Fin.castLE X.p0_le b : Fin r) ≠ Fin.castLE X.p0_le a :=
        fun h => hab (Fin.castLE_injective _ h).symm
      simp [cl, hN, Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hcast : ∀ g : Fin r → ℝ, ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then g k else 0 := by
    intro g
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun k : Fin r => (k : ℕ) < X.p0) =
        Finset.univ.map (Fin.castLEEmb X.p0_le) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hk
        exact ⟨⟨k, hk⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hset, Finset.sum_map]
    rfl
  have hinner : ∀ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 w (cl N (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 w (cl N (Fin.castLE X.p0_le b))) =
      ((‖w (Fin.castLE X.p0_le a)‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne' hb, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [Matrix.one_apply_eq, mul_one, hsf]
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp
    simp only [sgn, ha, if_true, Complex.ofReal_one, one_mul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hww : (sf X.p0 w w).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * ‖w k‖ ^ 2 := by
    unfold sf
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold Ms
  rw [hAg, inv_one]
  simp only [hinner]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, hww]
  have hc := hcast (fun k => ‖w k‖ ^ 2)
  beta_reduce at hc
  rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sgn
  split_ifs <;> ring

end ModeHalfA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {n : ℕ}

abbrev lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Matrix (Fin i) (Fin i) ℂ :=
  M.submatrix (Fin.castLE i.isLt.le) (Fin.castLE i.isLt.le)

theorem det_lb (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (lb M i).det = lminor M (Fin.castSucc i) := rfl

def wv (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Fin i → ℂ :=
  vecMul (fun j : Fin i => M i (Fin.castLE i.isLt.le j)) (lb M i)⁻¹

def Lm (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => if h : (k : ℕ) < i then -wv M i ⟨k, h⟩ else if k = i then 1 else 0

theorem row_expand (N M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1) :
    (N * M) i j = (∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j) + M i j := by
  classical
  rw [Matrix.mul_apply]
  have h1 : ∑ k : Fin n, N i k * M k j = ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), N i k * M k j := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · rw [hup k (lt_of_not_ge hk), zero_mul]
  have h2 : Finset.univ.filter (fun k : Fin n => k ≤ i) = insert i (Finset.univ.filter (fun k => k < i)) := by
    ext k
    simp [le_iff_lt_or_eq, or_comm]
  have h3 : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), N i k * M k j =
      ∑ k : Fin i, N i (Fin.castLE i.isLt.le k) * M (Fin.castLE i.isLt.le k) j := by
    refine Finset.sum_bij' (fun k hk => (⟨k, (Finset.mem_filter.mp hk).2⟩ : Fin i))
      (fun k _ => Fin.castLE i.isLt.le k) (fun _ _ => Finset.mem_univ _) (fun k _ => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact k.isLt
  rw [h1, h2, Finset.sum_insert (by simp), h3, hd, one_mul, add_comm]

theorem Lm_up (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin n) (h : i < k) : Lm M i k = 0 := by
  simp only [Lm, Matrix.of_apply]
  have h' : ¬ ((k : ℕ) < i) := by rw [Fin.lt_iff_val_lt_val] at h; omega
  rw [dite_eq_right h', if_neg (ne_of_gt h)]

theorem Lm_diag (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : Lm M i i = 1 := by
  simp [Lm]

theorem Lm_det (M : Matrix (Fin n) (Fin n) ℂ) : (Lm M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i k h => Lm_up M i k (OrderDual.toDual_lt_toDual.mp h))]
  simp [Lm_diag]

theorem row_sys (N M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hup : ∀ k : Fin n, i < k → N i k = 0) (hd : N i i = 1)
    (hz : ∀ j : Fin n, j < i → (N * M) i j = 0) :
    vecMul (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) (lb M i) =
      -fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
  funext j'
  have hrow := row_expand N M i (Fin.castLE i.isLt.le j') hup hd
  rw [hz _ (by simp [Fin.lt_iff_val_lt_val])] at hrow
  simp only [vecMul, dotProduct, lb, submatrix_apply, Pi.neg_apply]
  linear_combination (-1 : ℂ) * hrow

theorem Lm_mul_up (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (i j : Fin n) (h : j < i) : (Lm M * M) i j = 0 := by
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  rw [row_expand (Lm M) M i j (fun k hk => Lm_up M i k hk) (Lm_diag M i)]
  have hL : ∀ k : Fin i, Lm M i (Fin.castLE i.isLt.le k) = -wv M i k := by
    intro k
    simp only [Lm, Matrix.of_apply]
    rw [dite_eq_left (by simp)]
    rfl
  simp_rw [hL]
  have key : vecMul (wv M i) (lb M i) = fun j : Fin i => M i (Fin.castLE i.isLt.le j) := by
    rw [wv, vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, vecMul_one]
  have hk := congrFun key ⟨j, h⟩
  simp only [vecMul, dotProduct, lb, submatrix_apply] at hk
  have hk' : ∑ k : Fin i, wv M i k * M (Fin.castLE i.isLt.le k) j = M i j := hk
  simp only [neg_mul, Finset.sum_neg_distrib, hk', neg_add_cancel]

theorem Lm_unique (N M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k : Fin (n + 1), lminor M k ≠ 0)
    (hup : ∀ i k : Fin n, i < k → N i k = 0) (hd : ∀ i, N i i = 1)
    (hz : ∀ i j : Fin n, j < i → (N * M) i j = 0) : N = Lm M := by
  ext i k
  have hdet : IsUnit (lb M i).det := by rw [det_lb]; exact isUnit_iff_ne_zero.mpr (hM _)
  have h1 := row_sys N M i (hup i) (hd i) (hz i)
  have h2 := row_sys (Lm M) M i (fun k hk => Lm_up M i k hk) (Lm_diag M i)
    (fun j hj => Lm_mul_up M hM i j hj)
  have heq : (fun k : Fin i => N i (Fin.castLE i.isLt.le k)) = fun k => Lm M i (Fin.castLE i.isLt.le k) := by
    have h3 := congrArg (fun v => vecMul v (lb M i)⁻¹) (h1.trans h2.symm)
    simpa only [vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, vecMul_one] using h3
  rcases lt_trichotomy k i with hk | rfl | hk
  · exact congrFun heq ⟨k, hk⟩
  · rw [hd, Lm_diag]
  · rw [hup i k hk, Lm_up M i k hk]

theorem lminor_nb (N B : Matrix (Fin n) (Fin n) ℂ) (hup : ∀ i k : Fin n, i < k → N i k = 0)
    (hd : ∀ i, N i i = 1) (hB : B.BlockTriangular id) (k : Fin (n + 1)) :
    lminor (N * B) k = ∏ j : Fin k, B (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  set e : Fin k → Fin n := Fin.castLE (Nat.le_of_lt_succ k.isLt) with he
  have hmono : ∀ a b : Fin k, a < b → e a < e b := fun a b h => h
  have hsub : (N * B).submatrix e e = N.submatrix e e * B.submatrix e e := by
    ext a b
    simp only [submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective _) _ _ (fun c hc => ?_) (fun _ => rfl)
    have hc' : (k : ℕ) ≤ c := by
      by_contra hlt
      exact hc ⟨⟨c, by omega⟩, Fin.ext rfl⟩
    have hac : e a < c := by
      rw [Fin.lt_iff_val_lt_val]
      show (a : ℕ) < c
      omega
    rw [hup _ _ hac, zero_mul]
  have hNt : (N.submatrix e e).BlockTriangular OrderDual.toDual :=
    fun a b h => hup _ _ (hmono _ _ (OrderDual.toDual_lt_toDual.mp h))
  have hBt : (B.submatrix e e).BlockTriangular id := fun a b h => hB (hmono _ _ h)
  rw [lminor, ← he, hsub, det_mul, Matrix.det_of_lowerTriangular _ hNt,
    Matrix.det_of_upperTriangular hBt]
  simp [hd]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
end
