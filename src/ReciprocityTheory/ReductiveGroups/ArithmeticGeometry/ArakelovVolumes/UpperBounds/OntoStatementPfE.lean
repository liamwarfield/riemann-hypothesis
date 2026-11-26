module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem chi_norm (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1

theorem bchar_ne (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 := by
  have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  unfold bchar
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hd := (hb' τ).1
  have hbt : (mat b τ).BlockTriangular id := fun a c hca => (hb' τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff] at hd
  have hi := hd i (Finset.mem_univ _)
  exact zpow_ne_zero _ hi


open Classical in
def phiF (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) : Frame X.Ψ r → ℝ≥0∞ :=
  fun y => X.dom.piecewise (fun y => ENNReal.ofReal (‖f0 y‖ ^ 2)) 0 y * W y

theorem phiF_dom (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiF X f0 W x = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by
  simp [phiF, Set.piecewise, hx]

theorem phiF_meas {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hf : ContinuousOn f0 X.dom)
    (hW : Measurable W) : Measurable (phiF X f0 W) := by
  classical
  have hopen : IsOpen X.dom := by
    have h1 : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
      rfl
    rw [h1]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · refine isOpen_ne_fun ?_ continuous_const
      unfold mat
      fun_prop
    · refine isOpen_lt continuous_const ?_
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
  unfold phiF
  refine Measurable.mul ?_ hW
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hopen.measurableSet
  exact ENNReal.continuous_ofReal.comp_continuousOn (hf.norm.pow 2)

theorem phiF_B {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phiF X f0 W (rmul x b) = phiF X f0 W x := by
  intro x hx b hb
  rw [phiF_dom X f0 W (dom_rmul X hx hb), phiF_dom X f0 W hx, hf0 x hx b hb, hW.2.1 x hx b hb,
    norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  have hA0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 (bchar_ne X la hb)) 2
  have hAt : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.div_eq_inv_mul]
  calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
        ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W x)
      = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x *
          (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) := by ring
    _ = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by rw [ENNReal.mul_inv_cancel hA0 hAt, mul_one]

theorem phiF_G {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : IsMetricW X la W) : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phiF X f0 W (lact γ x) = phiF X f0 W x := by
  intro γ hγ x hx
  rw [phiF_dom X f0 W (dom_lact X hγ hx), phiF_dom X f0 W hx, hf0 γ hγ x hx, hW.2.2 γ hγ x hx,
    norm_mul, chi_norm X la hγ, one_mul]

variable (x0 : Frame X.Ψ r)

theorem nfac_pos {la : Wt X.Ψ r} {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < X.nfac la (cpt X x0 z) := by
  have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
  have hd : ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro τ i h
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply Finset.prod_pos
  intro τ _
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem nfac_cont (la : Wt X.Ψ r) : ContinuousOn (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have hn : Continuous fun z : V (nd X) => nmat X z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    unfold nmat
    by_cases h : b < a
    · simp only [h, dif_pos]
      fun_prop
    · simp only [h, dif_neg, not_false_eq_true]
      exact continuous_const
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => ?_
    show Continuous fun z : V (nd X) => mat x0 τ * mat (nmat X z) τ
    exact continuous_const.matrix_mul ((continuous_apply τ).comp hn)
  have hd : ∀ τ i, Continuous fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
    intro τ i
    have h1 : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
    exact h1.comp hc
  have hne : ∀ z ∈ OmF X x0, ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro z hz τ i h
    have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply continuousOn_finsetProd
  intro τ _
  apply continuousOn_finsetProd
  intro i _
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.rpow_const
  · exact ((hd τ _).continuousAt.div (hd τ _).continuousAt (hne z hz τ _)).norm
  · left
    exact norm_ne_zero_iff.mpr (div_ne_zero (hne z hz τ _) (hne z hz τ _))

theorem expPhla_cont (la : Wt X.Ψ r) :
    ContinuousOn (fun z => Real.exp (-phla X la (cpt X x0 z))) (OmF X x0) := by
  unfold phla
  have h1 := nfac_cont X x0 la
  exact (continuousOn_const.mul (h1.log fun z hz => (nfac_pos X x0 (la := la) hz).ne')).neg.rexp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_dmin (τ : X.Ψ) (i : Fin (r + 1)) : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
  unfold dmin lminor gram hermC col mat
  first
    | fun_prop
    | (apply Continuous.matrix_det; apply Continuous.matrix_submatrix; fun_prop)
    | continuity

theorem nfac_contOn (la : Wt X.Ψ r) : ContinuousOn (X.nfac la) X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hne : ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro x hx τ i h0
    have h1 := (hx τ).2 i
    rw [h0] at h1
    simp at h1
  unfold Data.nfac
  apply continuousOn_finsetProd
  intro τ _
  apply continuousOn_finsetProd
  intro i _
  apply ContinuousOn.rpow_const
  · exact (((hd τ i.succ).continuousOn).div ((hd τ i.castSucc).continuousOn)
      (fun x hx => hne x hx τ i.castSucc)).norm
  · intro x hx
    left
    exact norm_ne_zero_iff.2 (div_ne_zero (hne x hx τ i.succ) (hne x hx τ i.castSucc))

variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)

def Gf (x : Frame X.Ψ r) : ℝ≥0∞ := ENNReal.ofReal (X.pnorm la (P0 D la F) x ^ 2)

private lemma dom_isOpen : IsOpen X.dom := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    first
      | exact Continuous.matrix_det (continuous_apply τ)
      | (unfold mat; fun_prop)
  show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isOpen_iInter_of_finite fun τ => ?_
  refine (isOpen_ne_fun (hdet τ) continuous_const).inter (isOpen_iInter_of_finite fun i => ?_)
  exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hd τ i)))

private lemma continuous_cpt' : Continuous (cpt X x0) := by
  have hn : ∀ (τ : X.Ψ) (a b : Fin r), Continuous fun z : V (nd X) => nmat X z τ a b := by
    intro τ a b
    by_cases h : b < a
    · simp only [nmat, dif_pos h]
      first
        | exact (EuclideanSpace.proj (𝕜 := ℂ) _).continuous
        | fun_prop
    · by_cases h' : a = b
      · simp only [nmat, dif_neg h, if_pos h']
        exact continuous_const
      · simp only [nmat, dif_neg h, if_neg h']
        exact continuous_const
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun z => ∑ k, mat x0 τ a k * mat (nmat X z) τ k b
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hn τ k b)

private lemma bor_diag_ne_zero {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ)
    (i : Fin r) : b τ i i ≠ 0 := by
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (by intro a c hca; exact (hb τ).2 a c hca)] at h
  exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ _)

theorem Gf_meas (hF : DifferentiableOn ℂ F (OmF X x0)) : Measurable (Gf D la F) := by
  classical
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i :=
    fun τ i => cont_dmin X τ i
  have hcellO : IsOpen (cell D) := by
    have hc : cell D = X.dom ∩ {x | D.Δ x ≠ 0} := rfl
    rw [hc]
    exact dom_isOpen.inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hfc : ContinuousOn (fun x => bchar la (D.bOf x) * F (D.zOf x)) (cell D) := by
    have hzc : ContinuousOn D.zOf (cell D) := D.hz.continuousOn
    have hbc : ContinuousOn D.bOf (cell D) := D.hb.continuousOn
    have hsplit : ∀ x ∈ cell D, D.zOf x ∈ OmF X x0 ∧ D.bOf x ∈ Bor X.Ψ r :=
      fun x hx => ⟨(D.split x hx.1 hx.2).1, (D.split x hx.1 hx.2).2.1⟩
    refine ContinuousOn.mul ?_ (hF.continuousOn.comp hzc fun x hx => (hsplit x hx).1)
    unfold bchar
    apply continuousOn_finsetProd
    intro τ _
    apply continuousOn_finsetProd
    intro i _
    apply ContinuousOn.zpow₀
    · have hent : Continuous fun y : Frame X.Ψ r => y τ i i := by
        first
          | fun_prop
          | continuity
      exact hent.comp_continuousOn hbc
    · intro x hx
      left
      exact bor_diag_ne_zero (hsplit x hx).2 τ i
  have hP : P0 D la F = (cell D).piecewise (fun x => bchar la (D.bOf x) * F (D.zOf x)) 0 := by
    funext x
    by_cases h : x ∈ cell D
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact if_pos h
    · first
        | rw [Set.piecewise_eq_of_notMem _ _ _ h]
        | rw [Set.piecewise_eq_of_not_mem _ _ _ h]
      exact if_neg h
  have hPm : Measurable (P0 D la F) := by
    rw [hP]
    exact hfc.measurable_piecewise continuous_zero.continuousOn hcellO.measurableSet
  have hnf : Measurable fun x => X.nfac la x := by
    unfold Data.nfac
    apply Finset.measurable_prod
    intro τ _
    apply Finset.measurable_prod
    intro i _
    exact (((hd τ i.succ).measurable.div (hd τ i.castSucc).measurable).norm).pow_const _
  have hp : ∀ x, X.pnorm la (P0 D la F) x = ‖P0 D la F x‖ * X.nfac la x := fun x => rfl
  unfold Gf
  simp only [hp]
  first
    | exact ((hPm.norm.mul hnf).pow_const 2).ennreal_ofReal
    | exact ENNReal.measurable_ofReal.comp ((hPm.norm.mul hnf).pow_const 2)

theorem Gf_inv {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    Gf D la F (rmul x b) = Gf D la F x := by
  unfold Gf
  rw [FrameDegreeData.pnorm_rmul X la _ (fun y hy b' hb' => poincareLift_borel_equivariant D la F hy hb') x hx b hb]

private lemma one_mem_bor_upper_bounds {Ψ : Finset (E →+* ℂ)} :
    (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame Ψ r) ∈ Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne hca.ne'

theorem Gf_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Gf D la F (cpt X x0 z) = ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) := by
  have hzd : cpt X x0 z ∈ X.dom := hz
  have hne : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hzd τ).2 i
    rw [h0] at h1
    simp at h1
  have hpos : 0 < X.nfac la (cpt X x0 z) := by
    unfold Data.nfac
    apply Finset.prod_pos
    intro τ _
    apply Finset.prod_pos
    intro i _
    apply Real.rpow_pos_of_pos
    exact norm_pos_iff.2 (div_ne_zero (hne τ i.succ) (hne τ i.castSucc))
  have hr1 : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = cpt X x0 z := by
    funext τ
    exact Matrix.mul_one (mat (cpt X x0 z) τ)
  obtain ⟨hΔ, hzo, hbo⟩ := D.uniq z hz _ one_mem_bor_upper_bounds
  rw [hr1] at hΔ hzo hbo
  have hP : P0 D la F (cpt X x0 z) = F z := by
    unfold P0
    rw [if_pos (show cpt X x0 z ∈ X.dom ∧ D.Δ (cpt X x0 z) ≠ 0 from ⟨hzd, hΔ⟩), hzo, hbo]
    simp [bchar]
  unfold Gf
  have hp : X.pnorm la (P0 D la F) (cpt X x0 z) =
      ‖P0 D la F (cpt X x0 z)‖ * X.nfac la (cpt X x0 z) := rfl
  rw [hp, hP]
  congr 1
  unfold phla
  have hl : -(-2 * Real.log (X.nfac la (cpt X x0 z))) = Real.log (X.nfac la (cpt X x0 z) ^ 2) := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hl, Real.exp_log (pow_pos hpos 2), mul_pow]

theorem norm_poincareLift_sq_le {x : Frame X.Ψ r} (_hx : x ∈ X.dom) {m : ℝ} (hm : 0 < m) (hmx : m ≤ X.nfac la x) :
    ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * Gf D la F x := by
  unfold Gf
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg m))]
  apply ENNReal.ofReal_le_ofReal
  have hp : X.pnorm la (P0 D la F) x = ‖P0 D la F x‖ * X.nfac la x := rfl
  rw [hp]
  have hm2 : 0 < m ^ 2 := by positivity
  have h1 : m ^ 2 ≤ X.nfac la x ^ 2 := by
    have := hm.le
    gcongr
  have h2 : 1 ≤ (m ^ 2)⁻¹ * X.nfac la x ^ 2 := by
    rw [inv_mul_eq_div, one_le_div hm2]
    exact h1
  rw [mul_pow, ← mul_assoc, mul_comm ((m ^ 2)⁻¹), mul_assoc]
  exact le_mul_of_one_le_right (sq_nonneg _) h2

theorem ae_OmF : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
  have hmeas : MeasurableSet (OmF X x0) :=
    (dom_isOpen.preimage continuous_cpt').measurableSet
  unfold muF
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hmeas)

theorem poincareLift_locally_squareIntegrable (hM : FrameMeasStatement (E := E)) (hx0 : IsOrth X x0)
    (hF : DifferentiableOn ℂ F (OmF X x0))
    (hL2 : ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤)
    {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2) < ⊤ := by
  obtain ⟨K, hK, hKG⟩ := hM r X x0 hx0 C hC hCd
  obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ C, m ≤ X.nfac la x := by
    rcases C.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨x1, hx1, hmin⟩ := hC.exists_isMinOn h ((nfac_contOn X la).mono hCd)
    exact ⟨X.nfac la x1, FlowCoefficientBounds.nfac_pos X (hCd hx1) la, fun x hx => hmin hx⟩
  have h1 : ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤
      ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ x in C, Gf D la F x := by
    rw [← lintegral_const_mul _ (Gf_meas D la F hF)]
    exact setLIntegral_mono' hC.measurableSet fun x hx => norm_poincareLift_sq_le D la F (hCd hx) hm (hmC x hx)
  have h2 := hKG (Gf D la F) (Gf_meas D la F hF) fun x hx b hb => Gf_inv D la F hx hb
  have h3 : ∫⁻ z in sat X x0 C, Gf D la F (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_OmF (x0 := x0))] with z hz
    rw [Gf_cpt D la F hz]
  calc ∫⁻ x in C, ENNReal.ofReal (‖P0 D la F x‖ ^ 2)
      ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * (K * ∫⁻ z in sat X x0 C,
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0) :=
        h1.trans (mul_le_mul' le_rfl (h2.trans (mul_le_mul' le_rfl h3)))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hK (hL2 C hC hCd))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

noncomputable section

theorem levi_logNormSq_zero {n : ℕ} (h : V n → ℂ) (hh : ContDiff ℂ ∞ h) (v0 : V n)
    (hne : h v0 ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Real.log (Complex.normSq (h y)) : ℝ) : ℂ)) v0 ξ = 0 := by
  have hl := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n 1 (fun _ => h) v0 ξ
    (fun _ => hh.contDiffAt.of_le two_le_infty) (by intro h'; exact hne (congrFun h' 0))
  have e1 : (fun y => ((Real.log (sqNorm (fun i : Fin 1 => (fun _ => h) i y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (Complex.normSq (h y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm]
  rw [e1] at hl
  rw [hl]
  have hn : (Complex.normSq (h v0) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.2 hne).ne'
  have hP : projPerp (fun _ : Fin 1 => h v0) = 0 := by
    ext i l
    fin_cases i; fin_cases l
    simp [projPerp, sqNorm, vecMulVec_apply, Complex.mul_conj, hn]
  simp [hP, sqNorm]

theorem leviT_nonneg {n : ℕ} (v0 : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ)) v0 ξ).re := by
  let g : Fin (n + 1) → V n → ℂ := fun i =>
    Fin.cons (α := fun _ => V n → ℂ) (fun _ : V n => (1 : ℂ)) (fun j : Fin n => fun y : V n => y j) i
  have hc : ∀ i, ContDiffAt ℂ 2 (g i) v0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [g, Fin.cons_zero]; exact contDiffAt_const
    · simp only [g, Fin.cons_succ]; exact (cd_coord _).contDiffAt.of_le two_le_infty
  have hne : (fun i => g i v0) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [g] at this
  have h := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n (n + 1) g v0 ξ hc hne
  have e1 : (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := by
    funext y
    simp [sqNorm, Fin.sum_univ_succ, g, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
  rw [e1] at h
  rw [h, Complex.ofReal_re]
  exact div_nonneg (sqNorm_nonneg' _) (sqNorm_nonneg' _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem rhF_eq_log (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {y : V (nd X)} (hy : y ∈ OmF X x0) :
    rhF X x0 y = -Real.log (∏ τ, (Am X y τ).det.re) := by
  have key : ∀ τ, 0 < (Am X y τ).det.re ∧ ‖(Am X y τ).det‖ = (Am X y τ).det.re := by
    intro τ
    have hpos := ((mem_OmF_iff X x0 ho y).1 hy τ).det_pos
    have h := Complex.lt_def.1 hpos
    simp only [Complex.zero_re, Complex.zero_im] at h
    refine ⟨h.1, ?_⟩
    rw [show (Am X y τ).det = ((Am X y τ).det.re : ℂ) from Complex.ext (by simp) (by simp [← h.2])]
    rw [Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg h.1.le]
  rw [rhF_eq_sum X x0 ho y, Real.log_prod (fun τ _ => (key τ).1.ne')]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by rw [(key τ).2]

theorem levi_rhF_nonneg (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z0 : V (nd X)} (hz0 : z0 ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z0 ξ).re := by
  set Hf : V (nd X) → ℂ := fun y => ∏ τ, (1 - Zt X y τ * (Zt X z0 τ)ᴴ).det with hHf
  have hHcd : ContDiff ℂ ∞ Hf := by
    refine contDiff_prod fun τ _ => contDiff_det_of fun a b => ?_
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
    exact contDiff_const.sub (ContDiff.sum fun c _ => (cd_Zt X τ a c).mul contDiff_const)
  set P : V (nd X) → ℝ := fun y => ∏ τ, (Am X y τ).det.re with hP
  have hAm : ∀ y ∈ OmF X x0, ∀ τ, (Am X y τ).PosDef := fun y hy => (mem_OmF_iff X x0 ho y).1 hy
  have hPpos : ∀ y ∈ OmF X x0, 0 < P y := fun y hy =>
    Finset.prod_pos fun τ _ => (det_re_pos_im (hAm y hy τ)).1
  have hle : ∀ y ∈ OmF X x0, P y * P z0 ≤ Complex.normSq (Hf y) := by
    intro y hy
    simp only [hP, hHf]
    rw [← Finset.prod_mul_distrib, map_prod]
    exact Finset.prod_le_prod₀ (fun τ _ => mul_nonneg (det_re_pos_im (hAm y hy τ)).1.le
      (det_re_pos_im (hAm z0 hz0 τ)).1.le)
      (fun τ _ => det_mul_det_le_normSq_det _ _ (hAm y hy τ) (hAm z0 hz0 τ))
  have hself : Complex.normSq (Hf z0) = P z0 * P z0 := by
    simp only [hP, hHf]
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : (1 - Zt X z0 τ * (Zt X z0 τ)ᴴ) = Am X z0 τ := rfl
    rw [e, det_eq_ofReal (hAm z0 hz0 τ), Complex.normSq_ofReal]
    simp
  set F : V (nd X) → ℝ := fun y => rhF X x0 y + Real.log (Complex.normSq (Hf y)) with hF
  have hmin : ∀ y ∈ OmF X x0, F z0 ≤ F y := by
    intro y hy
    have h2 := Real.log_le_log (mul_pos (hPpos y hy) (hPpos z0 hz0)) (hle y hy)
    rw [Real.log_mul (hPpos y hy).ne' (hPpos z0 hz0).ne'] at h2
    have h3 : F z0 = Real.log (P z0) := by
      simp only [hF]
      rw [hself, rhF_eq_log X x0 ho hz0, Real.log_mul (hPpos z0 hz0).ne' (hPpos z0 hz0).ne']
      ring
    rw [h3]
    simp only [hF]
    rw [rhF_eq_log X x0 ho hy]
    linarith
  have hmax : IsLocalMax (fun y => -F y) z0 := by
    have : IsLocalMin F z0 :=
      Filter.eventually_of_mem ((isOpen_OmF X x0).mem_nhds hz0) fun y hy => hmin y hy
    exact this.neg
  have hNpos : Complex.normSq (Hf z0) ≠ 0 := by
    rw [hself]; have := hPpos z0 hz0; positivity
  have hHne : Hf z0 ≠ 0 := fun h => hNpos (by rw [h]; simp)
  have hc1 : ContDiffAt ℝ 2 (fun y => rhF X x0 y) z0 := (rhF_contDiffAt X x0 ho hz0).of_le two_le_infty
  have hc2 : ContDiffAt ℝ 2 (fun y => Real.log (Complex.normSq (Hf y))) z0 := by
    have hn : ContDiff ℝ ∞ fun y : V (nd X) => Complex.normSq (Hf y) := by
      simp only [Complex.normSq_eq_norm_sq]
      exact (contDiff_norm_sq ℝ).comp (hHcd.restrict_scalars ℝ)
    exact ((Real.contDiffAt_log.2 hNpos).comp z0 hn.contDiffAt).of_le two_le_infty
  have hcF : ContDiffAt ℝ 2 F z0 := hc1.add hc2
  have h1 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcF.neg hmax ξ
  have e1 : (fun y => ((-F y : ℝ) : ℂ)) = fun y => (((-1) * F y : ℝ) : ℂ) := by
    funext y; simp
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hcF ξ] at h1
  have e2 : (fun y => ((F y : ℝ) : ℂ)) =
      fun y => ((rhF X x0 y + Real.log (Complex.normSq (Hf y)) : ℝ) : ℂ) := rfl
  rw [e2, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hc1 hc2 ξ,
    levi_logNormSq_zero Hf hHcd z0 hHne ξ] at h1
  simp at h1
  linarith

private theorem det_one_sub_mul_conjTranspose_mem_Icc {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - Z * Zᴴ).PosSemidef) :
    0 ≤ (1 - Z * Zᴴ).det.re ∧ (1 - Z * Zᴴ).det.re ≤ 1 ∧ ‖(1 - Z * Zᴴ).det‖ = (1 - Z * Zᴴ).det.re := by
  have hH : (1 - Z * Zᴴ).IsHermitian := h.isHermitian
  have hev : ∀ i, 0 ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ 1 := by
    intro i
    refine ⟨h.eigenvalues_nonneg i, ?_⟩
    rw [hH.eigenvalues_eq i]
    set v := (hH.eigenvectorBasis i).ofLp with hvdef
    have hv : star v ⬝ᵥ v = 1 := by
      have h1 : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
      rw [hvdef]
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
      push_cast at h2
      exact h2
    have hq : 0 ≤ star v ⬝ᵥ (Z * Zᴴ) *ᵥ v := (posSemidef_self_mul_conjTranspose Z).dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hv, map_sub, RCLike.one_re]
    have := (RCLike.nonneg_iff.1 hq).1
    linarith
  have hd : (1 - Z * Zᴴ).det = ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have h0 : 0 ≤ ∏ i, hH.eigenvalues i := Finset.prod_nonneg fun i _ => (hev i).1
  rw [hd, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg h0]
  exact ⟨h0, Finset.prod_le_one₀ (fun i _ => (hev i).1) fun i _ => (hev i).2, rfl⟩

theorem rhF_nonneg (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 ≤ rhF X x0 z := by
  rw [rhF_eq_sum X x0 ho z, neg_nonneg]
  refine Finset.sum_nonpos fun τ _ => Real.log_nonpos (norm_nonneg _) ?_
  obtain ⟨h0, h1, h2⟩ : 0 ≤ (Am X z τ).det.re ∧ (Am X z τ).det.re ≤ 1 ∧ ‖(Am X z τ).det‖ = (Am X z τ).det.re :=
    det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) ((mem_OmF_iff X x0 ho z).1 hz τ).posSemidef
  rw [h2]
  exact h1

theorem sub_eqF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (a : ℝ) :
    {z : V (nd X) | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} =
      {z | (∀ τ, (Am X z τ).PosSemidef) ∧
        Real.exp (Real.log (1 + ‖z‖ ^ 2) - a) ≤ ∏ τ, (Am X z τ).det.re} := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hle⟩
    have hpd := (mem_OmF_iff X x0 ho z).1 hz
    refine ⟨fun τ => (hpd τ).posSemidef, ?_⟩
    have hpos : ∀ τ, 0 < (Am X z τ).det.re := fun τ => by
      have h := Complex.lt_def.1 (hpd τ).det_pos
      simp only [Complex.zero_re] at h
      exact h.1
    unfold eF at hle
    rw [rhF_eq_log X x0 ho hz] at hle
    have hP : 0 < ∏ τ, (Am X z τ).det.re := Finset.prod_pos fun τ _ => hpos τ
    rw [← Real.exp_log hP]
    exact Real.exp_le_exp.2 (by linarith)
  · rintro ⟨hpsd, hle⟩
    have hP : 0 < ∏ τ, (Am X z τ).det.re := lt_of_lt_of_le (Real.exp_pos _) hle
    have hpos : ∀ τ, 0 < (Am X z τ).det.re := by
      intro τ
      obtain ⟨h0, -, -⟩ : 0 ≤ (Am X z τ).det.re ∧ (Am X z τ).det.re ≤ 1 ∧
          ‖(Am X z τ).det‖ = (Am X z τ).det.re := det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)
      rcases h0.eq_or_lt with h0 | h0
      · exact absurd hP (by rw [Finset.prod_eq_zero (Finset.mem_univ τ) h0.symm]; exact lt_irrefl 0)
      · exact h0
    have hz : z ∈ OmF X x0 := (mem_OmF_iff X x0 ho z).2 fun τ => ((hpsd τ).posDef_iff_isUnit).2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h => by
        have := hpos τ
        rw [h, Complex.zero_re] at this
        exact lt_irrefl 0 this))
    refine ⟨hz, ?_⟩
    unfold eF
    rw [rhF_eq_log X x0 ho hz]
    have := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at this
    linarith

theorem isClosed_psdF : IsClosed {z : V (nd X) | ∀ τ, (Am X z τ).PosSemidef} := by
  have hset : {z : V (nd X) | ∀ τ, (Am X z τ).PosSemidef} =
      ⋂ τ, ⋂ x : Fin X.p0 → ℂ, {z | 0 ≤ star x ⬝ᵥ (Am X z τ) *ᵥ x} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h τ x => (h τ).dotProduct_mulVec_nonneg x, fun h τ => ?_⟩
    exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_one.sub (Matrix.isHermitian_mul_conjTranspose_self _)) (h τ)
  rw [hset]
  refine isClosed_iInter fun τ => isClosed_iInter fun x => ?_
  have he : ∀ a c, Continuous fun z : V (nd X) => Am X z τ a c := fun a c => (cd_Am_entry X τ a c).continuous
  have hf : Continuous fun z : V (nd X) => star x ⬝ᵥ (Am X z τ) *ᵥ x := by
    simp only [dotProduct, Matrix.mulVec]
    exact continuous_finsetSum _ fun a _ =>
      continuous_const.mul (continuous_finsetSum _ fun c _ => (he a c).mul continuous_const)
  exact isClosed_le continuous_const hf

theorem isCompact_subF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (a : ℝ) : IsCompact {z : V (nd X) | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} := by
  rw [sub_eqF X x0 ho a, Set.setOf_and]
  apply Metric.isCompact_of_isClosed_isBounded
  · refine (isClosed_psdF X).inter (isClosed_le ?_ ?_)
    · exact Real.continuous_exp.comp ((Continuous.log (continuous_const.add (continuous_norm.pow 2))
        fun z => (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2).ne').sub continuous_const)
    · exact continuous_finsetProd _ fun τ _ => Complex.continuous_re.comp (cd_detAm X τ).continuous
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.exp a, fun z hz => ?_⟩
    obtain ⟨hpsd, hle⟩ := hz
    have hP : ∏ τ, (Am X z τ).det.re ≤ 1 :=
      Finset.prod_le_one₀ (fun τ _ => (det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)).1)
        fun τ _ => (det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)).2.1
    have h1 : Real.log (1 + ‖z‖ ^ 2) - a ≤ 0 := Real.exp_le_one_iff.1 (le_trans hle hP)
    have h2 : 1 + ‖z‖ ^ 2 ≤ Real.exp a := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2)]
      exact Real.exp_le_exp.2 (by linarith)
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem val_lh (hU : IsOpen U) : IsLocalHomeomorph (Subtype.val : U → V n) :=
  hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph

theorem symm_val {e : OpenPartialHomeomorph U (V n)} (he : IsChart n (Subtype.val : U → V n) e)
    {y : V n} (hy : y ∈ e.target) : ((e.symm y : U) : V n) = y :=
  (he (e.map_target hy)).trans (e.right_inv hy)

theorem target_sub {e : OpenPartialHomeomorph U (V n)} (he : IsChart n (Subtype.val : U → V n) e) :
    e.target ⊆ U := fun y hy => by
  rw [← symm_val he hy]
  exact (e.symm y).2

theorem comp_symm_eqOn (f : V n → ℂ) {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) :
    Set.EqOn ((fun x : U => f x.1) ∘ e.symm) f e.target := fun y hy => by
  simp only [Function.comp]
  rw [symm_val he hy]

theorem smooth_val {f : V n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    Smooth n (Subtype.val : U → V n) (fun x => f x.1) := fun e he =>
  (hf.mono (target_sub he)).congr (comp_symm_eqOn f he)

theorem smoothR_val {f : V n → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    SmoothR n (Subtype.val : U → V n) (fun x => f x.1) :=
  smooth_val (f := fun y => (f y : ℂ)) (Complex.ofRealCLM.contDiff.comp_contDiffOn hf)

theorem eventually_target (hU : IsOpen U) {e : OpenPartialHomeomorph U (V n)}
    (he : IsChart n (Subtype.val : U → V n) e) {x : U} (hx : x ∈ e.source) :
    e.target ∈ 𝓝 x.1 := by
  have hx' : x.1 ∈ e.target := by
    rw [show x.1 = e x from he hx]
    exact e.map_source hx
  exact e.open_target.mem_nhds hx'

theorem levi_val (hU : IsOpen U) (f : V n → ℝ) (x : U) (ξ : Fin n → ℂ) :
    Levi n (Subtype.val : U → V n) (fun y => f y.1) x ξ = leviV n (fun y => (f y : ℂ)) x.1 ξ := by
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) x
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  exact leviV_congr ((comp_symm_eqOn (fun y => (f y : ℂ)) he).eventuallyEq_of_mem
    (eventually_target hU he hx)) ξ

theorem db_val (hU : IsOpen U) (f : V n → ℂ) (j : Fin n) (x : U) :
    db n (Subtype.val : U → V n) j (fun y => f y.1) x = wdb n j f x.1 := by
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) x
  rw [db_eq_wdb n _ e he j _ x hx]
  have hfe : ((fun y : U => f y.1) ∘ e.symm) =ᶠ[𝓝 x.1] f :=
    (comp_symm_eqOn f he).eventuallyEq_of_mem (eventually_target hU he hx)
  simp only [wdb]
  rw [hfe.fderiv_eq]

def ext0 (F : U → ℂ) (y : V n) : ℂ := by
  classical
  exact if h : y ∈ U then F ⟨y, h⟩ else 0

theorem extendByZeroOnSubset_apply_coe (F : U → ℂ) (x : U) : ext0 F x.1 = F x := by
  simp [ext0, x.2]

theorem differentiableOn_extendByZero (hU : IsOpen U) {F : U → ℂ} (hF : Holo n (Subtype.val : U → V n) F) :
    DifferentiableOn ℂ (ext0 F) U := by
  intro y hy
  obtain ⟨e, he, hx⟩ := exists_chart n (Subtype.val : U → V n) (val_lh hU) ⟨y, hy⟩
  have hT : e.target ∈ 𝓝 y := eventually_target hU he hx
  have hd : DifferentiableAt ℂ (F ∘ e.symm) y := (hF e he).differentiableAt hT
  have heq : (F ∘ e.symm) =ᶠ[𝓝 y] ext0 F := by
    refine Filter.eventuallyEq_of_mem hT fun w hw => ?_
    have h1 := extendByZeroOnSubset_apply_coe F (e.symm w)
    rw [symm_val he hw] at h1
    exact h1.symm
  exact (hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt

private theorem volFun_val_eq_volume_image (hU : IsOpen U) (A : Set U) (hA : MeasurableSet A) :
    volFun n (Subtype.val : U → V n) A = volume (Subtype.val '' A) := by
  have key : ∀ y : V n, ((A ∩ Subtype.val ⁻¹' {y}).encard : ℝ≥0∞) =
      (Subtype.val '' A).indicator 1 y := by
    intro y
    by_cases hy : y ∈ Subtype.val '' A
    · obtain ⟨x, hxA, rfl⟩ := hy
      have hs : A ∩ Subtype.val ⁻¹' {x.1} = {x} := by
        ext z
        constructor
        · rintro ⟨-, hz⟩
          exact Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hz))
        · intro hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨hxA, rfl⟩
      rw [hs, Set.encard_singleton, Set.indicator_of_mem (Set.mem_image_of_mem _ hxA)]
      simp
    · have hs : A ∩ Subtype.val ⁻¹' {y} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hz hzy
        exact hy ⟨z, hz, hzy⟩
      rw [hs, Set.encard_empty]
      simp [Set.indicator, hy]
  rw [volFun, lintegral_congr key, lintegral_indicator_one (hU.measurableSet.subtype_image hA)]

theorem vol_val (hU : IsOpen U) :
    vol n (Subtype.val : U → V n) = Measure.comap Subtype.val volume := by
  have hadd : VolAdditive n (Subtype.val : U → V n) := by
    intro f hf hd
    rw [volFun_val_eq_volume_image hU _ (MeasurableSet.iUnion hf), Set.image_iUnion]
    rw [measure_iUnion (fun i j hij => (hd hij).image Subtype.val_injective.injOn
      (Set.subset_univ _) (Set.subset_univ _)) (fun i => hU.measurableSet.subtype_image (hf i))]
    exact tsum_congr fun i => (volFun_val_eq_volume_image hU _ (hf i)).symm
  ext A hA
  rw [vol, dite_eq_left hadd, Measure.ofMeasurable_apply _ hA,
    Measure.comap_apply _ Subtype.val_injective (fun s hs => hU.measurableSet.subtype_image hs) _ hA]
  exact volFun_val_eq_volume_image hU A hA

theorem lintegral_val (hU : IsOpen U) (g : V n → ℝ≥0∞) :
    ∫⁻ x, g x.1 ∂vol n (Subtype.val : U → V n) = ∫⁻ y in U, g y := by
  rw [vol_val hU]
  exact lintegral_subtype_comap hU.measurableSet g

theorem hormander_open (hU : IsOpen U) (e : V n → ℝ) (he : ContDiffOn ℝ ∞ e U)
    (hel : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re)
    (hec : ∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a})
    (φ : V n → ℝ) (hφ : ContDiffOn ℝ ∞ φ U)
    (hφl : ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ w : ℂ)) y ξ).re)
    (F0 : V n → ℂ) (hF0 : ContDiffOn ℝ ∞ F0 U) (h : V n → ℝ≥0∞) (hh : Measurable h)
    (hb : ∀ y ∈ U, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2 * Real.exp (-φ y)) ≤
        ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) := by
  let X : EtaleStein n U :=
    { z := Subtype.val
      isLocalHomeomorph := val_lh hU
      e := fun x => e x.1
      smooth_e := smoothR_val he
      levi_e := fun x ξ => by rw [levi_val hU]; exact hel x.1 x.2 ξ
      isCompact_le := fun a => by
        rw [Subtype.isCompact_iff]
        convert hec a using 1
        ext y
        simp [and_comm] }
  obtain ⟨F, hFh, hFi⟩ := ReciprocityTheory.L2DbarEstimates.hormander n U X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1) (smoothR_val hφ) (fun x ξ => by rw [levi_val hU]; exact hφl x.1 x.2 ξ)
    (smooth_val hF0) (hh.comp measurable_subtype_coe) (fun x ξ => by
      show ENNReal.ofReal (‖dbarDot n (Subtype.val : U → V n) (fun x => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n (Subtype.val : U → V n) (fun x => φ x.1) x ξ).re
      rw [levi_val hU, dbarDot]
      simp only [db_val hU]
      exact hb x.1 x.2 ξ)
  refine ⟨ext0 F, differentiableOn_extendByZero hU hFh, ?_⟩
  have e1 : ∫⁻ y in U, ENNReal.ofReal (‖F0 y - ext0 F y‖ ^ 2 * Real.exp (-φ y)) =
      wint n (Subtype.val : U → V n) (fun x => F0 x.1 - F x) (fun x => φ x.1) := by
    rw [wint, ← lintegral_val hU]
    refine lintegral_congr fun x => ?_
    simp only [extendByZeroOnSubset_apply_coe]
  have e2 : ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ y)) =
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : U → V n) :=
    (lintegral_val hU _).symm
  rw [e1, e2]
  exact hFi

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end
