module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import Lemmata.GeneralBFactVersion.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
  Metric Polynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x0 : Frame X.Ψ r}

theorem lminor_one (k : Fin (r + 1)) : lminor (1 : Matrix (Fin r) (Fin r) ℂ) k = 1 := by
  unfold lminor
  rw [Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]

theorem orthogonalFrame_delta_eq_one (hx0 : IsOrth X x0) : DeltaF X x0 x0 = 1 := by
  unfold DeltaF
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
  have h : Mx X x0 x0 τ = 1 := by
    unfold Mx
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (orthogonalFrame_det_ne_zero (X := X) (x0 := x0) hx0 τ))
  rw [h, lminor_one]

def linePoly (x v : Frame X.Ψ r) : ℂ[X] :=
  ∏ τ, ∏ k : Fin (r + 1),
    (((Mx X x0 x τ).map C + (Polynomial.X : ℂ[X]) • ((mat x0 τ)⁻¹ * mat v τ).map C).submatrix
      (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det

theorem linePoly_eval (x v : Frame X.Ψ r) (t : ℂ) :
    (linePoly (x0 := x0) x v).eval t = DeltaF X x0 (x + t • v) := by
  unfold linePoly DeltaF lminor
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Mx, mat, Matrix.mul_apply, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_left_comm,
    Polynomial.eval_finsetSum]

theorem dense_delta (hx0 : IsOrth X x0) (x : Frame X.Ψ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ ball x ε, DeltaF X x0 y ≠ 0 := by
  classical
  set w : Frame X.Ψ r := x0 - x
  set P := linePoly (x0 := x0) x w
  have hP1 : P.eval 1 = 1 := by
    rw [linePoly_eval, one_smul, add_sub_cancel, orthogonalFrame_delta_eq_one hx0]
  have hP0 : P ≠ 0 := by
    rintro h
    rw [h, Polynomial.eval_zero] at hP1
    exact zero_ne_one hP1
  set δ : ℝ := ε / (‖w‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hinf : ((fun s : ℝ => (s : ℂ)) '' Set.Ioo 0 δ).Infinite :=
    (Set.Ioo_infinite hδ).image (fun a _ b _ h => Complex.ofReal_injective h)
  obtain ⟨c, hc, hcP⟩ := (hinf.diff (Polynomial.finite_setOf_isRoot hP0)).nonempty
  obtain ⟨s, hs, rfl⟩ := hc
  refine ⟨x + (s : ℂ) • w, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs.1]
    calc s * ‖w‖ ≤ δ * ‖w‖ := by gcongr; exact hs.2.le
      _ < δ * (‖w‖ + 1) := by gcongr; linarith
      _ = ε := by
        have : (‖w‖ + 1) ≠ 0 := by positivity
        simp only [δ]
        field_simp
  · rw [← linePoly_eval]
    exact hcP

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lu_holds : LUStatement (E := E) := by
  intro r X x0 hx0
  refine ⟨DeltaF X x0, zF X x0, bF X x0, Delta_diff (X := X) (x0 := x0),
    fun x _ ε hε => dense_delta (X := X) (x0 := x0) hx0 x ε hε,
    zF_diffOn (X := X) (x0 := x0), bF_diffOn (X := X) (x0 := x0),
    fun x hx hΔ => ⟨zF_mem (X := X) (x0 := x0) hx0 hx hΔ, bF_mem (X := X) (x0 := x0) hx hΔ,
      split_eq (X := X) (x0 := x0) hx0 x⟩,
    fun z _ b hb => uniq_all (X := X) (x0 := x0) hx0 hb⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

local instance instMSMat {m n : Type*} : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance instBorelMat {m n : Type*} [Fintype m] [Fintype n] : BorelSpace (Matrix m n ℂ) :=
  inferInstanceAs (BorelSpace (m → n → ℂ))

theorem meas_inv {n : Type*} [Fintype n] [DecidableEq n] : Measurable fun A : Matrix n n ℂ => A⁻¹ := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (continuous_id.matrix_det.measurable.inv).mul
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable

theorem meas_Yb {p q : ℕ} : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => Yb M := by
  have hB : Measurable fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ => M.toBlocks₂₂ :=
    (show Continuous fun M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ =>
        (M.toBlocks₂₂ : Matrix (Fin q) (Fin q) ℂ) from
      continuous_pi fun i => continuous_pi fun j =>
        continuous_id.matrix_elem (Sum.inr i) (Sum.inr j)).measurable
  have hBi := (meas_inv (n := Fin q)).comp hB
  unfold Yb
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (continuous_id.matrix_elem (Sum.inl i) (Sum.inr k)).measurable.mul
    ((continuous_id.matrix_elem k j).measurable.comp hBi)

theorem meas_dpow {p q : ℕ} (s : ℝ) : Measurable fun Z : Matrix (Fin p) (Fin q) ℂ => dpow Z s := by
  unfold dpow
  exact (Complex.continuous_re.comp ((continuous_const.sub
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)).matrix_det)).measurable.pow_const s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cont_mat (X : Data E r) (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ

theorem cont_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) : Continuous fun x => Mx X x0 x τ := by
  unfold Mx tl
  exact (continuous_const.matrix_mul (cont_mat X τ)).matrix_submatrix _ _

theorem meas_kap (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kap X x0 bb) := by
  unfold kap
  exact Finset.measurable_prod _ fun τ _ =>
    (meas_dpow bb).comp (meas_Yb.comp (cont_Mx X x0 τ).measurable)

theorem cont_lact (X : Data E r) (γ : GL (Fin r) E) : Continuous (lact (Ψ := X.Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : Frame X.Ψ r =>
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  exact continuous_const.matrix_mul (cont_mat X τ)

theorem meas_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a, ⋂ c, {b : Frame X.Ψ r | c < a → b τ a c = 0}) := by
    ext b
    simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
  · exact (isOpen_ne_fun (cont_mat X τ).matrix_det continuous_const).measurableSet
  · by_cases hca : c < a
    · simp only [hca, true_implies]
      exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
    · simp [hca]

def Sset (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun pr : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 pr.1) pr.2) '' (FF ×ˢ Bor X.Ψ r)

theorem meas_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) : MeasurableSet (Sset X x0 FF) := by
  have : PolishSpace (V (nd X) × Frame X.Ψ r) := {}
  refine MeasurableSet.image_of_continuousOn_injOn (hFF.prod (meas_Bor X)) ?_ ?_
  · refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    exact ((cont_mat X τ).comp ((cont_cpt X x0).comp continuous_fst)).matrix_mul
      ((cont_mat X τ).comp continuous_snd)
  · rintro ⟨z, b⟩ ⟨_, hb⟩ ⟨z', b'⟩ ⟨_, hb'⟩ h
    obtain ⟨e1, e2⟩ := cpt_inj X ho hb hb' h
    exact Prod.ext e1 e2

private lemma rmul_rmul_eq_rmul_rmul (X : Data E r) (x b c : Frame X.Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat b τ) (mat c τ)

private lemma bor_rmul_mem (X : Data E r) {b c : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (hc : c ∈ Bor X.Ψ r) : rmul b c ∈ Bor X.Ψ r := by
  intro τ
  have hm : mat (rmul b c) τ = mat b τ * mat c τ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
    have h2 : (mat c τ).BlockTriangular id := fun i j h => (hc τ).2 i j h
    exact (h1.mul h2) hda

private lemma inv_mat_mem_bor (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
  intro τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  have hm : mat (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ = (mat b τ)⁻¹ := rfl
  refine ⟨?_, fun a d hda => ?_⟩
  · rw [hm]
    exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
  letI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ hu
  have h1 : (mat b τ).BlockTriangular id := fun i j h => (hb τ).2 i j h
  exact (Matrix.blockTriangular_inv_of_blockTriangular h1) hda

private lemma rmul_rmul_inv_mat (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (y : Frame X.Ψ r) :
    rmul (rmul y b) (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = y := by
  funext τ
  have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat y τ * mat b τ * (mat b τ)⁻¹ = y τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rfl

theorem rmul_mem_S (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ Sset X x0 FF ↔ y ∈ Sset X x0 FF := by
  constructor
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c (fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)⟩, ⟨hz, bor_rmul_mem X hc (inv_mat_mem_bor X hb)⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans
      ((congrArg (fun w => rmul w _) h).trans (rmul_rmul_inv_mat X hb y))
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, h⟩
    refine ⟨⟨z, rmul c b⟩, ⟨hz, bor_rmul_mem X hc hb⟩, ?_⟩
    simp only at h ⊢
    exact (rmul_rmul_eq_rmul_rmul X _ _ _).symm.trans (congrArg (fun w => rmul w b) h)

theorem cpt_mem_S (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))} (z : V (nd X)) :
    cpt X x0 z ∈ Sset X x0 FF ↔ z ∈ FF := by
  constructor
  · rintro ⟨⟨z', b'⟩, ⟨hz', hb'⟩, h⟩
    simp only at h
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rwa [← (cpt_inj X ho hb' (ExtFPf.oneF_mem X) h).1]
  · intro hz
    exact ⟨⟨z, ExtFPf.oneF X⟩, ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

theorem lact_rmul' (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (rmul x b) τ = mat (lact γ x) τ * mat b τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem wdb_contDiffOn (hU : IsOpen U) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g U) (k : Fin n) :
    ContDiffOn ℝ ∞ (wdb n k g) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (bas n k)) U := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (Complex.I • bas n k)) U :=
    hd.clm_apply contDiffOn_const
  show ContDiffOn ℝ ∞
    (fun y => (fderiv ℝ g y (bas n k) + Complex.I * fderiv ℝ g y (Complex.I • bas n k)) / 2) U
  exact (h1.add (contDiffOn_const.mul h2)).div_const 2

theorem wd_continuousOn (hU : IsOpen U) {h : V n → ℂ} (hh : ContDiffOn ℝ ∞ h U) (j : Fin n) :
    ContinuousOn (wd n j h) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hh).2
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y (bas n j)) U := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y (Complex.I • bas n j)) U :=
    hd.clm_apply contDiffOn_const
  show ContinuousOn
    (fun y => (fderiv ℝ h y (bas n j) - Complex.I * fderiv ℝ h y (Complex.I • bas n j)) / 2) U
  exact ((h1.sub (contDiffOn_const.mul h2)).div_const 2).continuousOn

theorem leviV_scale (g : V n → ℂ) (z : V n) (t : ℝ) (ξ : Fin n → ℂ) :
    (leviV n g z (fun j => (t : ℂ) * ξ j)).re = t ^ 2 * (leviV n g z ξ).re := by
  have h : leviV n g z (fun j => (t : ℂ) * ξ j) = ((t ^ 2 : ℝ) : ℂ) * leviV n g z ξ := by
    simp only [leviV, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]

theorem levi_unif (hU : IsOpen U) {g : V n → ℝ} (hg : ContDiffOn ℝ ∞ g U) {K : Set (V n)}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ z ∈ K, ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => (g w : ℂ)) z ξ).re) :
    ∃ c > 0, ∀ z ∈ K, ∀ ξ : Fin n → ℂ,
      c * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (g w : ℂ)) z ξ).re := by
  have hG : ContDiffOn ℝ ∞ (fun w => (g w : ℂ)) U :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hg).congr (fun x _ => by simp)
  have hcont : ContinuousOn
      (fun p : V n × (Fin n → ℂ) => (leviV n (fun w => (g w : ℂ)) p.1 p.2).re)
      (K ×ˢ sphere (0 : Fin n → ℂ) 1) := by
    refine Complex.continuous_re.comp_continuousOn
      (f := fun p : V n × (Fin n → ℂ) => leviV n (fun w => (g w : ℂ)) p.1 p.2) ?_
    show ContinuousOn (fun p : V n × (Fin n → ℂ) => ∑ j, ∑ k,
      wd n j (wdb n k (fun w => (g w : ℂ))) p.1 * p.2 j * (starRingEnd ℂ) (p.2 k)) _
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    have hw : ContinuousOn
        (fun p : V n × (Fin n → ℂ) => wd n j (wdb n k (fun w => (g w : ℂ))) p.1)
        (K ×ˢ sphere (0 : Fin n → ℂ) 1) :=
      (wd_continuousOn hU (wdb_contDiffOn hU hG k) j).comp continuousOn_fst
        (fun p hp => hKU hp.1)
    refine (hw.mul ?_).mul ?_
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
    · exact (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_snd)).continuousOn
  by_cases hne : (K ×ˢ sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ :=
      (hK.prod (isCompact_sphere (0 : Fin n → ℂ) 1)).exists_isMinOn hne hcont
    have hp0ne : p0.2 ≠ 0 := by
      intro h
      have h1 := hp0.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at h1
      exact zero_ne_one h1
    have hc0 : 0 < (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re := hpos p0.1 hp0.1 p0.2 hp0ne
    refine ⟨(leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1),
      div_pos hc0 (by positivity), ?_⟩
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hη : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      have hm : (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re
          ≤ (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re :=
        isMinOn_iff.1 hmin (z, ‖ξ‖⁻¹ • ξ) (Set.mk_mem_prod hz hη)
      have hξη : (fun j => ((‖ξ‖ : ℝ) : ℂ) * (‖ξ‖⁻¹ • ξ) j) = ξ := by
        funext j
        rw [Pi.smul_apply, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_mul]
      have key : (leviV n (fun w => (g w : ℂ)) z ξ).re
          = ‖ξ‖ ^ 2 * (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re :=
        (congrArg (fun v => (leviV n (fun w => (g w : ℂ)) z v).re) hξη.symm).trans
          (leviV_scale (fun w => (g w : ℂ)) z ‖ξ‖ (‖ξ‖⁻¹ • ξ))
      have hsum : ∑ j, ‖ξ j‖ ^ 2 ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by
        calc ∑ j, ‖ξ j‖ ^ 2 ≤ ∑ _j : Fin n, ‖ξ‖ ^ 2 :=
              Finset.sum_le_sum fun j _ => by gcongr; exact norm_le_pi_norm ξ j
          _ = (n : ℝ) * ‖ξ‖ ^ 2 := by simp
          _ ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
      rw [key]
      calc (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1) * ∑ j, ‖ξ j‖ ^ 2
          ≤ (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * ‖ξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (div_pos hc0 (by positivity)).le
        _ = (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re * ‖ξ‖ ^ 2 := by
            rw [← mul_assoc, div_mul_cancel₀ _ (by positivity : ((n : ℝ) + 1) ≠ 0)]
        _ ≤ ‖ξ‖ ^ 2 * (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re := by
            nlinarith [hm, sq_nonneg ‖ξ‖]
  · refine ⟨1, one_pos, ?_⟩
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · exfalso
      apply hne
      refine ⟨(z, ‖ξ‖⁻¹ • ξ), hz, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.2 hξ).ne']

private theorem eq_zero_on_ball_of_eventuallyEq_zero {F : V n → ℂ} {w : V n} {ρ : ℝ}
    (hF : DifferentiableOn ℂ F (ball w ρ)) (h0 : F =ᶠ[𝓝 w] 0) :
    ∀ y ∈ ball w ρ, F y = 0 := by
  intro y hy
  by_cases hyw : y = w
  · subst hyw
    exact h0.self_of_nhds
  have hρ : 0 < ρ := pos_of_mem_ball hy
  have hd : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hyw)
  have hyd : ‖y - w‖ < ρ := by rw [← dist_eq_norm]; exact hy
  have hmaps : Set.MapsTo (fun t : ℂ => w + t • (y - w)) (ball (0 : ℂ) (ρ / ‖y - w‖)) (ball w ρ) := by
    intro t ht
    rw [mem_ball, dist_zero_right, lt_div_iff₀ hd] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hLd : Differentiable ℂ (fun t : ℂ => w + t • (y - w)) := by fun_prop
  have hg : DifferentiableOn ℂ (fun t : ℂ => F (w + t • (y - w))) (ball (0 : ℂ) (ρ / ‖y - w‖)) :=
    hF.comp hLd.differentiableOn hmaps
  have hT : Filter.Tendsto (fun t : ℂ => w + t • (y - w)) (𝓝 0) (𝓝 w) := by
    have h := hLd.continuous.tendsto 0
    rwa [zero_smul, add_zero] at h
  have hg0 : (fun t : ℂ => F (w + t • (y - w))) =ᶠ[𝓝 0] 0 := h0.comp_tendsto hT
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (ρ / ‖y - w‖) := by
    rw [mem_ball, dist_zero_right, norm_one, lt_div_iff₀ hd, one_mul]
    exact hyd
  have h2 := (hg.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) _).isPreconnected (mem_ball_self (div_pos hρ hd)) hg0 h1
  simpa using h2

theorem ident_preconn (hU : IsOpen U) (hc : IsPreconnected U) {F : V n → ℂ}
    (hF : DifferentiableOn ℂ F U) {a : V n} (ha : a ∈ U) (h0 : F =ᶠ[𝓝 a] 0) : Set.EqOn F 0 U := by
  have hS : IsOpen {z : V n | F =ᶠ[𝓝 z] 0} := isOpen_setOf_eventually_nhds
  have hcl : closure {z : V n | F =ᶠ[𝓝 z] 0} ∩ U ⊆ {z : V n | F =ᶠ[𝓝 z] 0} := by
    rintro z ⟨hzc, hzU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨w, hwS, hzw⟩ := Metric.mem_closure_iff.1 hzc (r / 2) (half_pos hr)
    have hsub : ball w (r / 2) ⊆ U := by
      intro y hy
      apply hrU
      rw [mem_ball] at hy ⊢
      calc dist y z ≤ dist y w + dist w z := dist_triangle _ _ _
        _ < r / 2 + r / 2 := by rw [dist_comm w z]; exact add_lt_add hy hzw
        _ = r := add_halves r
    have hzb : z ∈ ball w (r / 2) := by rw [mem_ball]; exact hzw
    have hw0 : F =ᶠ[𝓝 w] 0 := hwS
    show F =ᶠ[𝓝 z] 0
    exact Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb)
      (fun y hy => eq_zero_on_ball_of_eventuallyEq_zero (hF.mono hsub) hw0 y hy)
  have hUS := hc.subset_of_closure_inter_subset hS ⟨a, ha, h0⟩ hcl
  intro z hz
  have h' : F =ᶠ[𝓝 z] 0 := hUS hz
  exact h'.self_of_nhds

theorem hgn_of (hU : IsOpen U) (hc : IsPreconnected U) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    {a : V n} (ha : a ∈ U) (hne : ¬ F =ᶠ[𝓝 a] 0) :
    ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, F y ≠ 0 := by
  intro W hW hWU hWne
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hWne
  have hy0 : F =ᶠ[𝓝 y] 0 := Filter.eventually_of_mem (hW.mem_nhds hy) (fun x hx => hcon x hx)
  have hall := ident_preconn hU hc hF (hWU hy) hy0
  exact hne (Filter.eventually_of_mem (hU.mem_nhds ha) (fun x hx => hall hx))

theorem ker_bot_of_det {f' : V n →L[ℂ] V n} (hdet : f'.det ≠ 0) :
    LinearMap.ker (f' : V n →ₗ[ℂ] V n) = ⊥ := by
  exact (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))

theorem iso_zero {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0) (hdet : f'.det ≠ 0)
    (h0 : f 0 = 0) : ∃ δ > 0, ∀ y ∈ closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  obtain ⟨K, -, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (ker_bot_of_det hdet)
  have hev : ∀ᶠ z in 𝓝[≠] (0 : V n), f z ≠ 0 := hf.eventually_ne (c := 0) ⟨K, hK⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, half_pos hε, fun y hy hy0 => ?_⟩
  by_contra hne
  have hyd : dist y 0 < ε := lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hε)
  exact hball hyd hne hy0

theorem coord_ne_of_det {f : V n → V n} (hn : 1 ≤ n) (hdet : (fderiv ℂ f 0).det ≠ 0) :
    ∃ k : Fin n, ¬ (fun z => f z k) =ᶠ[𝓝 0] 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ᶠ z in 𝓝 (0 : V n), ∀ k : Fin n, f z k = 0 := by
    rw [Filter.eventually_all]
    intro k
    exact hcon k
  have hf0 : f =ᶠ[𝓝 0] 0 := by
    filter_upwards [hall] with z hz
    ext k
    simpa using hz k
  have hd : fderiv ℂ f 0 = 0 := by
    rw [hf0.fderiv_eq]
    simp
  apply hdet
  rw [hd]
  have hfr : Module.finrank ℂ (V n) = n := finrank_euclideanSpace_fin
  show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
  rw [ContinuousLinearMap.coe_zero, LinearMap.det_zero, hfr]
  exact zero_pow (by omega)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Topology Filter ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.FD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace ExG

theorem two_le_inf : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
    | exact WithTop.coe_le_coe.mpr le_top
    | exact (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    | decide
    | simp
    | norm_num

variable {r : ℕ} (X : Data E r)

private lemma isOpen_omF (x0 : Frame X.Ψ r) : IsOpen (OmF X x0) := by
  first
  | exact ExF.isOpen_OmF X x0
  | exact isOpen_OmF X x0
  | exact ExF.isOpen_Om X x0
  | exact (X.isOpen_dom).preimage (continuous_cpt X x0)
  | exact X.isOpen_dom.preimage (by unfold cpt; fun_prop)
  | exact X.dom_open.preimage (by unfold cpt; fun_prop)
  | exact X.hdom.preimage (by unfold cpt; fun_prop)

theorem isOpen_Om (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := by
  have hO := isOpen_omF X x0
  exact hg.continuousOn.isOpen_inter_preimage hO isOpen_ne

theorem g_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℂ ∞ g1 z := by
  exact (contDiffOn_of_differentiableOn (nd X) g1 (OmF X x0) (isOpen_omF X x0) hg).contDiffAt
    ((isOpen_omF X x0).mem_nhds hz)

theorem inv_cd (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => (‖g1 y‖ ^ 2)⁻¹) z := by
  have h1 : ContDiffAt ℝ ∞ g1 z := (g_cd X x0 g1 hg hz).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun y => ‖g1 y‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt.comp z h1
  exact h2.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

theorem levi_inv_nonneg (x0 : Frame X.Ψ r) (g1 : V (nd X) → ℂ) (hg : DifferentiableOn ℂ g1 (OmF X x0))
    {z : V (nd X)} (hz : z ∈ OmF X x0) (hne : g1 z ≠ 0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) z ξ).re := by
  have hfun : (fun y => (((‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) = fun y => ((Complex.normSq ((g1 y)⁻¹) : ℝ) : ℂ) := by
    funext y
    rw [Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hcd : ContDiffAt ℂ 2 (fun y => (g1 y)⁻¹) z := ((g_cd X x0 g1 hg hz).of_le two_le_inf).inv hne
  rw [hfun, leviV_normSq_comp hcd ξ, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem isCompact_sub (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (g1 : V (nd X) → ℂ)
    (hg : DifferentiableOn ℂ g1 (OmF X x0)) (a : ℝ) :
    IsCompact {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} := by
  have hK := ExF.isCompact_subF X x0 ho a
  have hcont : ContinuousOn (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} :=
    ((hg.continuousOn.norm.pow 2).mul (continuousOn_const.sub (fun z hz =>
      (ExF.eF_contDiffAt X x0 ho hz).continuousAt.continuousWithinAt))).mono (fun z hz => hz.1)
  have hcl := hcont.preimage_isClosed_of_isClosed hK.isClosed (isClosed_Ici (a := (1 : ℝ)))
  have hset : {z : V (nd X) | (z ∈ OmF X x0 ∧ g1 z ≠ 0) ∧ eF X x0 z + (‖g1 z‖ ^ 2)⁻¹ ≤ a} =
      {z | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} ∩ (fun z => ‖g1 z‖ ^ 2 * (a - eF X x0 z)) ⁻¹' Set.Ici 1 := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨⟨hzO, hz0⟩, hle⟩
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      have hinv : 0 ≤ (‖g1 z‖ ^ 2)⁻¹ := inv_nonneg.mpr hpos.le
      refine ⟨⟨hzO, by linarith⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by linarith
      calc (1 : ℝ) = ‖g1 z‖ ^ 2 * (‖g1 z‖ ^ 2)⁻¹ := (mul_inv_cancel₀ hpos.ne').symm
        _ ≤ ‖g1 z‖ ^ 2 * (a - eF X x0 z) := mul_le_mul_of_nonneg_left hle' hpos.le
    · rintro ⟨⟨hzO, _⟩, h1⟩
      have hz0 : g1 z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at h1
        norm_num at h1
      have hpos : 0 < ‖g1 z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz0) 2
      refine ⟨⟨hzO, hz0⟩, ?_⟩
      have hle' : (‖g1 z‖ ^ 2)⁻¹ ≤ a - eF X x0 z := by
        calc (‖g1 z‖ ^ 2)⁻¹ = (‖g1 z‖ ^ 2)⁻¹ * 1 := (mul_one _).symm
          _ ≤ (‖g1 z‖ ^ 2)⁻¹ * (‖g1 z‖ ^ 2 * (a - eF X x0 z)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
          _ = a - eF X x0 z := by field_simp
      linarith
  rw [hset]
  exact hK.of_isClosed_subset hcl Set.inter_subset_left

end ExG

private theorem leviV_ofReal_add_of_contDiffAt_two {n : ℕ} {F G : V n → ℝ} {y : V n} (hF : ContDiffAt ℝ 2 F y)
    (hG : ContDiffAt ℝ 2 G y) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((F v + G v : ℝ) : ℂ)) y ξ =
      leviV n (fun v => (F v : ℂ)) y ξ + leviV n (fun v => (G v : ℂ)) y ξ := by
  have h := leviV_ofReal_sum (u := ![F, G]) (x := y) (fun i => by fin_cases i <;> simpa) ξ
  simpa [Fin.sum_univ_two] using h

theorem exhaustG_holds : ExhaustGStatement (E := E) := by
  intro r X x0 ho g1 hg
  have hU : IsOpen {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := ExG.isOpen_Om X x0 g1 hg
  have hLH : IsLocalHomeomorph (Subtype.val : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} → V (nd X)) :=
    hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : ∀ z ∈ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      ContDiffAt ℝ ∞ (fun z => eF X x0 z + (‖g1 z‖ ^ 2)⁻¹) z := fun z hz =>
    (ExF.eF_contDiffAt X x0 ho hz.1).add (ExG.inv_cd X x0 g1 hg hz.1 hz.2)
  refine ⟨{ z := Subtype.val
            isLocalHomeomorph := hLH
            e := fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹
            smooth_e := ?_
            levi_e := ?_
            isCompact_le := ?_ }, rfl, rfl⟩
  · intro ch hch
    have hts : ∀ y ∈ ch.target, ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := fun y hy => by
      rw [hch (ch.map_target hy)]
      exact ch.right_inv hy
    have hsub : ch.target ⊆ {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} := fun y hy => by
      rw [← hts y hy]
      exact (ch.symm y).2
    have hcd : ContDiffOn ℝ ∞ (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) ch.target :=
      fun y hy => (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hf y (hsub hy))).contDiffWithinAt
    refine hcd.congr (fun y hy => ?_)
    simp only [Function.comp_apply, hts y hy]
  · intro x ξ
    obtain ⟨ch, hx, hch⟩ := hLH x
    have hchart : IsChart (nd X) Subtype.val ch := fun y _ => congrFun hch y
    rw [levi_eq_leviV (nd X) Subtype.val ch hchart _ x hx ξ]
    have htg : ch.target ∈ 𝓝 (x : V (nd X)) := by
      have h0 := ch.open_target.mem_nhds (ch.map_source hx)
      rwa [← congrFun hch x] at h0
    have hgerm : (fun y => (((fun y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹)
        (ch.symm y) : ℝ) : ℂ)) =ᶠ[𝓝 (x : V (nd X))]
        (fun y => ((eF X x0 y + (‖g1 y‖ ^ 2)⁻¹ : ℝ) : ℂ)) := by
      filter_upwards [htg] with y hy
      have hy' : ((ch.symm y : {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}) : V (nd X)) = y := by
        rw [congrFun hch (ch.symm y)]
        exact ch.right_inv hy
      simp only [hy']
    rw [leviV_congr hgerm ξ]
    have hxO : (x : V (nd X)) ∈ OmF X x0 := x.2.1
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ExG.two_le_inf
    have hE : ContDiffAt ℝ 2 (eF X x0) x := (ExF.eF_contDiffAt X x0 ho hxO).of_le h2
    have hI : ContDiffAt ℝ 2 (fun y => (‖g1 y‖ ^ 2)⁻¹) x :=
      (ExG.inv_cd X x0 g1 hg hxO x.2.2).of_le h2
    have hR : ContDiffAt ℝ 2 (rhF X x0) x := (ExF.rhF_contDiffAt X x0 ho hxO).of_le h2
    have hT : ContDiffAt ℝ 2 (fun z : V (nd X) => Real.log (1 + ‖z‖ ^ 2)) x := ExF.T_cd.contDiffAt.of_le h2
    rw [leviV_ofReal_add_of_contDiffAt_two hE hI ξ]
    have hEsplit : leviV (nd X) (fun v => (eF X x0 v : ℂ)) x ξ =
        leviV (nd X) (fun v => (rhF X x0 v : ℂ)) x ξ +
          leviV (nd X) (fun v => (Real.log (1 + ‖v‖ ^ 2) : ℂ)) x ξ :=
      leviV_ofReal_add_of_contDiffAt_two hR hT ξ
    rw [hEsplit, Complex.add_re, Complex.add_re]
    have h1 := ExF.levi_rhF_nonneg X x0 ho hxO ξ
    have h3 := ExF.leviT_nonneg (x : V (nd X)) ξ
    have h4 := ExG.levi_inv_nonneg X x0 g1 hg hxO x.2.2 ξ
    linarith
  · intro a
    rw [Subtype.isCompact_iff]
    convert ExG.isCompact_sub X x0 ho g1 hg a using 1
    ext z
    constructor
    · rintro ⟨⟨w, hw⟩, hle, rfl⟩
      exact ⟨hw, hle⟩
    · rintro ⟨hw, hle⟩
      exact ⟨⟨z, hw⟩, hle, rfl⟩

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lactDom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X hγ x).2 hx

theorem rmulDom (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    rmul x b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom X hx hb

theorem isOpenDom (X : Data E r) : IsOpen X.dom := FourierCoefficientDomain.isOpen_dom X

theorem lact_mul' {Ψ : Finset (E →+* ℂ)} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  simp only [lact, mat, Units.val_mul, Matrix.map_mul]
  rw [Matrix.mul_assoc]
  rfl

theorem lact_rmul' {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

theorem norm_chi (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1

theorem chi_ne (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    X.χ la γ ≠ 0 := by
  intro h
  have := norm_chi X la hγ
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem poin_mul (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ) (hg : X.IsSec la' g)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  dsimp only
  rw [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  have h1 := chi_ne X la' γ.2
  have h2 := chi_ne X la γ.2
  field_simp

theorem poin_rmul (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    poin X la P (rmul x b) = bchar la b * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  rw [lact_rmul', hP _ (lactDom X γ.2 hx) b hb]
  ring

theorem poin_lact (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {γ' : GL (Fin r) E}
    (hγ' : γ' ∈ X.Γ) (x : Frame X.Ψ r) :
    poin X la P (lact γ' x) = X.χ la γ' * poin X la P x := by
  unfold poin
  set g : X.Γ := ⟨γ', hγ'⟩
  have key : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 (lact γ' x)) =
      X.χ la γ' * ((X.χ la (γ * g).1)⁻¹ * P (lact (γ * g).1 x)) := by
    intro γ
    have hm : ((γ * g : X.Γ) : GL (Fin r) E) = γ.1 * γ' := rfl
    rw [hm, lact_mul', X.χ_mul la γ.1 γ.2 γ' hγ']
    have h1 := chi_ne X la hγ'
    have h2 := chi_ne X la γ.2
    field_simp
  rw [tsum_congr key, tsum_mul_left]
  congr 1
  exact (Equiv.mulRight g).tsum_eq (fun δ : X.Γ => (X.χ la δ.1)⁻¹ * P (lact δ.1 x))

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open Metric

theorem fderiv_bound_ball {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {g : Y → ℂ} {y : Y}
    {R M : ℝ} (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball y (2 * R)))
    (hM : ∀ v ∈ ball y (2 * R), ‖g v‖ ≤ M) : ‖fderiv ℂ g y‖ ≤ M / R := by
  first | exact Bl.general_b_fact_version.goal1 .. | (apply Bl.general_b_fact_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_version.goal1 <;> assumption)

theorem differentiableOn_tsum_loc {ι Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {U : Set Y}
    (hU : IsOpen U) (f : ι → Y → ℂ) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hb : ∀ y ∈ U, ∃ ε > 0, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ v ∈ ball y ε, ‖f i v‖ ≤ u i) :
    DifferentiableOn ℂ (fun y => ∑' i, f i y) U := by
  intro y0 hy0
  obtain ⟨ε, hε, u, hu, hub⟩ := hb y0 hy0
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU y0 hy0
  set m := min ε δ with hm
  have hm0 : 0 < m := lt_min hε hδ
  set R := m / 4 with hR
  have hR0 : 0 < R := by positivity
  have hsub : ∀ y ∈ ball y0 R, ball y (2 * R) ⊆ ball y0 m := by
    intro y hy v hv
    rw [mem_ball] at *
    calc dist v y0 ≤ dist v y + dist y y0 := dist_triangle _ _ _
      _ < 2 * R + R := add_lt_add hv hy
      _ ≤ m := by rw [hR]; linarith
  have hε' : ball y0 m ⊆ ball y0 ε := ball_subset_ball (min_le_left _ _)
  have hδ' : ball y0 m ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hδU
  have hin : ∀ y ∈ ball y0 R, y ∈ U := fun y hy => hδ' (hsub y hy (mem_ball_self (by linarith)))
  have hder : ∀ i, ∀ y ∈ ball y0 R, HasFDerivAt (f i) (fderiv ℂ (f i) y) y := fun i y hy =>
    ((hf i y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))).hasFDerivAt
  have hbd : ∀ i, ∀ y ∈ ball y0 R, ‖fderiv ℂ (f i) y‖ ≤ u i / R := fun i y hy =>
    fderiv_bound_ball hR0 ((hf i).mono ((hsub y hy).trans hδ')) (fun v hv => hub i v (hε' (hsub y hy hv)))
  have hs := hasFDerivAt_tsum_of_isPreconnected (hu.div_const R) isOpen_ball
    (convex_ball y0 R).isPreconnected hder hbd (mem_ball_self hR0)
    (Summable.of_norm_bounded hu fun i => hub i y0 (mem_ball_self hε)) (mem_ball_self hR0)
  exact hs.differentiableAt.differentiableWithinAt

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end
