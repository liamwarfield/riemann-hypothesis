module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivEqFderivPair
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem deriv_eq_fderiv_pair (U : ℂ × V → ℂ) (z0 : ℂ) (w : V) (hU : DifferentiableAt ℂ U (z0, w)) :
    deriv (fun z => U (z, w)) z0 = fderiv ℂ U (z0, w) (1, 0) := by
  have hl : HasDerivAt (fun z : ℂ => (z, w)) ((1 : ℂ), (0 : V)) z0 := (hasDerivAt_id z0).prodMk (hasDerivAt_const z0 w)
  exact (hU.hasFDerivAt.comp_hasDerivAt z0 hl).deriv

theorem iFD_slice (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (z : ℂ) (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v = iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hU' : ContDiffOn ℂ ∞ (fun p : ℂ × V => U ((z, 0) + p)) (Set.univ ×ˢ D) :=
    hU.comp (contDiff_const.add contDiff_id).contDiffOn (fun p hp => ⟨trivial, by simpa using hp.2⟩)
  have hpre : (ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D) = D := by
    ext w
    simp
  have hfun : (fun w => U (z, w)) = (fun p : ℂ × V => U ((z, 0) + p)) ∘ (ContinuousLinearMap.inr ℂ ℂ V) := by
    funext w
    simp
  have hgw : ContinuousLinearMap.inr ℂ ℂ V w0 ∈ (Set.univ ×ˢ D : Set (ℂ × V)) := ⟨trivial, hw0⟩
  have hD' : IsOpen ((ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D)) := by rw [hpre]; exact hD
  rw [hfun, ← iteratedFDerivWithin_of_isOpen k hD' (by rw [hpre]; exact hw0),
    (ContinuousLinearMap.inr ℂ ℂ V).iteratedFDerivWithin_comp_right hU' hs.uniqueDiffOn hD'.uniqueDiffOn hgw
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen k hs hgw, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]
  simp

private theorem natCast_le_infty_withTop (a : ℕ) : ((a : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private theorem inv_mul_mul_mul_eq_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (S : Set E)
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) (e : E) (k : ℕ) :
    ∀ y ∈ S, iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) y = fderiv ℂ (iteratedFDeriv ℂ k f) y e := by
  induction k with
  | zero =>
    intro y hy
    have hd : DifferentiableAt ℂ f y :=
      (hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp
  | succ k ih =>
    intro y hy
    have hev : iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) =ᶠ[nhds y]
        fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e :=
      Filter.eventually_of_mem (hS.mem_nhds hy) ih
    have hg : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
      (hf.contDiffAt (hS.mem_nhds hy)).iteratedFDeriv_right (by
        have h : ((2 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
        exact_mod_cast h)
    have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
      hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    have hdg : DifferentiableAt ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have happ : fderiv ℂ (fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e) y =
        (ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).comp (fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y) :=
      ((ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).hasFDerivAt.comp y
        hdg.hasFDerivAt).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, happ,
      iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp [hsym (m 0) e]

theorem iFD_deriv_comm (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => deriv (fun z => U (z, w)) 0) w0 v =
      deriv (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) 0 := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hdiffU : ∀ p ∈ (Set.univ ×ˢ D : Set (ℂ × V)), DifferentiableAt ℂ U p := fun p hp =>
    (hU.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  have hU1 : ContDiffOn ℂ ∞ (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) (Set.univ ×ˢ D) :=
    (hU.fderiv_of_isOpen hs (m := ∞) (by exact le_of_eq (by rfl))).clm_apply contDiffOn_const
  have hL : (fun w => deriv (fun z => U (z, w)) 0) =ᶠ[nhds w0] fun w => fderiv ℂ U (0, w) ((1 : ℂ), (0 : V)) :=
    Filter.eventually_of_mem (hD.mem_nhds hw0) fun w hw => deriv_eq_fderiv_pair U 0 w (hdiffU (0, w) ⟨trivial, hw⟩)
  rw [((Filter.EventuallyEq.iteratedFDeriv ℂ hL k).eq_of_nhds),
    iFD_slice (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) D hD hU1 0 w0 hw0 k v]
  have hR : (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) =
      fun z => iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) :=
    funext fun z => iFD_slice U D hD hU z w0 hw0 k v
  have hdI : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, w0) :=
    ((hU.contDiffAt (hs.mem_nhds ⟨trivial, hw0⟩)).iteratedFDeriv_right (m := 1) (by
      have h : ((1 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
      exact_mod_cast h)).differentiableAt one_ne_zero
  have hdΦ : DifferentiableAt ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp _ hdI
  rw [hR, deriv_eq_fderiv_pair _ 0 w0 hdΦ, inv_mul_mul_mul_eq_mul U _ hs hU _ k (0, w0) ⟨trivial, hw0⟩]
  have h2 : fderiv ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).comp
        (fderiv ℂ (iteratedFDeriv ℂ k U) (0, w0)) :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).hasFDerivAt.comp
      (0, w0) hdI.hasFDerivAt).fderiv
  rw [h2]
  simp

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AbsArgLtPi
noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem abs_arg_lt_pi {P : ℂ} (hP : P ∈ Complex.slitPlane) : |P.arg| < Real.pi := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg P, lt_of_le_of_ne (Complex.arg_le_pi P) (Complex.slitPlane_arg_ne_pi hP)⟩

theorem cpow_split {P a b : ℂ} (hP : P ∈ Complex.slitPlane) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : |a.arg| < (Real.pi - |P.arg|) / 2) (hb' : |b.arg| < (Real.pi - |P.arg|) / 2) (w : ℂ) :
    (P * a * b) ^ w = P ^ w * a ^ w * b ^ w := by
  have hP0 : P ≠ 0 := Complex.slitPlane_ne_zero hP
  have hPpi := abs_arg_lt_pi hP
  have hpos : 0 ≤ Real.pi - |P.arg| := by linarith
  have h1 : P.arg + a.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg)]
    · linarith [le_abs_self (P.arg + a.arg)]
  have hPa : P * a ≠ 0 := mul_ne_zero hP0 ha
  have harg : (P * a).arg = P.arg + a.arg := by
    have := congrArg Complex.im (Complex.log_mul hP0 ha h1)
    simpa [Complex.log_im] using this
  have h2 : (P * a).arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [harg]
    have := abs_add_le (P.arg + a.arg) b.arg
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg + b.arg)]
    · linarith [le_abs_self (P.arg + a.arg + b.arg)]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hPa hb), Complex.log_mul hPa hb h2, Complex.log_mul hP0 ha h1,
    Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

theorem detD_congr {ι : Type} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) :
    detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]

theorem ev_small {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : E → ℂ} (hc : ContinuousAt c 0) (h0 : c 0 = 1)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 ∧ |(c T).arg| < δ := by
  have hne : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 := hc.eventually_ne (by rw [h0]; exact one_ne_zero)
  have hcont : ContinuousAt (fun T => (c T).arg) 0 :=
    ContinuousAt.comp (f := c) (g := Complex.arg) (Complex.continuousAt_arg (by rw [h0]; exact Complex.one_mem_slitPlane)) hc
  have ht : Tendsto (fun T => (c T).arg) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto
    simpa [h0, Complex.arg_one] using this
  filter_upwards [hne, ht (Metric.ball_mem_nhds 0 hδ)] with T h1 h2
  refine ⟨h1, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using h2

private theorem mul_toBlocks₂₁' (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem mul_toBlocks₂₂ (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

private theorem u1_mul_mX_one_eq_add (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX 1 Q R 1) = u1 x + u2 x * R := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hxc21 : (x * Cm n).toBlocks₂₁ = u1 x := by
    rw [mul_toBlocks₂₁', Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, u1]
    simp [Matrix.mul_smul]
  have hxc22 : (x * Cm n).toBlocks₂₂ = u2 x := by
    rw [mul_toBlocks₂₂, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, u2]
    simp [Matrix.mul_smul]
  rw [mX, hinv, show x * (Cm n * fromBlocks 1 Q R 1 * Cmi n) = (x * Cm n * fromBlocks 1 Q R 1) * Cmi n by
    simp only [Matrix.mul_assoc], first_cayley_block_mul_inverse_cayley, mul_toBlocks₂₁', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁,
    Matrix.mul_one, hxc21, hxc22]

theorem fz_mX {m : ℕ} {e : ℤ} {z : ℂ} {j : ℕ} {x : M2 n} (hx : x ∈ DomZ n)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (h1 : (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0) (h2 : (1 + subOn (blkA j) (wM x) * T).det ≠ 0)
    (h1' : |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2)
    (h2' : |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) :
    fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z) := by
  obtain ⟨hD, hP⟩ := hx
  have hD' := hD
  obtain ⟨hdet, hu1, hu2, -⟩ := hD'
  obtain ⟨hQR, hRQ⟩ := embOn_mul_embOn_compl j T S
  have hdetM : (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1).det = x.det := by
    rw [Matrix.det_mul, det_mX_one _ _ hRQ, mul_one]
  have hub : (ub1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det := by
    rw [inverse_first_block_mul_unipotent_domain x hD _ _ hQR hRQ, Matrix.det_mul, det_one_add_mul_comm, det_one_add_mul_embOn]
  have hw : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu2)]
  have hu : (u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det := by
    rw [u1_mul_mX_one_eq_add, ← det_one_add_mul_embOn, ← Matrix.det_mul]
    congr 1
    rw [hw, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu1), Matrix.one_mul]
  unfold fz
  rw [hdetM, hu, hub,
    show (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det * ((1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det) =
      (u1 x).det * (ub1 x).det * (1 + subOn (blkA j) (wM x) * T).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det by ring,
    cpow_split hP h2 h1 h2' h1' (-z), mul_zpow, sub_eq_add_neg, Complex.cpow_add _ _ h1,
    show (-(m : ℂ)) = ((-(m : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  ring

private theorem detD_det_one_add_mul_rpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ) (t : ℂ) :
    (detD fun S : Matrix ι ι ℂ => (1 + W * S).det ^ t) =
      W.det * ∏ i ∈ Finset.range (Fintype.card ι), (t + (i : ℂ)) := by
  have hF : AnalyticAt ℂ (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) 0 := analyticAt_det_one_add_cpow t
  have h := CEq.equivar_thm ι (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) W hF
  beta_reduce at h
  rw [h]
  congr 1
  have hG : AnalyticAt ℂ (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) 0 :=
    analyticAt_det_one_add_cpow t
  have hr := CEq.reindex_thm ι (Fin (Fintype.card ι)) (Fintype.equivFin ι) _ hG
  beta_reduce at hr
  rw [← kappaC (Fintype.card ι) t, ← hr]
  congr 1
  funext S
  have hS : (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) S =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (1 + S) := by
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hS, Matrix.det_reindex_self]

theorem djZ : DjZ := by
  intro n m e j z x hj hx
  have hx' := hx
  obtain ⟨hD, hP⟩ := hx'
  have hδ : 0 < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := by
    have := abs_arg_lt_pi hP
    linarith
  have hcA : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA j) ℂ),
      (1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun T => (1 + subOn (blkA j) (wM x) * T).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hcB : ∀ᶠ S in 𝓝 (0 : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0 ∧
        |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun S => (1 + subOn (blkB j) (wM x)⁻¹ * S).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hinner : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      ((1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) →
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          ((subOn (blkB j) (wM x)⁻¹).det *
            ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ))) := by
    intro T hT
    rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z)) ?_,
      detD_const_mul, detD_det_one_add_mul_rpow_eq]
    filter_upwards [hcB] with S hS
    exact fz_mX hx T S hS.1 hT.1 hS.2 hT.2
  rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      (fz m e z x * ((subOn (blkB j) (wM x)⁻¹).det *
        ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ)))) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) ?_]
  · rw [detD_const_mul, detD_det_one_add_mul_rpow_eq, card_blkA hj, card_blkB hj, minorOn_eq, minorOn_eq]
    have e1 : ∏ i ∈ Finset.range j, (-z + (i : ℂ)) = ∏ i ∈ Finset.range j, ((i : ℂ) - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    have e2 : ∏ i ∈ Finset.range (n - j), ((-(m : ℂ)) - z + (i : ℂ)) =
        ∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [e1, e2]
    ring
  · filter_upwards [hcA] with T hT
    rw [hinner T hT]
    ring

end PositivityTheory.Rg.Sw.HSt
end
end

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fz_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (Set.univ ×ˢ DomZ n) :=
  ((fzHol n m 0).2.2).contDiffOn_of_completeSpace

theorem Fd_eq (m : ℕ) {y : M2 n} (hy : y ∈ DomZ n) :
    Fd m y = fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0) :=
  deriv_eq_fderiv_pair (fun p : ℂ × M2 n => fz m 0 p.1 p.2) 0 y
    (((fz_contDiffOn m).contDiffAt ((isOpen_univ.prod isOpen_domZ).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
      (by simp))

theorem Fd_contDiffOn (m : ℕ) : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := by
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod isOpen_domZ
  have h1 : ContDiffOn ℂ ∞ (fun p : ℂ × M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) p (1, 0))
      (Set.univ ×ˢ DomZ n) :=
    ((fz_contDiffOn m).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℂ ∞ (fun y : M2 n => fderiv ℂ (fun p : ℂ × M2 n => fz m 0 p.1 p.2) (0, y) (1, 0)) (DomZ n) :=
    h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨Set.mem_univ _, hy⟩)
  exact h2.congr fun y hy => Fd_eq m hy

theorem fz_slice_contDiffOn (m : ℕ) (z : ℂ) : ContDiffOn ℂ ∞ (fz (n := n) m 0 z) (DomZ n) := by
  have hl : ContDiff ℂ ∞ (fun y : M2 n => ((z : ℂ), y)) := contDiff_const.prodMk contDiff_id
  have h := (fz_contDiffOn (n := n) m).comp hl.contDiffOn (fun y hy => (⟨Set.mem_univ _, hy⟩ : ((z : ℂ), y) ∈ Set.univ ×ˢ DomZ n))
  exact h

theorem djFd : DjFd := by
  intro n m j x hj1 hj hx
  set U : ℂ × M2 n → ℂ := fun p => fz m 0 p.1 p.2 with hUdef
  have hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ DomZ n) := fz_contDiffOn m
  have hD : IsOpen (DomZ n) := isOpen_domZ
  have hO : IsOpen (Set.univ ×ˢ DomZ n : Set (ℂ × M2 n)) := isOpen_univ.prod hD
  have expand : ∀ F : M2 n → ℂ, ContDiffOn ℂ ∞ F (DomZ n) →
      detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) F x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1))) := by
    intro F hF
    have hrw : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        F (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
        (fun T => detD (fun S => F (x + LQ (blkA j) x T + LR (blkB j) x S))) := by
      funext T; congr 1; funext S; rw [mul_mX, LQ_apply, LR_apply]
    rw [hrw]
    exact detD_detD_comp F (DomZ n) hD hF x hx (LQ (blkA j) x) (LR (blkB j) x)
  have hcomm : ∀ (k : ℕ) (v : Fin k → M2 n), iteratedFDeriv ℂ k (Fd m) x v =
      deriv (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := fun k v =>
    iFD_deriv_comm U (DomZ n) hD hU x hx k v
  have hdiff : ∀ (k : ℕ) (v : Fin k → M2 n), DifferentiableAt ℂ (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) 0 := by
    intro k v
    have e : (fun z => iteratedFDeriv ℂ k (fz m 0 z) x v) =
        fun z => iteratedFDeriv ℂ k U (z, x) (fun i => ((0 : ℂ), v i)) :=
      funext fun z => iFD_slice U (DomZ n) hD hU z x hx k v
    rw [e]
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, x) :=
      (hU.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hx⟩)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k)
    have hl : DifferentiableAt ℂ (fun z : ℂ => (z, x)) 0 := differentiableAt_id.prodMk (differentiableAt_const x)
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × M2 n) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp
      (0 : ℂ) (hd.comp (0 : ℂ) hl)
  rw [expand (Fd m) (Fd_contDiffOn m)]
  simp_rw [hcomm]
  have hsum : deriv (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 =
      ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        deriv (fun z => iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) 0 := by
    rw [deriv_fun_sum (fun σ _ => DifferentiableAt.fun_sum (fun τ _ => (hdiff _ _).const_mul _))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [deriv_fun_sum (fun τ _ => (hdiff _ _).const_mul _)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [deriv_const_mul _ (hdiff _ _)]
  rw [← hsum]
  have hfz : (fun z => ∑ σ : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
        (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (blkA (n := n) j) + Fintype.card (blkB (n := n) j)) (fz m 0 z) x
          (Fin.append (fun i => LQ (blkA j) x (Matrix.single ((Fintype.equivFin (blkA (n := n) j)).symm i)
              (σ ((Fintype.equivFin (blkA (n := n) j)).symm i)) 1))
            (fun i => LR (blkB j) x (Matrix.single ((Fintype.equivFin (blkB (n := n) j)).symm i)
              (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) 1)))) =
      fun z => ((∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))) *
        (fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) := by
    funext z
    rw [← expand (fz m 0 z) (fz_slice_contDiffOn m z), djZ n m 0 j z x hj hx]
    ring
  rw [hfz]
  set A : ℂ → ℂ := fun z => (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z))
    with hAdef
  have hA : DifferentiableAt ℂ A 0 := by
    simp only [hAdef]
    exact (DifferentiableAt.fun_finsetProd fun i _ => (differentiableAt_const _).sub differentiableAt_id).mul
      (DifferentiableAt.fun_finsetProd fun i _ => ((differentiableAt_const _).sub differentiableAt_id))
  have hA0 : A 0 = 0 := by
    simp only [hAdef]
    rw [Finset.prod_eq_zero (i := 0) (by simp; omega) (by simp), zero_mul]
  have hg : DifferentiableAt ℂ (fun z => fz m 0 z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹) 0 := by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => ((u1 x).det * (ub1 x).det) ^ (-z)) 0 :=
      (differentiableAt_id.neg).const_cpow (Or.inl (Complex.slitPlane_ne_zero hx.2))
    simp only [fz]
    exact (((differentiableAt_const _).mul h1).mul_const _).mul_const _
  rw [deriv_fun_mul hA hg, hA0, zero_mul, add_zero]
  congr 1
  simp [fz, hF, f0]
