module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceImmersiveGeneral

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff

noncomputable section

theorem smoothTransition_eventually_const {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    ∃ c : ℝ, Real.smoothTransition =ᶠ[𝓝 x] fun _ => c := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · refine ⟨0, ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  · refine ⟨1, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)

theorem smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C ∧
      |deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  obtain ⟨-, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨-, h2⟩ := contDiff_infty_iff_deriv.1 h1
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max (max C1 C2) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have a := hC1 x hx
    have b := hC2 x hx
    rw [Real.norm_eq_abs] at a b
    exact ⟨a.trans ((le_max_left _ _).trans (le_max_left _ _)),
      b.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨c, hc⟩ := smoothTransition_eventually_const hx
    have hd := hc.deriv
    have e1 : deriv Real.smoothTransition x = 0 := by rw [hd.eq_of_nhds]; simp
    have e2 : deriv (deriv Real.smoothTransition) x = 0 := by rw [hd.deriv_eq]; simp
    rw [e1, e2, abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem logLogStep_arith {C c t p q f v w : ℝ} (hC0 : 0 ≤ C) (hc : 1 ≤ c) (ht : t ≠ 0) (hp : |p| ≤ C)
    (hq : |q| ≤ C) (hf : |f| ≤ 1) (hv : v = -(2 * (t⁻¹ / c))) (hw : w = -(2 * (-(t ^ 2)⁻¹ / c))) :
    |q * v * v + p * w| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) ∧
      |p * v * (p * v) + f * (q * v * v + p * w)| ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hD : 0 < c * t ^ 2 := by positivity
  have hvv : v * v ≤ 4 / (c * t ^ 2) := by
    have e : v * v = 4 / (c * t ^ 2) / c := by rw [hv]; field_simp; ring
    rw [e]; exact div_le_self (by positivity) hc
  have hvv0 : 0 ≤ v * v := mul_self_nonneg v
  have hw' : |w| = 2 / (c * t ^ 2) := by
    have e : w = 2 / (c * t ^ 2) := by rw [hw]; field_simp
    rw [e, abs_of_pos (by positivity)]
  have h1 : |q * v * v + p * w| ≤ 6 * C / (c * t ^ 2) := by
    calc |q * v * v + p * w| ≤ |q * v * v| + |p * w| := abs_add_le _ _
      _ = |q| * (v * v) + |p| * |w| := by rw [mul_assoc, abs_mul q, abs_of_nonneg hvv0, abs_mul p]
      _ ≤ C * (4 / (c * t ^ 2)) + C * (2 / (c * t ^ 2)) := by rw [hw']; gcongr
      _ = 6 * C / (c * t ^ 2) := by ring
  have h2 : p * v * (p * v) ≤ 4 * C ^ 2 / (c * t ^ 2) := by
    calc p * v * (p * v) = |p| ^ 2 * (v * v) := by rw [sq_abs]; ring
      _ ≤ C ^ 2 * (4 / (c * t ^ 2)) := by gcongr
      _ = 4 * C ^ 2 / (c * t ^ 2) := by ring
  have hK : 6 * C / (c * t ^ 2) ≤ (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by
    gcongr; nlinarith
  refine ⟨h1.trans hK, ?_⟩
  calc |p * v * (p * v) + f * (q * v * v + p * w)|
      ≤ |p * v * (p * v)| + |f * (q * v * v + p * w)| := abs_add_le _ _
    _ ≤ 4 * C ^ 2 / (c * t ^ 2) + 1 * (6 * C / (c * t ^ 2)) := by
      rw [abs_of_nonneg (mul_self_nonneg (p * v)), abs_mul]; gcongr
    _ = (6 * C + 4 * C ^ 2) / (c * t ^ 2) := by ring

theorem logLogStep_deriv2_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ t : ℝ, t < 0 →
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c)) t ∧
      ContDiffAt ℝ 2 (fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c)) t| ≤ K / (c * t ^ 2) ∧
      |deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t| ≤ K / (c * t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := smoothTransition_deriv_bound
  refine ⟨6 * C + 4 * C ^ 2, by positivity, fun c hc t ht => ?_⟩
  have hc0 : 0 < c := by linarith
  set σ := Real.smoothTransition with hσdef
  have hsm : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  obtain ⟨hd0, h1⟩ := contDiff_infty_iff_deriv.1 hsm
  obtain ⟨hd1, -⟩ := contDiff_infty_iff_deriv.1 h1
  let u : ℝ → ℝ := fun x => 2 - 2 * (Real.log (-x) / c)
  let u' : ℝ → ℝ := fun x => -(2 * (x⁻¹ / c))
  let u'' : ℝ → ℝ := fun x => -(2 * (-(x ^ 2)⁻¹ / c))
  have hu : ∀ x, x < 0 → HasDerivAt u (u' x) x := by
    intro x hx
    have hl : HasDerivAt (fun x => Real.log (-x)) x⁻¹ x := by
      have := (hasDerivAt_neg x).log (by simpa using hx.ne)
      rwa [neg_div_neg_eq, one_div] at this
    exact ((hl.div_const c).const_mul 2).const_sub 2
  have hu' : ∀ x, x < 0 → HasDerivAt u' (u'' x) x := fun x hx =>
    (((hasDerivAt_inv hx.ne).div_const c).const_mul 2).neg
  let F : ℝ → ℝ := fun x => cutStep (Real.log (-x) / c)
  let G : ℝ → ℝ := fun x => deriv σ (u x) * u' x
  have hF : ∀ x, x < 0 → HasDerivAt F (G x) x := fun x hx =>
    (hd0 (u x)).hasDerivAt.comp x (hu x hx)
  have hG : HasDerivAt G (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) t :=
    ((hd1 (u t)).hasDerivAt.comp t (hu t ht)).mul (hu' t ht)
  have evF : deriv F =ᶠ[𝓝 t] G := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hF x hx).deriv
  have hF2 : deriv (deriv F) t = deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t :=
    (hG.congr_of_eventuallyEq evF).deriv
  have hH : ∀ x, x < 0 → HasDerivAt (fun x => F x ^ 2 / 2) (F x * G x) x := by
    intro x hx
    have := ((hF x hx).fun_mul (hF x hx)).div_const 2
    exact (this.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by ring)
  have evH : deriv (fun x => F x ^ 2 / 2) =ᶠ[𝓝 t] fun x => F x * G x := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact (hH x hx).deriv
  have hH2 : deriv (deriv fun x => F x ^ 2 / 2) t =
      G t * G t + F t * (deriv (deriv σ) (u t) * u' t * u' t + deriv σ (u t) * u'' t) :=
    (((hF t ht).fun_mul hG).congr_of_eventuallyEq evH).deriv
  have hucd : ContDiffAt ℝ 2 u t :=
    contDiffAt_const.sub (contDiffAt_const.mul ((contDiffAt_id.neg.log (by simpa using ht.ne)).div_const c))
  have hFcd : ContDiffAt ℝ 2 F t := (Real.smoothTransition.contDiffAt (n := 2)).comp t hucd
  have hf : |F t| ≤ 1 := by
    show |Real.smoothTransition (u t)| ≤ 1
    exact abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (u t)], Real.smoothTransition.le_one (u t)⟩
  obtain ⟨b1, b2⟩ := logLogStep_arith (p := deriv σ (u t)) (q := deriv (deriv σ) (u t)) hC0 hc ht.ne
    (hC _).1 (hC _).2 hf rfl rfl
  refine ⟨hFcd, (hFcd.pow 2).div_const 2, ?_, ?_⟩
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c)) t = _ from hF2]; exact b1
  · rw [show deriv (deriv fun x => cutStep (Real.log (-x) / c) ^ 2 / 2) t = _ from hH2]; exact b2

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenFixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix Metric

noncomputable section

namespace IsolatedFibreOpenOfGeneric

theorem isClosed_zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroLocus J) := by
  have h : zeroLocus J = ⋂ q ∈ J, {x | eval x q = 0} := by
    ext x
    simp [zeroLocus]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem eval_linPoly {n k : ℕ} (B : Matrix (Fin k) (Fin n) ℂ) (z : Fin n → ℂ) (i : Fin k) :
    eval z (linPoly B.mulVecLin i) = (B *ᵥ z) i := by
  simp [linPoly, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem finiteProjection_near (hGen : GenericProjectionFinite.Statement) {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsAffVariety J k) (A : Matrix (Fin k) (Fin n) ℂ) :
    ∃ M : Matrix (Fin k) (Fin n) ℂ,
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), IsFiniteProjection J (A + t • (M - A)).mulVecLin := by
  obtain ⟨⟨S, ⟨M, f, hfS, hf⟩, hS⟩, -⟩ := hGen n k J hJ.isPrime hJ.dim
  refine ⟨M, ?_⟩
  set a : Fin k × Fin n → ℂ := fun p => A p.1 p.2
  set b : Fin k × Fin n → ℂ := fun p => (M - A) p.1 p.2
  have hg : ∀ t : ℂ, eval (fun p : Fin k × Fin n => (A + t • (M - A)) p.1 p.2) f = eval (a + t • b) f :=
    fun t => rfl
  have han : ∀ t : ℂ, AnalyticAt ℂ (fun t : ℂ => eval (a + t • b) f) t := fun t =>
    (AnalyticOnNhd.eval_mvPolynomial f _ trivial).comp
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  rcases (han 0).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (fun t _ => han t)
      isPreconnected_univ (Set.mem_univ 0) h0 (Set.mem_univ 1)
    apply hf
    have h1 : (fun p : Fin k × Fin n => M p.1 p.2) = a + (1 : ℂ) • b := by
      funext p
      simp [a, b]
    rw [h1]
    exact hz
  · filter_upwards [hne] with t ht
    exact hS _ ⟨f, hfS, by rw [hg]; exact ht⟩

theorem proof (hGen : GenericProjectionFinite.Statement) (hFin : FiniteMapOpen.Statement) :
    IsolatedFibreOpen.Statement := by
  intro n k J A x hJ hx ⟨W, hW, hiso⟩ W' hW'
  have hZc : IsClosed (zeroLocus J) := isClosed_zeroLocus J
  have hAc : ∀ B : Matrix (Fin k) (Fin n) ℂ, Continuous fun z : Fin n → ℂ => B *ᵥ z :=
    fun B => continuous_const.matrix_mulVec continuous_id

  obtain ⟨r0, hr0, hr0W⟩ := Metric.mem_nhds_iff.1 (inter_mem hW hW')
  have hr : 0 < r0 / 2 := half_pos hr0
  have hcb : closedBall x (r0 / 2) ⊆ W ∩ W' :=
    (closedBall_subset_ball (half_lt_self hr0)).trans hr0W
  have hSc : IsCompact (zeroLocus J ∩ closedBall x (r0 / 2)) :=
    (isCompact_closedBall x _).inter_left hZc
  have hKc : IsCompact (zeroLocus J ∩ sphere x (r0 / 2)) := (isCompact_sphere x _).inter_left hZc

  have hAK : A *ᵥ x ∉ (fun z => A *ᵥ z) '' (zeroLocus J ∩ sphere x (r0 / 2)) := by
    rintro ⟨z, ⟨hzZ, hzs⟩, hzA⟩
    have hzx : z = x := hiso z (hcb (sphere_subset_closedBall hzs)).1 hzZ hzA
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 ((hKc.image (hAc A)).isClosed.isOpen_compl) _ hAK
  obtain ⟨M, hM⟩ := finiteProjection_near hGen hJ A
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hAc (M - A)).continuousOn
  have hAt : ∀ (t : ℂ) (z : Fin n → ℂ), (A + t • (M - A)) *ᵥ z = A *ᵥ z + t • ((M - A) *ᵥ z) :=
    fun t z => by rw [add_mulVec, smul_mulVec]
  have hclose : ∀ t : ℂ, ‖t‖ * C < ε / 4 → ∀ z ∈ zeroLocus J ∩ closedBall x (r0 / 2),
      dist ((A + t • (M - A)) *ᵥ z) (A *ᵥ z) < ε / 4 := by
    intro t ht z hz
    rw [dist_eq_norm, hAt, add_sub_cancel_left, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg t)).trans_lt ht

  have hstep : ∀ t : ℂ, IsFiniteProjection J (A + t • (M - A)).mulVecLin → ‖t‖ * C < ε / 4 →
      ball (A *ᵥ x) (ε / 4) ⊆
        (fun z => (A + t • (M - A)) *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) := by
    intro t hfin ht
    set B := A + t • (M - A) with hB
    have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (aeval fun i => linPoly B.mulVecLin i) =
        projAlgHom J B.mulVecLin := by
      rw [MvPolynomial.comp_aeval]
      rfl
    have hTo : IsOpen ((fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2))) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨z, ⟨hzZ, hzb⟩, rfl⟩
      have h := hFin n k J (fun i => linPoly B.mulVecLin i) hJ.isPrime (by rw [hcomp]; exact hfin.1)
        (by rw [hcomp]; exact hfin.2) z hzZ (ball x (r0 / 2)) (isOpen_ball.mem_nhds hzb)
      simpa only [eval_linPoly] using h
    have hTS : (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) ⊆
        (fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) :=
      Set.image_mono (Set.inter_subset_inter_right _ ball_subset_closedBall)
    have hSim : IsClosed ((fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2))) :=
      (hSc.image (hAc B)).isClosed
    have hxS : x ∈ zeroLocus J ∩ closedBall x (r0 / 2) := ⟨hx, mem_closedBall_self hr.le⟩
    have hsub : ball (A *ᵥ x) (ε / 2) ⊆ (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) := by
      refine (convex_ball _ _).isPreconnected.subset_of_closure_inter_subset hTo ?_ ?_
      · refine ⟨B *ᵥ x, ?_, x, ⟨hx, mem_ball_self hr⟩, rfl⟩
        rw [mem_ball]
        linarith [hclose t ht x hxS]
      · rintro _ ⟨hcl, hball⟩
        obtain ⟨z, hzS, rfl⟩ := closure_minimal hTS hSim hcl
        refine ⟨z, ⟨hzS.1, ?_⟩, rfl⟩
        by_contra hzb
        have hzs : z ∈ sphere x (r0 / 2) :=
          mem_sphere.2 (le_antisymm (mem_closedBall.1 hzS.2) (not_lt.1 (by simpa [mem_ball] using hzb)))
        apply hεK (show A *ᵥ z ∈ ball (A *ᵥ x) ε from ?_) ⟨z, ⟨hzS.1, hzs⟩, rfl⟩
        rw [mem_ball] at hball ⊢
        have h1 := hclose t ht z hzS
        rw [dist_comm] at h1
        linarith [dist_triangle (A *ᵥ z) (B *ᵥ z) (A *ᵥ x)]
    exact (ball_subset_ball (by linarith)).trans (hsub.trans hTS)

  have h0 : Tendsto (fun t : ℂ => ‖t‖ * C) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => ‖t‖ * C := continuous_norm.mul continuous_const
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
    simpa using h
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ * C < ε / 4 := h0.eventually (gt_mem_nhds (by positivity))
  refine mem_of_superset (ball_mem_nhds (A *ᵥ x) (by positivity : (0 : ℝ) < ε / 4)) ?_
  intro y hy
  have hz : ∀ t : ℂ, ∃ z : Fin n → ℂ,
      (∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y) →
        z ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ z = y := by
    intro t
    by_cases h : ∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose zf hzf using hz
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      zf t ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ zf t = y := by
    filter_upwards [hM, hsmall] with t h1 h2
    exact hzf t (hstep t h1 h2 hy)
  obtain ⟨a, haS, hacl⟩ := hSc (f := map zf (𝓝[≠] (0 : ℂ)))
    (le_principal_iff.2 (hev.mono fun t ht => ht.1))
  have hlim : Tendsto (fun t => A *ᵥ zf t) (𝓝[≠] (0 : ℂ)) (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [hev] with t ht
    rw [← ht.2, hAt, sub_add_cancel_left, norm_neg, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ht.1) (norm_nonneg _)
  have hay : A *ᵥ a = y :=
    eq_of_nhds_neBot (hacl.map (hAc A).continuousAt (tendsto_map'_iff.2 hlim))
  exact ⟨a, ⟨haS.1, (hcb haS.2).2⟩, hay⟩

end IsolatedFibreOpenOfGeneric

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem tendsto_nhds_of_analyticAt_eq {σ τ : Type} [Fintype σ] [Fintype τ] {h : (σ → ℂ) → (τ → ℂ)} {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : Tendsto h (𝓝 a) (𝓝 b) := by
  rw [← hab]; exact hh.continuousAt.tendsto

def germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : holGerms b →+* holGerms a where
  toFun φ := ⟨(φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab), by
      obtain ⟨f, hf, hφ⟩ := φ.2
      exact ⟨f ∘ h, hf.comp_of_eq hh hab, by rw [← hφ]; rfl⟩⟩
  map_one' := rfl
  map_mul' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ * ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) *
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_mul, ← hf, ← hg]; rfl
  map_zero' := rfl
  map_add' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ + ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) +
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_add, ← hf, ← hg]; rfl

theorem germPull_coe {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) (φ : holGerms b) (f : (τ → ℂ) → ℂ)
    (hφ : (f : Germ (𝓝 b) ℂ) = φ) : ((germPull h hh hab φ : holGerms a) : Germ (𝓝 a) ℂ) = ↑(f ∘ h) := by
  show (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) = _
  rw [← hφ]; rfl

theorem germPull_germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h₁ : (σ → ℂ) → (τ → ℂ))
    (h₂ : (τ → ℂ) → (σ → ℂ)) {a : σ → ℂ} {b : τ → ℂ} (hh₁ : AnalyticAt ℂ h₁ a) (hab : h₁ a = b)
    (hh₂ : AnalyticAt ℂ h₂ b) (hba : h₂ b = a) (h₁₂ : ∀ y, h₁ (h₂ y) = y) (φ : holGerms b) :
    germPull h₂ hh₂ hba (germPull h₁ hh₁ hab φ) = φ := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  apply Subtype.ext
  have e1 := germPull_coe h₁ hh₁ hab φ f hφ
  rw [germPull_coe h₂ hh₂ hba _ (f ∘ h₁) e1.symm, ← hφ]
  congr 1
  funext y
  simp [h₁₂]

def germAffineEquiv {σ τ : Type} [Fintype σ] [Fintype τ] (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) :
    holGerms c ≃+* holGerms (0 : σ → ℂ) :=
  have h1 : AnalyticAt ℂ (fun z : σ → ℂ => e z + c) 0 := (e.analyticAt 0).add analyticAt_const
  have h1e : (fun z : σ → ℂ => e z + c) 0 = c := by simp
  have h2 : AnalyticAt ℂ (fun y : τ → ℂ => e.symm (y - c)) c :=
    (e.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have h2e : (fun y : τ → ℂ => e.symm (y - c)) c = 0 := by simp
  RingEquiv.ofRingHom (germPull _ h1 h1e) (germPull _ h2 h2e)
    (RingHom.ext fun φ => germPull_germPull _ _ h2 h2e h1 h1e (fun z => by simp) φ)
    (RingHom.ext fun φ => germPull_germPull _ _ h1 h1e h2 h2e (fun y => by simp) φ)

theorem isNoetherianRing_holGerms_transfer {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) (h : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms c) :=
  isNoetherianRing_of_ringEquiv _ (germAffineEquiv e c).symm

theorem isField_holGerms_fin_zero : IsField (holGerms (0 : Fin 0 → ℂ)) := by
  refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {φ} hφ => ?_⟩
  · exact one_ne_zero (congrArg Subtype.val h).symm
  · obtain ⟨f, hf, hfφ⟩ := φ.2
    have hall : ∀ x : Fin 0 → ℂ, f x = f 0 := fun x => by rw [Subsingleton.elim x 0]
    have h0 : f 0 ≠ 0 := by
      intro h0
      apply hφ
      apply Subtype.ext
      rw [← hfφ]
      exact Germ.coe_eq.2 (Eventually.of_forall fun x => by rw [hall x, h0])
    refine ⟨⟨↑(fun x => (f x)⁻¹), fun x => (f x)⁻¹, hf.inv h0, rfl⟩, ?_⟩
    apply Subtype.ext
    change (φ : Germ (𝓝 (0 : Fin 0 → ℂ)) ℂ) * ↑(fun x => (f x)⁻¹) = 1
    rw [← hfφ]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => by
      show f x * (f x)⁻¹ = 1
      rw [hall x]
      exact mul_inv_cancel₀ h0)

theorem isNoetherianRing_holGerms_option (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) (σ : Type) [Fintype σ]
    (hR : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms (0 : Option σ → ℂ)) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  obtain ⟨φ, hφI, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := by
    intro h
    apply hφ0
    apply Subtype.ext
    rw [← hfφ]
    exact Germ.coe_eq.2 h
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz

  let Pl : (Option σ → ℂ) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let Tl : (Option σ → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let ι : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ) := germPull Pl (Pl.analyticAt 0) (map_zero Pl)
  let τ : holGerms (0 : Option σ → ℂ) := ⟨↑(Tl : (Option σ → ℂ) → ℂ), Tl, Tl.analyticAt 0, rfl⟩
  let Φ : (Fin d → holGerms (0 : σ → ℂ)) → holGerms (0 : Option σ → ℂ) :=
    fun a => ∑ j : Fin d, ι (a j) * τ ^ (j : ℕ)
  have Φ_add : ∀ a b, Φ (a + b) = Φ a + Φ b := fun a b => by
    simp only [Φ, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  have Φ_smul : ∀ (r : holGerms (0 : σ → ℂ)) a, Φ (r • a) = ι r * Φ a := fun r a => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]
  have Φ_zero : Φ 0 = 0 := by simp [Φ]
  let N : Submodule (holGerms (0 : σ → ℂ)) (Fin d → holGerms (0 : σ → ℂ)) :=
    { carrier := {a | Φ a ∈ I}
      add_mem' := fun {a b} ha hb => by
        change Φ (a + b) ∈ I
        rw [Φ_add]; exact I.add_mem ha hb
      zero_mem' := by
        change Φ 0 ∈ I
        rw [Φ_zero]; exact I.zero_mem
      smul_mem' := fun r a ha => by
        change Φ (r • a) ∈ I
        rw [Φ_smul]; exact Ideal.mul_mem_left I _ ha }
  obtain ⟨s, hs⟩ : N.FG := IsNoetherian.noetherian N
  refine ⟨insert φ (s.image Φ), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro ψ hψ
    rw [Finset.coe_insert, Set.mem_insert_iff] at hψ
    rcases hψ with rfl | hψ
    · exact hφI
    · rw [Finset.coe_image] at hψ
      obtain ⟨a, ha, rfl⟩ := hψ
      have : a ∈ N := hs ▸ Submodule.subset_span ha
      exact this
  · intro ψ hψ
    obtain ⟨g, hg, hgψ⟩ := ψ.2
    have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)
    have hgA : AnalyticAt ℂ (g ∘ A) 0 := hg.comp_of_eq (A.analyticAt 0) (map_zero A)
    obtain ⟨q, a, hq, ha, hev⟩ := hD σ d (f ∘ A) (g ∘ A) hfA hgA hAd
    have hqB : AnalyticAt ℂ (q ∘ A.symm) 0 := hq.comp_of_eq (A.symm.analyticAt 0) (map_zero _)
    let Q : holGerms (0 : Option σ → ℂ) := ⟨↑(q ∘ A.symm), q ∘ A.symm, hqB, rfl⟩
    let a' : Fin d → holGerms (0 : σ → ℂ) := fun j => ⟨↑(a j), a j, ha j, rfl⟩
    have hev' : ∀ᶠ y in 𝓝 (0 : Option σ → ℂ),
        g y = q (A.symm y) * f y + ∑ j : Fin d, a j (Pl y) * Tl y ^ (j : ℕ) := by
      have hB : Tendsto A.symm (𝓝 0) (𝓝 0) := by
        simpa using A.symm.continuous.tendsto (0 : Option σ → ℂ)
      filter_upwards [hB.eventually hev] with y hy
      simpa [Pl, Tl] using hy
    have key : ψ = Q * φ + Φ a' := by
      apply Subtype.ext
      have hι : ∀ j, ((ι (a' j) : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
          ↑(a j ∘ Pl) := fun j => germPull_coe _ _ _ (a' j) (a j) rfl
      simp only [Φ, Subring.coe_add, Subring.coe_mul, ← hfφ, ← hgψ]
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [Subring.coe_mul, Subring.coe_pow, hι]
      change (↑g : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = Germ.coeRingHom _ (q ∘ A.symm) * Germ.coeRingHom _ f +
        ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ Pl) * Germ.coeRingHom _ (Tl : (Option σ → ℂ) → ℂ) ^ (j : ℕ)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_mul, ← map_pow, ← map_sum, ← map_add (f := _)]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev'] with y hy
      simp [hy, Finset.sum_apply]
    have hΦ : Φ a' ∈ I := by
      have : Φ a' = ψ - Q * φ := by rw [key]; ring
      rw [this]; exact I.sub_mem hψ (Ideal.mul_mem_left I _ hφI)
    have ha'N : a' ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))) := by
      rw [hs]; exact hΦ
    have hgen : ∀ x ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))),
        Φ x ∈ Ideal.span (↑(insert φ (s.image Φ)) : Set (holGerms (0 : Option σ → ℂ))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Ideal.subset_span (by
          rw [Finset.coe_insert, Finset.coe_image]
          exact Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
      | zero => rw [Φ_zero]; exact Ideal.zero_mem _
      | add x y _ _ hx hy => rw [Φ_add]; exact Ideal.add_mem _ hx hy
      | smul r x _ hx => rw [Φ_smul]; exact Ideal.mul_mem_left _ _ hx
    have hspan := hgen a' ha'N
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) hspan

theorem AnalyticGermsNoetherian.proof (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) : AnalyticGermsNoetherian.Statement := by
  have hfin : ∀ n : ℕ, IsNoetherianRing (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := (isField_holGerms_fin_zero).toField
      infer_instance
    | succ n ih =>
      have h := isNoetherianRing_holGerms_option hD hG (Fin n) ih
      exact isNoetherianRing_holGerms_transfer
        (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv 0 h
  intro σ _ w
  exact isNoetherianRing_holGerms_transfer
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv w (hfin _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDoublePointsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

def NormalDoublePointsGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I → NormalDoublePointsOnDivisor M u q

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeCollarMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      Integrable ({y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeDeepMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      Integrable ({y | logAbsSq P y < -Real.exp 1}.indicator (tubeDens J A P R (fun _ => euclPot)))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
      ∀ L ∈ O, ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
        P ≠ RingHom.ker (eval q) →
          ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularInjectivePieces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegularInjectivePieces.Statement : Prop :=
  ∀ (d : ℕ) (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin d → ℂ), IsOpen U → DifferentiableOn ℂ g U →
    ∃ P : ℕ → Set (Fin d → ℂ), (∀ i, MeasurableSet (P i)) ∧ Pairwise (Function.onFun Disjoint P) ∧
      ⋃ i, P i = {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
      ∀ i, Set.InjOn g (P i)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAwayZariski
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAwayZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
      ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
        ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
          P ≠ RingHom.ker (eval q) →
            ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def TubeCollarCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 →
      ∃ C : ℝ, ∀ y, {y | -Real.exp 1 ≤ logAbsSq P y}.indicator (tubeDens J A P R (fun _ => euclPot)) y ≤
        C * chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
          (fun _ : Fin (d + 1) => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntCountAdd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ChartIntCountAdd.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    Continuous f → HasCompactSupport f → (∀ k, SmoothNear (zeroSet W) (φ k)) →
    (∀ i, MeasurableSet (E i)) → Pairwise (Function.onFun Disjoint E) →
      HasSum (fun i => chartInt W A ((E i).indicator f) φ) (chartInt W A ((⋃ i, E i).indicator f) φ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorOneComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

def DivisorOneComponent.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ I : Ideal (MvPolynomial (Fin n) ℂ), J ⊔ Ideal.span {linForm u} ≤ I ∧
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) ∧
        ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
          ∃ W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W ∧
            (∀ W' ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes, q ∈ zeroSet W' → W' = W) ∧
            ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamCritNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamCritNull.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    DifferentiableOn ℂ σ (Metric.ball 0 r) → Set.InjOn σ (Metric.ball 0 r) → IsOpen N →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W) →
      volume {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamOffRegularZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamOffRegularZero.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (σ : (Fin d → ℂ) → Fin n → ℂ) (r : ℝ) (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), tsupport f ⊆ N →
      chartInt W A ((σ '' {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0})ᶜ.indicator f)
        φ = 0

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def RegFormCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → Continuous f → HasCompactSupport f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin n → ℂ) (ε : ℝ), 0 < ε →
        ∀ v w : (Fin n → ℂ) → ℝ, (∀ x, 0 ≤ w x) → (∀ x ∈ tsupport f, |v x| ≤ w x) →
          ∀ y, chartAbsDens J A (fun x => v x * f x) (vecCons (logReg u ε) φ) y ≤
            C * chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamDensIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ParamDensIntegrable.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (σ : (Fin d → ℂ) → Fin n → ℂ) (r r' : ℝ)
    (N : Set (Fin n → ℂ)),
    DifferentiableOn ℂ σ (Metric.ball 0 r) → r' < r →
    (∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r') →
    ∀ (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      Continuous f → tsupport f ⊆ N → (∀ i, SmoothNear (zeroSet W) (φ i)) →
        IntegrableOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w)
          (Metric.ball (0 : Fin d → ℂ) r)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLogDensNonneg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def logDistSq {n : ℕ} (x : Fin n → ℂ) (z : Fin n → ℂ) : ℝ :=
  Real.log (euclPot (z - x))

def RegLogDensNonneg.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ),
    0 < ε → z ≠ x → IsSheetAt J A z s →
      0 ≤ ReciprocityTheory.AnForm.maDens
        (fun k => (vecCons (logReg u ε) fun _ => logDistSq x : Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ s)
        (A *ᵥ z)

end

end GroundTheory.Heights₂.Heights
end
