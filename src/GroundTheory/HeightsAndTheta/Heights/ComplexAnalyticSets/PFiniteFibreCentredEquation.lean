module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongRegularise
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalTrace

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteFibreCentredEquation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable def FiniteFibreCentredEquation.centredPoly (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : ℂ[X] :=
  (X - C a) ^ k + ∑ j : Fin k, C (c j) * (X - C a) ^ (j : ℕ)

theorem FiniteFibreCentredEquation.centredPoly_eval (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = (T - a) ^ k + ∑ j, c j * (T - a) ^ (j : ℕ) := by
  simp [FiniteFibreCentredEquation.centredPoly, eval_finsetSum]

theorem FiniteFibreCentredEquation.centredPoly_coeff (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (m : ℕ) :
    (FiniteFibreCentredEquation.centredPoly a c).coeff m =
      ((X - C a) ^ k).coeff m + ∑ j : Fin k, c j * ((X - C a) ^ (j : ℕ)).coeff m := by
  simp [FiniteFibreCentredEquation.centredPoly, finsetSum_coeff, coeff_C_mul]

theorem FiniteFibreCentredEquation.centredPoly_natDegree_lt (a : ℂ) {k : ℕ} (c : Fin k → ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).natDegree < k + 1 := by
  refine Nat.lt_succ_of_le (natDegree_add_le_of_degree_le ?_ ?_)
  · rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans ?_
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
    exact j.isLt.le

theorem FiniteFibreCentredEquation.centredPoly_coeff_top (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : (FiniteFibreCentredEquation.centredPoly a c).coeff k = 1 := by
  rw [FiniteFibreCentredEquation.centredPoly_coeff]
  have h1 : ((X - C a) ^ k).coeff k = 1 := by
    have h := ((monic_X_sub_C a).pow k).coeff_natDegree
    rwa [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have h2 : ∀ j : Fin k, ((X - C a) ^ (j : ℕ)).coeff k = 0 := fun j =>
    coeff_eq_zero_of_natDegree_lt (by
      rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]; exact j.isLt)
  simp [h1, h2]

theorem FiniteFibreCentredEquation.centredPoly_eval_expand (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = T ^ k + ∑ m : Fin k, (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ (m : ℕ) := by
  rw [eval_eq_sum_range' (FiniteFibreCentredEquation.centredPoly_natDegree_lt a c), Finset.sum_range_succ, FiniteFibreCentredEquation.centredPoly_coeff_top,
    Finset.sum_range (fun m => (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ m)]
  ring

theorem FiniteFibreCentredEquation.proof (hI : FiniteFibreGermIntegral.Statement)
    (hW : WeierstrassPreparation.Statement) : FiniteFibreCentredEquation.Statement := by
  intro σ _ S w d A hS hfib g hg
  obtain ⟨N, a, ha, hrel⟩ := hI σ S w d A hS hfib (fun z => g z - g w) (hg.sub analyticAt_const)
  set f : (Option (Fin d) → ℂ) → ℂ := fun x =>
    x none ^ N + ∑ j, a j (A w + fun i => x (some i)) * x none ^ (j : ℕ) with hf_def
  have hlast : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => x none) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) none).analyticAt 0
  have hfirst : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => A w + fun i => x (some i)) 0 :=
    analyticAt_const.add ((ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) (some i)).analyticAt 0)
  have hfan : AnalyticAt ℂ f 0 := by
    refine (hlast.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp_of_eq hfirst (show A w + (0 : Fin d → ℂ) = A w from add_zero _)).mul (hlast.pow _)

  set p : ℂ[X] := X ^ N + ∑ j : Fin N, C (a j (A w)) * X ^ (j : ℕ) with hp_def
  have hpm : p.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hpe : (fun t => f (pointWithLast 0 t)) = fun t => p.eval t := by
    funext t
    have h0 : (fun i => pointWithLast (0 : Fin d → ℂ) t (some i)) = 0 := rfl
    simp only [hf_def, hp_def, h0, add_zero, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hne : analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 ≠ ⊤ := by
    rw [hpe]
    intro htop
    have hpan : AnalyticOnNhd ℂ (fun t => p.eval t) Set.univ := fun t _ =>
      (Polynomial.differentiable p).analyticAt t
    have hall : Set.EqOn (fun t => p.eval t) 0 Set.univ :=
      hpan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (analyticOrderAt_eq_top.1 htop)
    exact hpm.ne_zero (Polynomial.funext fun t => by simpa using hall (Set.mem_univ t))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = k :=
    ⟨_, (Nat.cast_analyticOrderNatAt hne).symm⟩
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hW (Fin d) k f hfan hk
  refine ⟨k, fun m y => (FiniteFibreCentredEquation.centredPoly (g w) fun j => c j (y - A w)).coeff m, fun m => ?_, fun T => ?_, ?_⟩
  · simp only [FiniteFibreCentredEquation.centredPoly_coeff]
    refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((hc j).comp_of_eq (f := fun y : Fin d → ℂ => y - A w) (analyticAt_id.sub analyticAt_const)
      (sub_self _)).mul analyticAt_const
  · rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    simp [hc0]
  ·
    set φ : (σ → ℂ) → (Option (Fin d) → ℂ) := fun z => pointWithLast (A z - A w) (g z - g w) with hφ_def
    have hφc : ContinuousAt φ w := by
      refine continuousAt_pi.2 fun o => ?_
      cases o with
      | none => exact hg.continuousAt.sub continuousAt_const
      | some i => exact ((continuous_apply i).comp A.continuous).continuousAt.sub continuousAt_const
    have hφw : φ w = 0 := by
      funext o; cases o <;> simp [hφ_def, pointWithLast]
    have hφt : Tendsto φ (𝓝 w) (𝓝 0) := hφw ▸ hφc.tendsto
    filter_upwards [hφt.eventually hfe, hφt.eventually (he.continuousAt.eventually_ne he0), hrel]
      with z h1 h2 h3 hzX
    have hf0 : f (φ z) = 0 := by
      show (g z - g w) ^ N + ∑ j, a j (A w + (A z - A w)) * (g z - g w) ^ (j : ℕ) = 0
      rw [add_sub_cancel]
      exact h3 hzX
    have hω : (g z - g w) ^ k + ∑ j, c j (A z - A w) * (g z - g w) ^ (j : ℕ) = 0 := by
      rw [hf0] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    exact hω

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffShape
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology
open scoped ContDiff

noncomputable section

private def cutProfile (k : ℕ) (w : ℝ) : ℝ :=
  if w = 0 then 0 else if 1 ≤ w then 1 else cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))

private theorem cutStep_small (k : ℕ) {w : ℝ} (h0 : w ≠ 0) (hw : |w| < cutLevel k) :
    cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : Real.log w < -Real.exp ((k : ℝ) + 1) := by
    rw [← Real.log_abs, ← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (abs_pos.2 h0) hw
  have h2 : (k : ℝ) + 1 < Real.log (-Real.log w) := by
    rw [← Real.log_exp ((k : ℝ) + 1)]
    exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  have h3 : 1 < Real.log (-Real.log w) / ((k : ℝ) + 1) := (one_lt_div hk).2 h2
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cutStep_large (k : ℕ) {w : ℝ} (hw : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < w)
    (h1 : w < 1) : cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw0 : 0 < w := (Real.exp_pos _).trans hw
  have hl : -Real.exp (((k : ℝ) + 1) / 2) < Real.log w := by
    rw [← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (Real.exp_pos _) hw
  have hneg : 0 < -Real.log w := neg_pos.2 (Real.log_neg hw0 h1)
  have h2 : Real.log (-Real.log w) < ((k : ℝ) + 1) / 2 := by
    rw [← Real.log_exp (((k : ℝ) + 1) / 2)]
    exact Real.log_lt_log hneg (by linarith)
  have h3 : Real.log (-Real.log w) / ((k : ℝ) + 1) < 1 / 2 := by
    rw [div_lt_iff₀ hk]; linarith
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutProfile_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ∞ (cutProfile k) (Set.Ioi (-cutLevel k)) := by
  obtain ⟨hc0, hc1⟩ := cutLevel_mem k
  set c' := Real.exp (-Real.exp (((k : ℝ) + 1) / 2))
  have hc'1 : c' < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))
  refine (isOpen_Ioi.contDiffOn_iff).2 fun x hx => ?_
  rcases lt_or_ge x (cutLevel k) with hxc | hxc
  ·
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (Set.mem_Ioi.1 hx) hxc] with w hw
    have hwa : |w| < cutLevel k := abs_lt.2 hw
    unfold cutProfile
    split_ifs with h0 h1
    · rfl
    · exact absurd (h1.trans_lt (hw.2.trans hc1)) (lt_irrefl _)
    · exact cutStep_small k h0 hwa
  rcases lt_or_ge c' x with hxc' | hxc'
  ·
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxc'] with w hw
    have hw0 : 0 < w := (Real.exp_pos _).trans hw
    unfold cutProfile
    split_ifs with h0 h1
    · exact absurd h0 hw0.ne'
    · rfl
    · exact cutStep_large k hw (not_le.1 h1)
  ·
    have hx0 : 0 < x := hc0.trans_le hxc
    have hx1 : x < 1 := hxc'.trans_lt hc'1
    have hform : ContDiffAt ℝ ∞ (fun w => cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))) x := by
      have hlog : ContDiffAt ℝ ∞ (fun w => Real.log (-Real.log w)) x :=
        ((Real.contDiffAt_log.2 hx0.ne').neg).log (neg_ne_zero.2 (Real.log_neg hx0 hx1).ne)
      exact Real.smoothTransition.contDiffAt.comp x
        (contDiffAt_const.sub (contDiffAt_const.mul (hlog.div_const _)))
    refine hform.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx0 hx1] with w hw
    simp [cutProfile, hw.1.ne', not_le.2 hw.2]

theorem CutOffShape.proof : CutOffShape.Statement := by
  intro m Q
  have hF : ∀ k, logLogCut Q k = cutProfile k ∘ fun y => ‖eval y Q‖ ^ 2 := fun k => rfl
  have hstep : ∀ t, cutStep t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨fun k => ⟨?_, fun y => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · rw [hF]
    have hw : ContDiff ℝ ∞ fun y : Fin m → ℂ => ‖eval y Q‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp
        (((AnalyticOnNhd.eval_mvPolynomial Q).contDiff (n := ∞)).restrict_scalars ℝ)
    exact (cutProfile_contDiffOn k).comp_contDiff hw fun y =>
      (neg_neg_of_pos (cutLevel_mem k).1).trans_le (by exact sq_nonneg ‖eval y Q‖)
  · unfold logLogCut; split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hstep _
  · have h1 := (cutLevel_mem k).2
    unfold logLogCut logAbsSq; split_ifs with h0 h1'
    · rfl
    · exact absurd (h1'.trans_lt (hy.trans h1)) (lt_irrefl _)
    · exact cutStep_small k h0 (by rwa [abs_of_nonneg (by positivity)])
  · have hw0 : ‖eval y Q‖ ^ 2 ≠ 0 := by positivity
    by_cases hw1 : 1 ≤ ‖eval y Q‖ ^ 2
    · simp [logLogCut, hw0, hw1]
    refine tendsto_const_nhds.congr' ?_
    set L := Real.log (-Real.log (‖eval y Q‖ ^ 2))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * |L|)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : L / ((k : ℝ) + 1) < 1 / 2 := by
      rw [div_lt_iff₀ hk']; linarith [le_abs_self L]
    simp only [logLogCut, logAbsSq, hw0, hw1, if_false]
    exact (Real.smoothTransition.one_of_one_le (by linarith)).symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietySlabMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

namespace VarietySlabMeasure

theorem isFiniteLinProj_of {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A :=
  ⟨h.injective, h.finite⟩

theorem fibreCount_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {U : Matrix (Fin n) (Fin n) ℂ}
    {s : Fin d → Fin n} (hA : ComplexSets.IsFiniteProjection J (U.submatrix s id))
    (B : Set (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin d)) :
    {z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard ≤
      ComplexSets.projDegree J (U.submatrix s id) := by
  obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.proof n d J _ hJ hd hA (WithLp.ofLp x)
  calc _ ≤ (ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).encard := by
        refine Set.encard_le_encard_of_injOn (f := fun z : EuclideanSpace ℂ (Fin n) => WithLp.ofLp z)
          ?_ (fun a _ b _ h => WithLp.ofLp_injective 2 h)
        rintro z ⟨⟨hz, -⟩, hx⟩
        exact ⟨hz, congrArg WithLp.ofLp hx⟩
    _ = ((ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).ncard : ℕ∞) :=
        hfin.cast_ncard_eq.symm
    _ ≤ _ := by exact_mod_cast hle

end VarietySlabMeasure

theorem VarietySlabMeasure.proof (hG : ComplexSets.FiniteProjectionsGeneric.Statement)
    (hW : VarietyProjectionMass.Statement) (hP : IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement) :
    VarietySlabMeasure.Statement := by
  classical
  intro n d J u hJ hdim hu R
  rcases hdim.lt_or_eq with hlt | heq
  · refine ⟨1, 1, one_pos, one_pos, fun ε _ _ => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) := measure_mono (by exact fun z hz => hz.1)
      _ = 0 := NullSmaller.proof n d J hlt
      _ ≤ _ := by simp
  obtain ⟨U, hU, hfin⟩ := (hG n d J hJ heq).2.2 1 (fun _ => 1)
  have hA : ∀ s : Fin d → Fin n, StrictMono s →
      ComplexSets.IsFiniteProjection J (U.submatrix s id) := fun s hs => by
    simpa using hfin 0 ⟨s, hs.injective⟩

  have hQ : ∀ s : Fin d → Fin n, ∃ Q : MvPolynomial (Fin d) ℂ, StrictMono s → Q ≠ 0 ∧
      ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval ((U.submatrix s id).mulVec fun j => z j) Q‖ ≤ ‖∑ j, u j * z j‖ := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨Q, hQ0, hb⟩ := IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine n d J (U.submatrix s id) u hJ
        (VarietySlabMeasure.isFiniteLinProj_of (hA s hs)) hu
      obtain ⟨C, hC⟩ := hb R
      have hK : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
      refine ⟨MvPolynomial.C ((max C 1 : ℝ) : ℂ)⁻¹ * Q, fun _ => ⟨?_, fun z hz hzR => ?_⟩⟩
      · exact mul_ne_zero (by simpa using hK.ne') hQ0
      · rw [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_of_nonneg hK.le, inv_mul_le_iff₀ hK]
        exact (hC z hz hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact ⟨0, fun h => absurd h hs⟩
  choose Q hQ using hQ

  have hR' : ∀ s : Fin d → Fin n, ∃ R' : ℝ, 0 < R' ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ R → ‖rowsProj U s z‖ < R' := by
    intro s
    have hc : Continuous (rowsProj U s) := by
      unfold rowsProj
      fun_prop
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max K 0 + 1, by positivity, fun z hz => ?_⟩
    have := hK z (mem_closedBall_zero_iff.mpr hz)
    linarith [le_max_left K 0]
  choose R' hR'0 hR' using hR'

  have hS : ∀ s : Fin d → Fin n, ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ (StrictMono s → ∀ η : ℝ, 0 < η → η ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
        ‖eval (fun i => x i) (Q s)‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)) := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨C, α, hC, hα, hb⟩ := hP d (Q s) (hQ s hs).1 (R' s) (hR'0 s)
      exact ⟨C, α, hC, hα, fun _ => hb⟩
    · exact ⟨1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose C α hC hα hS using hS
  set T := Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s) with hT

  obtain ⟨α₀, hα₀, hα₀le⟩ : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ s ∈ T, α₀ ≤ α s := by
    by_cases hne : T.Nonempty
    · exact ⟨T.inf' hne α, (Finset.lt_inf'_iff hne).2 fun s _ => hα s,
        fun s hs => Finset.inf'_le _ hs⟩
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
  set N : (Fin d → Fin n) → ℕ := fun s => ComplexSets.projDegree J (U.submatrix s id)
  have hNC : 0 ≤ ∑ s ∈ T, (N s : ℝ) * C s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hC s).le
  refine ⟨∑ s ∈ T, (N s : ℝ) * C s + 1, α₀, by linarith, hα₀, fun ε hε hε1 => ?_⟩
  set B : Set (EuclideanSpace ℂ (Fin n)) := {z | ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
  have hB : MeasurableSet B := by
    have hc : Continuous fun z : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * z j‖ := by fun_prop
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le hc.measurable measurable_const)
  have hεα : 0 < ε ^ α₀ := Real.rpow_pos_of_pos hε _
  have hterm : ∀ s ∈ T,
      (⨆ x : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
          μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B)) ≤
        ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := by
    intro s hs
    have hs' : StrictMono s := (Finset.mem_filter.mp hs).2
    rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
    · refine iSup_le fun x => ?_
      have := VarietySlabMeasure.fibreCount_le hJ heq (hA s hs') B x
      exact_mod_cast ENat.toENNReal_le.mpr this
    · calc _ ≤ μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
            ‖eval (fun i => x i) (Q s)‖ ≤ ε} := by
            refine measure_mono ?_
            rintro _ ⟨z, ⟨hz, hzR, hzε⟩, rfl⟩
            exact ⟨mem_ball_zero_iff.mpr (hR' s z hzR), ((hQ s hs').2 z hz hzR).trans hzε⟩
        _ ≤ ENNReal.ofReal (C s * ε ^ α s) := hS s hs' ε hε hε1
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hε hε1 (hα₀le s hs)) (hC s).le)
  calc μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
        = μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) := rfl
    _ ≤ _ := hW n d J hJ heq U hU B hB
    _ ≤ ∑ s ∈ T, ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ s ∈ T, (N s : ℝ) * C s * ε ^ α₀) :=
        (ENNReal.ofReal_sum_of_nonneg fun s _ => by have := hC s; positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, add_mul, one_mul]
        linarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormMinimalFactorPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace PrimitiveFormMinimalFactorPoints

open Topology Filter Polynomial

def anSub {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem coeff_analyticAt {d : ℕ} {y₀ : Fin d → ℂ} {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (h : E ∈ liftsRing (anSub y₀).subtype) (k : ℕ) : AnalyticAt ℂ (E.coeff k) y₀ := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at h
  obtain ⟨f, hf⟩ := h k
  rw [← hf]
  exact f.2

theorem C_mem {d : ℕ} {y₀ : Fin d → ℂ} {f : (Fin d → ℂ) → ℂ} (hf : AnalyticAt ℂ f y₀) :
    C f ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact C_mem_lifts (anSub y₀).subtype ⟨f, hf⟩

theorem X_mem {d : ℕ} (y₀ : Fin d → ℂ) : (X : Polynomial ((Fin d → ℂ) → ℂ)) ∈ liftsRing (anSub y₀).subtype := by
  rw [← lifts_iff_liftsRing]
  exact X_mem_lifts _

theorem eval₂_eq_zero_of_dvd {d n : ℕ} {b : Fin n → (Fin d → ℂ) → ℂ} {y : Fin d → ℂ}
    {E : Polynomial ((Fin d → ℂ) → ℂ)}
    (hd : (X ^ n + ∑ j, C (b j y) * X ^ (j : ℕ) : Polynomial ℂ) ∣ E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y))
    {τ : ℂ} (hτ : τ ^ n + ∑ j, b j y * τ ^ (j : ℕ) = 0) :
    E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) τ = 0 := by
  obtain ⟨G, hG⟩ := hd
  rw [← eval_map, hG, eval_mul]
  simp [eval_finsetSum, hτ]

theorem cleared_eq {n : ℕ} (c : Fin n → ℂ) (D x : ℂ) :
    (D * x) ^ n + ∑ j : Fin n, c j * D ^ (n - j) * (D * x) ^ (j : ℕ) =
      D ^ n * (x ^ n + ∑ j : Fin n, c j * x ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_sub_mul_pow D j.2.le]
  ring

theorem linear_apply_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ] {F : Type} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (L : (σ → ℂ) →L[ℂ] F) (v : σ → ℂ) :
    L v = ∑ i, v i • L (fun j => if i = j then 1 else 0) :=
  LinearMap.pi_apply_eq_sum_univ (L : (σ → ℂ) →ₗ[ℂ] F) v

theorem roots_near_centred {E : Type*} [TopologicalSpace E] {n : ℕ} (b : Fin n → E → ℂ) (y₀ : E) (u : ℂ)
    (hb : ∀ j, ContinuousAt (b j) y₀) (h0 : ∀ T : ℂ, T ^ n + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u) ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : ℂ, x ^ n + ∑ j, b j y * x ^ (j : ℕ) = 0 → ‖x - u‖ < ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Eventually.of_forall fun y x hx => by simp at hx
  set S : E → ℝ := fun y => ∑ j, ‖b j y‖ with hS
  set B : ℝ := max 1 (S y₀ + 1) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hSt : Tendsto S (𝓝 y₀) (𝓝 (S y₀)) :=
    tendsto_finsetSum _ fun j _ => (hb j).tendsto.norm
  have hDt : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 0) := by
    have : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀)
        (𝓝 (∑ j : Fin n, ‖b j y₀ - b j y₀‖ * B ^ (j : ℕ))) :=
      tendsto_finsetSum _ fun j _ => ((tendsto_const_nhds.sub (hb j).tendsto).norm).mul_const _
    simpa using this
  have hεn : (0 : ℝ) < ε ^ n := pow_pos hε n
  filter_upwards [hSt.eventually (gt_mem_nhds (lt_add_one (S y₀))), hDt.eventually (gt_mem_nhds hεn)]
    with y hSy hDy x hx
  have hxB : ‖x‖ ≤ B := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans hB1
    replace hx1 := lt_of_not_ge hx1
    have hxn : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    have hle : ‖x‖ ^ n ≤ S y * ‖x‖ ^ (n - 1) := by
      calc ‖x‖ ^ n = ‖∑ j, b j y * x ^ (j : ℕ)‖ := by rw [← norm_pow, hxn, norm_neg]
        _ ≤ ∑ j, ‖b j y * x ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin n, ‖b j y‖ * ‖x‖ ^ (n - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1.le (by omega)) (norm_nonneg _)
        _ = S y * ‖x‖ ^ (n - 1) := by rw [hS, Finset.sum_mul]
    have hpos : 0 < ‖x‖ ^ (n - 1) := pow_pos (zero_lt_one.trans hx1) _
    have : ‖x‖ * ‖x‖ ^ (n - 1) ≤ S y * ‖x‖ ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]; exact hle
    have hxS : ‖x‖ ≤ S y := le_of_mul_le_mul_right this hpos
    exact hxS.trans (hSy.le.trans (le_max_right _ _))
  have hid : (x - u) ^ n = ∑ j, (b j y₀ - b j y) * x ^ (j : ℕ) := by
    rw [← h0 x]
    have : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    rw [this]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hle : ‖x - u‖ ^ n ≤ ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
    calc ‖x - u‖ ^ n = ‖∑ j, (b j y₀ - b j y) * x ^ (j : ℕ)‖ := by rw [← norm_pow, hid]
      _ ≤ ∑ j, ‖(b j y₀ - b j y) * x ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxB _) (norm_nonneg _)
  have : ‖x - u‖ ^ n < ε ^ n := hle.trans_lt hDy
  exact lt_of_pow_lt_pow_left₀ n hε.le this

theorem proof (hMin : GermMinimalPolynomialDivides.Statement) (hCen : FiniteFibreCentredEquation.Statement)
    (hRem : PrimitiveFormRemainder.Statement) : PrimitiveFormMinimalFactorPoints.Statement := by
  classical
  intro σ _ Y w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδne hp hsep hrel
  obtain ⟨n, b, hb, hmX, hdiv⟩ := hMin σ Y w d A hX hirr hiso hinj ℓ (ℓ.analyticAt w)
  choose nW cW hcW hcW0 hWX using fun i : σ =>
    hCen σ Y w d A hX hiso (fun z => z i) ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  obtain ⟨V, K, f, hVo, hwV, hf, hXV⟩ := hX
  choose M R hR hRz using fun k : Fin K => hRem σ w d A ℓ N δ q nW cW (f k) hδ hq hcW hcW0 (hf k w hwV)
  set ev : (Fin d → ℂ) → ((Fin d → ℂ) → ℂ) →+* ℂ := fun y => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y with hev
  have hevC : ∀ y (g : (Fin d → ℂ) → ℂ), ev y g = g y := fun _ _ => rfl
  set e : σ → σ → ℂ := fun i j => if i = j then 1 else 0 with he

  set Q : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i => ∑ j, C (q i j) * X ^ (j : ℕ) with hQdef
  have hQ : ∀ i, Q i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (hq i j)) (Subring.pow_mem _ (X_mem _) _)
  have hQe : ∀ i y t, (Q i).eval₂ (ev y) t = ∑ j, q i j y * t ^ (j : ℕ) := by
    intro i y t; simp [hQdef, eval₂_finsetSum, hevC]
  have hproj : ∀ r : Fin d, AnalyticAt ℂ (fun y : Fin d → ℂ => y r) (A w) := fun r =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) r).analyticAt _
  set Ep : Polynomial ((Fin d → ℂ) → ℂ) := X ^ N + ∑ j, C (a j) * X ^ (j : ℕ) with hEp
  set EA : Fin d → Polynomial ((Fin d → ℂ) → ℂ) := fun r =>
    ∑ i, C (fun _ => A (e i) r) * Q i - C (fun y => δ y * y r) with hEA
  set El : Polynomial ((Fin d → ℂ) → ℂ) := ∑ i, C (fun _ => ℓ (e i)) * Q i - C δ * X with hEl
  set EW : σ → Polynomial ((Fin d → ℂ) → ℂ) := fun i =>
    Q i ^ nW i + ∑ j, C (fun y => cW i j y * δ y ^ (nW i - j)) * Q i ^ (j : ℕ) with hEW
  have hEpc : Ep ∈ liftsRing (anSub (A w)).subtype :=
    Subring.add_mem _ (Subring.pow_mem _ (X_mem _) _)
      (Subring.sum_mem _ fun j _ => Subring.mul_mem _ (C_mem (ha j)) (Subring.pow_mem _ (X_mem _) _))
  have hEAc : ∀ r, EA r ∈ liftsRing (anSub (A w)).subtype := fun r =>
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (C_mem (hδ.mul (hproj r)))
  have hElc : El ∈ liftsRing (anSub (A w)).subtype :=
    Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (C_mem analyticAt_const) (hQ i))
      (Subring.mul_mem _ (C_mem hδ) (X_mem _))
  have hEWc : ∀ i, EW i ∈ liftsRing (anSub (A w)).subtype := fun i =>
    Subring.add_mem _ (Subring.pow_mem _ (hQ i) _) (Subring.sum_mem _ fun j _ =>
      Subring.mul_mem _ (C_mem ((hcW i j).mul (hδ.pow _))) (Subring.pow_mem _ (hQ i) _))

  have hEpe : ∀ y t, Ep.eval₂ (ev y) t = t ^ N + ∑ j, a j y * t ^ (j : ℕ) := by
    intro y t; simp [hEp, eval₂_finsetSum, hevC]
  have hEAe : ∀ r y t, (EA r).eval₂ (ev y) t = ∑ i, A (e i) r * ∑ j, q i j y * t ^ (j : ℕ) - δ y * y r := by
    intro r y t; simp [hEA, eval₂_finsetSum, hevC, hQe]
  have hEle : ∀ y t, El.eval₂ (ev y) t = ∑ i, ℓ (e i) * ∑ j, q i j y * t ^ (j : ℕ) - δ y * t := by
    intro y t; simp [hEl, eval₂_finsetSum, hevC, hQe]
  have hEWe : ∀ i y t, (EW i).eval₂ (ev y) t = (∑ j, q i j y * t ^ (j : ℕ)) ^ nW i +
      ∑ j : Fin (nW i), cW i j y * δ y ^ (nW i - j) * (∑ j, q i j y * t ^ (j : ℕ)) ^ (j : ℕ) := by
    intro i y t; simp [hEW, eval₂_finsetSum, hevC, hQe, eval₂_pow]
  have hAsum : ∀ (v : σ → ℂ) r, A v r = ∑ i, v i * A (e i) r := by
    intro v r; rw [linear_apply_eq_sum A v]; simp [Finset.sum_apply, he]
  have hlsum : ∀ v : σ → ℂ, ℓ v = ∑ i, v i * ℓ (e i) := by
    intro v; rw [linear_apply_eq_sum ℓ v]; simp [he]

  have hrelA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ) := by
    filter_upwards [eventually_all.2 hrel] with z hz hzX i using hz i hzX
  have hWA : ∀ᶠ z in 𝓝 w, z ∈ Y → ∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0 := by
    filter_upwards [eventually_all.2 hWX] with z hz hzX i using hz i hzX
  have dEp := hdiv Ep (coeff_analyticAt hEpc) (by
    filter_upwards [hp] with z hz hzX; rw [hEpe]; exact hz hzX)
  have dEA := fun r => hdiv (EA r) (coeff_analyticAt (hEAc r)) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEAe, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i], hAsum z r, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEl := hdiv El (coeff_analyticAt hElc) (by
    filter_upwards [hrelA] with z hz hzX
    rw [hEle, Finset.sum_congr rfl fun i _ => by rw [← hz hzX i]]
    rw [hlsum z, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring)
  have dEW := fun i => hdiv (EW i) (coeff_analyticAt (hEWc i)) (by
    filter_upwards [hrelA, hWA] with z hz hzW hzX
    rw [hEWe, ← hz hzX i, cleared_eq, hzW hzX i, mul_zero])
  have dR := fun k => hdiv (R k) (hR k) (by
    filter_upwards [hRz k, hrelA, hWA, hVo.mem_nhds hwV] with z h1 hz hzW hzV hzX
    have hz0 : z ∈ {z | z ∈ V ∧ ∀ i, f i z = 0} := by rw [← hXV]; exact ⟨hzX, hzV⟩
    rw [← h1 (hzW hzX) (hz hzX), hz0.2 k, mul_zero])
  refine ⟨n, b, hb, hmX, ?_, ?_⟩
  · filter_upwards [hsep, dEp] with y hs hd hδy
    refine (hs hδy).of_dvd ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [hEp, Polynomial.map_add (f := _), Polynomial.map_sum, hevC] using hd
  intro U hU
  have hO : ∀ᶠ z in 𝓝 w, z ∈ U ∧ z ∈ V ∧ ∀ k, (∀ i, z i ^ nW i + ∑ j, cW i j (A z) * z i ^ (j : ℕ) = 0) →
      (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      δ (A z) ^ M k * f k z = (R k).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z) :=
    by filter_upwards [hU, hVo.mem_nhds hwV, eventually_all.2 hRz] with z h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hO
  have hnear := fun i => roots_near_centred (cW i) (A w) (w i) (fun j => (hcW i j).continuousAt) (hcW0 i) hε
  filter_upwards [eventually_all.2 hnear, eventually_all.2 dEA, dEl, eventually_all.2 dEW,
    eventually_all.2 dR] with y hny hAy hly hWy hRy hδy τ hτ
  set φ : σ → ℂ := fun i => (∑ j, q i j y * τ ^ (j : ℕ)) / δ y with hφ
  have hQφ : ∀ i, ∑ j, q i j y * τ ^ (j : ℕ) = δ y * φ i := fun i => by
    rw [hφ]; field_simp
  have hAφ : A φ = y := by
    funext r
    have h0 := eval₂_eq_zero_of_dvd (hAy r) hτ
    rw [hEAe, sub_eq_zero] at h0
    rw [hAsum φ r]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hlφ : ℓ φ = τ := by
    have h0 := eval₂_eq_zero_of_dvd hly hτ
    rw [hEle, sub_eq_zero] at h0
    rw [hlsum φ]
    apply mul_left_cancel₀ hδy
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hQφ i]; ring
  have hWφ : ∀ i, φ i ^ nW i + ∑ j, cW i j y * φ i ^ (j : ℕ) = 0 := by
    intro i
    have h0 := eval₂_eq_zero_of_dvd (hWy i) hτ
    rw [hEWe, hQφ i, cleared_eq] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδy)
  have hdist : dist φ w < ε := by
    rw [dist_pi_lt_iff hε]
    intro i
    rw [dist_eq_norm]
    exact hny i (φ i) (hWφ i)
  obtain ⟨hφU, hφV, hφR⟩ := hball hdist
  have hfk : ∀ k, f k φ = 0 := by
    intro k
    have h1 := hφR k (by rw [hAφ]; exact hWφ) (by intro i; rw [hAφ, hlφ, hQφ i])
    rw [hAφ, hlφ, eval₂_eq_zero_of_dvd (hRy k) hτ] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hδy)
  have hφX : φ ∈ Y ∩ V := by rw [hXV]; exact ⟨hφV, hfk⟩
  exact ⟨⟨hφX.1, hφU⟩, hAφ, hlφ⟩

end PrimitiveFormMinimalFactorPoints

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
