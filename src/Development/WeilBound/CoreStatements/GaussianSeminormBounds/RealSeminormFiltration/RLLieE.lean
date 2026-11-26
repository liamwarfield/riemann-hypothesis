module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieB
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieD
noncomputable section

open Filter Topology MeasureTheory

namespace PositivityTheory.RL.Delta

open Complex
open scoped Real ContDiff

theorem hadamard_lemma : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x := by
  intro n f hf h0
  have hD : ∀ v : Fin n → ℝ, ContDiff ℝ ∞ (fun w => fderiv ℝ f w v) := fun v =>
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hmean : ∀ h : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ h →
      ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∫ s in (0 : ℝ)..1, h (s • x)) := by
    intro h hh
    let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    have hk : IsCompact (Metric.closedBall (0 : ℝ) 2) := isCompact_closedBall _ _
    have hloc : MeasureTheory.LocallyIntegrable
        ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) MeasureTheory.volume :=
      (MeasureTheory.locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioc
    have hsm : ContDiffOn ℝ ∞ (Function.uncurry fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p))
        (Set.univ ×ˢ Set.univ) := by
      refine ContDiff.contDiffOn ?_
      exact (b.contDiff.comp contDiff_snd).smul (hh.comp (contDiff_snd.neg.smul contDiff_fst))
    have key := MeasureTheory.contDiffOn_convolution_right_with_param_comp (n := (⊤ : ℕ∞))
      (μ := MeasureTheory.volume) (ContinuousLinearMap.lsmul ℝ ℝ) (s := Set.univ)
      (v := fun _ : Fin n → ℝ => (0 : ℝ)) contDiffOn_const
      (g := fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p)) isOpen_univ hk
      (fun p t _ ht => by
        have : b t = 0 := image_eq_zero_of_notMem_tsupport (by rw [b.tsupport_eq]; exact ht)
        simp [this]) hloc hsm
    rw [contDiffOn_univ] at key
    convert key using 2 with x
    rw [MeasureTheory.convolution_def, intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have : b (-t) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, norm_neg, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2)
      simp [ht, this]
    · simp [ht]
  refine ⟨fun i x => ∫ s in (0 : ℝ)..1, fderiv ℝ f (s • x) (Pi.single i 1),
    fun i => hmean _ (hD _), fun x => ?_⟩
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (s • x) x) s := by
    intro s _
    have := (hd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
    rw [one_smul] at this
    exact this
  have hcv : ∀ v : Fin n → ℝ, Continuous (fun s : ℝ => fderiv ℝ f (s • x) v) := fun v =>
    (hD v).continuous.comp (continuous_id.smul continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcv x).intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, h0, sub_zero] at hftc
  rw [← hftc]
  have hx : ∀ s : ℝ, fderiv ℝ f (s • x) x =
      ∑ i, (x i : ℂ) * fderiv ℝ f (s • x) (Pi.single i 1) := by
    intro s
    calc fderiv ℝ f (s • x) x = fderiv ℝ f (s • x) (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) :=
          congrArg (fderiv ℝ f (s • x)) (pi_eq_sum_univ' x)
      _ = _ := by simp only [map_sum, map_smul, Complex.real_smul]
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · exact fun i _ => (continuous_const.mul (hcv _)).intervalIntegrable 0 1

theorem dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := by
  intro n f
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  set u : (Fin n → ℝ) → ℝ := (b : (Fin n → ℝ) → ℝ) - fun _ => 1 with hu
  have hus : ContDiff ℝ ∞ u := b.contDiff.sub contDiff_const
  have hub : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (b.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      ((b.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top))
    refine ⟨C + 1, by linarith [(norm_nonneg _).trans (hC 0)], fun x => ?_⟩
    rw [hu, iteratedFDeriv_sub b.contDiff contDiff_const]
    refine (norm_sub_le _ _).trans (add_le_add (hC x) ?_)
    by_cases hi : i = 0
    · subst hi; simp
    · rw [iteratedFDeriv_const_of_ne hi]; simp
  choose C hC0 hC using hub
  let L : ℕ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := fun R =>
    ((R : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ _
  have hL : ∀ R x, ‖L R x‖ = ‖x‖ / ((R : ℝ) + 1) := by
    intro R x
    show ‖((R : ℝ) + 1)⁻¹ • x‖ = _
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]
  have hL1 : ∀ R, ‖L R‖ ≤ 1 := fun R =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [hL, one_mul]
      exact div_le_self (norm_nonneg _) (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])
  have hsm : ∀ R, ContDiff ℝ ∞ (fun x => b (L R x) • f x) := fun R =>
    (b.contDiff.comp (L R).contDiff).smul (f.smooth ⊤)
  have hcs : ∀ R, HasCompactSupport (fun x => b (L R x) • f x) := by
    intro R
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * ((R : ℝ) + 1))) ?_
    intro x hx
    rw [mem_closedBall_zero_iff, not_le] at hx
    rw [b.zero_of_le_dist, zero_smul]
    rw [dist_zero_right, hL, le_div_iff₀ (by positivity)]
    exact hx.le
  refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun R : ℕ => (hcs R).toSchwartzMap (hsm R))
    ?_ (Filter.Eventually.of_forall hcs)
  rw [(schwartz_withSeminorms ℂ (Fin n → ℝ) ℂ).tendsto_nhds]
  rintro ⟨k, j⟩ ε hε
  set M : ℝ := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * C i * SchwartzMap.seminorm ℂ (k + 1) (j - i) f with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i)) (apply_nonneg _ _)
  have hlim : Filter.Tendsto (fun R : ℕ => M * (1 / ((R : ℝ) + 1))) Filter.atTop (nhds (M * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with R hR
  refine lt_of_le_of_lt ?_ hR
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine SchwartzMap.seminorm_le_bound ℂ k j _ (by positivity) fun x => ?_
  have e : (⇑((hcs R).toSchwartzMap (hsm R) - f) : (Fin n → ℝ) → ℂ) =
      fun x => (u ∘ L R) x • f x := by
    funext y
    show b (L R y) • f y - f y = (b (L R y) - 1) • f y
    rw [sub_smul, one_smul]
  rw [e]
  have hR0 : (0 : ℝ) < R + 1 := by positivity
  by_cases hx : ‖x‖ < R + 1
  · have hz : (fun x => (u ∘ L R) x • f x) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      have : b (L R y) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, hL]
        exact (div_le_one hR0).2 (le_of_lt hy))
      show (b (L R y) - 1) • f y = 0
      rw [this, sub_self, zero_smul]
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    positivity
  · rw [not_lt] at hx
    have h1 := norm_iteratedFDeriv_smul_le (hus.comp (L R).contDiff) (f.smooth ⊤) x (n := j)
      (by exact_mod_cast le_top)
    rw [mul_one_div, le_div_iff₀ hR0]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun x => (u ∘ L R) x • f x) x‖ * ((R : ℝ) + 1)
        ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖) * ‖x‖ := by
          gcongr
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ *
          (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (j - i) f x‖) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ M := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 : ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ ≤ C i := by
            rw [(L R).iteratedFDeriv_comp_right hus x (by exact_mod_cast le_top)]
            refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
            refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hC i _)
            exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL1 R)
          have h3 := SchwartzMap.le_seminorm ℂ (k + 1) (j - i) f x
          have h4 := hC0 i
          gcongr

theorem exists_quot : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t := by
  set E : ℂ → ℂ := fun z => cexp (2 * π * I * z) with hE
  have hEd : Differentiable ℂ E := by rw [hE]; fun_prop
  have hd : Differentiable ℂ (dslope E 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hEd.differentiableOn
  have hc : ContDiff ℝ ∞ (fun t : ℝ => dslope E 0 (t : ℂ)) :=
    (hd.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hmul : ∀ t : ℝ, (t : ℂ) * dslope E 0 t = cexp (2 * π * I * t) - 1 := by
    intro t
    have := sub_smul_dslope E 0 (t : ℂ)
    simpa [hE] using this
  have hne : ∀ t ∈ Metric.ball (0 : ℝ) 1, dslope E 0 (t : ℂ) ≠ 0 := by
    intro t ht h0
    by_cases h : t = 0
    · subst h
      have hD : HasDerivAt E (cexp (2 * π * I * 0) * (2 * π * I * 1)) 0 :=
        ((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).cexp
      rw [Complex.ofReal_zero, dslope_same, hD.deriv] at h0
      simp [Real.pi_ne_zero] at h0
    · have h1 := hmul t
      rw [h0, mul_zero, eq_comm, sub_eq_zero, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have h2 : (t : ℂ) = k := by
        have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ h3
        rw [hk]; ring
      have h4 : t = k := by exact_mod_cast h2
      rw [mem_ball_zero_iff, Real.norm_eq_abs, h4] at ht
      have h5 : |k| < 1 := by exact_mod_cast ht
      have h6 : k = 0 := Int.abs_lt_one_iff.1 h5
      exact h (by rw [h4, h6]; simp)
  refine ⟨fun t => (dslope E 0 (t : ℂ))⁻¹, hc.contDiffOn.inv hne, fun t ht => ?_⟩
  rw [← hmul t, mul_assoc, mul_inv_cancel₀ (hne t ht), mul_one]

theorem exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := by
  obtain ⟨q, hq, hq'⟩ := exists_quot
  obtain ⟨h, hh, hh'⟩ := hadamard_lemma n f (f.smooth ⊤) h0
  have hK : IsCompact (tsupport (f : (Fin n → ℝ) → ℂ)) :=
    (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (hf.trans Metric.ball_subset_closedBall)
  obtain ⟨r, hr, hr'⟩ := exists_lt_subset_ball (isClosed_tsupport _) hf
  set r' : ℝ := max r (1 / 2) with hr'def
  have hr1 : r' < 1 := max_lt hr (by norm_num)
  have hr0 : 0 < r' := lt_max_of_lt_right (by norm_num)
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨r', (r' + 1) / 2, hr0, by linarith⟩
  have hbs : tsupport (b : (Fin n → ℝ) → ℝ) ⊆ Metric.ball 0 1 := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by show (r' + 1) / 2 < 1; linarith)
  have hcoord : ∀ (i : Fin n), ∀ x ∈ Metric.ball (0 : Fin n → ℝ) 1, x i ∈ Metric.ball (0 : ℝ) 1 := by
    intro i x hx
    rw [mem_ball_zero_iff] at hx ⊢
    exact (norm_le_pi_norm x i).trans_lt hx
  have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) := by
    intro i
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_of_tsupport fun x hx => ?_
    rw [contMDiffAt_iff_contDiffAt]
    have hx' : x ∈ Metric.ball (0 : Fin n → ℝ) 1 := hbs (tsupport_smul_subset_left _ _ hx)
    refine b.contDiff.contDiffAt.smul (ContDiffAt.mul ?_ (hh i).contDiffAt)
    exact ContDiffAt.comp x (g := q) (f := fun x : Fin n → ℝ => x i)
      (hq.contDiffAt (Metric.isOpen_ball.mem_nhds (hcoord i x hx'))) (contDiffAt_apply ℝ (fun _ : Fin n => ℝ) i x)
  have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) :=
    fun i => b.hasCompactSupport.smul_right
  refine ⟨fun i => (hcs i).toSchwartzMap (hsm i), hcs, fun x => ?_⟩
  show f x = ∑ i, (cexp (2 * π * I * x i) - 1) * (b x • (q (x i) * h i x))
  have hb : f x = b x • f x := by
    by_cases hx : x ∈ tsupport (f : (Fin n → ℝ) → ℂ)
    · rw [b.one_of_mem_closedBall, one_smul]
      exact Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_max_left _ _) (hr' hx))
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  by_cases hx : x ∈ Metric.ball (0 : Fin n → ℝ) 1
  · rw [hb, hh' x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, ← mul_assoc, ← hq' _ (hcoord i x hx)]
  · have : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hbs h)
    rw [hb, this]; simp

theorem zero_of_ball (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]

theorem eq_delta (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (t : ℝ) (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * (t * x i : ℝ)) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * f 0 := by
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, HasCompactSupport (f : (Fin n → ℝ) → ℂ) → f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
    let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
    have he : ∀ x, e x = R • x := fun _ => rfl
    have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => e.injective (by rw [e.apply_symm_apply, he, smul_inv_smul₀ hR.ne'])
    have := zero_of_ball n (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      (fun i f g h => hχ R⁻¹ i _ _ fun x => by
        show g (e.symm x) = _ * f (e.symm x)
        rw [h, he']; simp) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ?_ (by
        show f (e 0) = 0
        rw [map_zero, h0])
    · rw [← this]
      exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.apply_symm_apply x).symm)
    · have hsub : Function.support (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ⊆ e ⁻¹' tsupport f :=
        fun x hx => subset_tsupport _ hx
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage e.continuous)).trans fun x hx => ?_
      have := hs hx
      rw [mem_ball_zero_iff, he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [mem_ball_zero_iff]
      exact (mul_lt_iff_lt_one_right hR).1 this
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨T ψ, fun f => ?_⟩
  let S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  have := hA (f - f 0 • ψ) (HasCompactSupport.sub hf (HasCompactSupport.smul_left (f := fun _ => f 0) h₁)) (by
    show f 0 - f 0 • ψ 0 = 0
    rw [hψ0]; simp)
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul, mul_comm] at this
  exact this

theorem eq_delta' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hχ : ∀ (l : V →ₗ[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * l x) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  obtain ⟨a, ha⟩ := eq_delta _ (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) fun t i f g h =>
    hχ (t • (LinearMap.proj i ∘ₗ e.toLinearEquiv.toLinearMap)) _ _ fun x => h (e x)
  refine ⟨a, fun f => ?_⟩
  have := ha (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f)
  refine Eq.trans ?_ (this.trans ?_)
  · exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.symm_apply_apply x).symm)
  · show a * f (e.symm 0) = _
    rw [map_zero]

end PositivityTheory.RL.Delta

end
end

noncomputable section

open scoped TensorProduct Matrix Classical RealInnerProductSpace Real SchwartzMap
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealWeil Complex

namespace PositivityTheory.RL.Up

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem trace_emb (a : F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F a) =
    (Algebra.trace ℚ F a : ℚ) := by
  classical
  rw [Algebra.trace_eq_matrix_trace (mixedEmbedding.latticeBasis F), Algebra.trace_eq_matrix_trace (integralBasis F), Matrix.trace,
    Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    mixedEmbedding.latticeBasis_apply, ← map_mul, mixedEmbedding.latticeBasis_repr_apply]

theorem trace_nondeg (l : κ → mixedEmbedding.mixedSpace F)
    (h : ∀ y, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (l ⬝ᵥ y) = 0) : l = 0 := by
  funext i
  refine (mixedEmbedding.latticeBasis F).ext_elem fun j => ?_
  have := h (Pi.single i (mixedEmbedding F ((integralBasis F).traceDual j)))
  rw [dotProduct_single, ← (mixedEmbedding.latticeBasis F).sum_repr (l i)] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, mixedEmbedding.latticeBasis_apply, ← map_mul, trace_emb,
    Module.Basis.trace_mul_traceDual] at this
  simpa [apply_ite] using this


variable (F κ) in
structure Co (l : Type) [Fintype l] where
  e1 : (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] EuclideanSpace ℝ l
  e2 : (κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] EuclideanSpace ℝ l
  pair : ∀ x y, ⟪e2 y, e1 x⟫ = -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i)

variable (F κ) in
theorem exists_co : ∃ n : ℕ, Nonempty (Co F κ (Fin n)) := by
  let e1 := toEuclidean (E := κ → mixedEmbedding.mixedSpace F)
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) :=
    (InnerProductSpace.toDual ℝ _).symm.toLinearEquiv.toLinearMap ∘ₗ
      ((ContinuousLinearMap.compL ℝ _ _ ℝ).flip (e1.symm : _ →L[ℝ] _)).toLinearMap ∘ₗ (-Fock.trB F κ)
  have hL : ∀ x y, ⟪L y, e1 x⟫ = -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := fun x y => by
    simp [L, Fock.trB_apply]
  have hi : Function.Injective L := (injective_iff_map_eq_zero _).2 fun y hy => trace_nondeg y fun x => by
    have := hL x y
    rw [hy, inner_zero_left, eq_comm, neg_eq_zero] at this
    rw [dotProduct_comm]
    exact this
  exact ⟨_, ⟨⟨e1, LinearEquiv.ofBijective L ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp)).1 hi⟩, hL⟩⟩⟩

theorem at_pt (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (SeminormBoundRestriction.pt y 0) := (SeminormBoundRestriction.at_iff _).2 fun _ => rfl

theorem evI_pt (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : (fun i => evI F (SeminormBoundRestriction.pt y z i)) = y :=
  funext fun i => RingEquiv.apply_symm_apply _ _

theorem realAd_one {M : Type} [AddCommGroup M] [Module (AF F) M] {a : M} (h : At (evI F) a) : realAd F 1 • a = a := by
  have := h (1 - realAd F 1) (by
    rw [← Fock.evIh_apply, map_sub, map_one, Fock.evIh_apply, Fock.evI_realAd, map_one, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero, eq_comm] at this

theorem pure_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem exists_adm (T : SInf F κ →L[ℂ] ℂ) : ∃ l ∈ (adeleClass F).adm κ, ∃ g ∈ SB (κ → Af F), ∀ f : SInf F κ,
    l (pureA F f g) = T f := by
  obtain ⟨g, hg, y, hy⟩ := SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
  let ι : SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  obtain ⟨r, hr⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  let l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := T.toLinearMap ∘ₗ r ∘ₗ LinearMap.funLeft ℂ ℂ fun a => SeminormBoundRestriction.pt a y
  have hl : ∀ (f : SInf F κ) g, l (pureA F f g) = g y • T f := fun f g => by
    have e : LinearMap.funLeft ℂ ℂ (fun a => SeminormBoundRestriction.pt a y) (pureA F f g) = ι (g y • f) := by
      funext a
      exact (SeminormBoundRestriction.pureA_pt _ _ _ _).trans (mul_comm _ _)
    show T (r _) = _
    rw [e, show r (ι (g y • f)) = g y • f from LinearMap.congr_fun hr _, map_smul]
  exact ⟨l, fun g _ => ⟨g y • T, fun f => hl f g⟩, g, hg, fun f => by rw [hl, hy, one_smul]⟩

namespace Co

variable {l : Type} [Fintype l] (c : Co F κ l)

def P : Sch l →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.e1

def P' : SInf F κ →L[ℂ] Sch l := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ c.e1.symm

theorem P_apply (f : Sch l) (x) : c.P f x = f (c.e1 x) := rfl

theorem P_P' (f : SInf F κ) : c.P (c.P' f) = f := SchwartzMap.ext fun x => congrArg f (c.e1.symm_apply_apply x)

theorem P'_P (f : Sch l) : c.P' (c.P f) = f := SchwartzMap.ext fun x => congrArg f (c.e1.apply_symm_apply x)

def vec (w : (κ → AF F) × (κ → AF F)) : l ⊕ l → ℝ :=
  Sum.elim (c.e1 fun i => evI F (w.1 i)) (c.e2 fun i => evI F (w.2 i))

theorem pPart_vec (w) : pPart (c.vec w) = c.e1 fun i => evI F (w.1 i) := rfl

theorem qPart_vec (w) : qPart (c.vec w) = c.e2 fun i => evI F (w.2 i) := rfl

theorem vec_ext {w w' : l ⊕ l → ℝ} (h1 : pPart w = pPart w') (h2 : qPart w = qPart w') : w = w' := by
  funext a
  rcases a with a | a
  · exact congrArg (fun v => v a) h1
  · exact congrArg (fun v => v a) h2

theorem vec_add (w w') : c.vec (w + w') = c.vec w + c.vec w' := by
  refine vec_ext ?_ ?_
  · rw [pPart_add, pPart_vec, pPart_vec, pPart_vec, ← map_add (f := _)]
    exact congrArg c.e1 (funext fun i => Fock.evI_add _ _)
  · rw [qPart_add, qPart_vec, qPart_vec, qPart_vec, ← map_add (f := _)]
    exact congrArg c.e2 (funext fun i => Fock.evI_add _ _)

theorem vec_smul (t : ℝ) (w) : c.vec (realAd F t • w) = t • c.vec w := by
  have e : ∀ a : AF F, evI F (realAd F t * a) = t • evI F a := fun a => by
    rw [Fock.evI_mul, Fock.evI_realAd, Algebra.smul_def]
  refine vec_ext ?_ ?_
  · rw [pPart_smul, pPart_vec, pPart_vec, ← map_smul]
    exact congrArg c.e1 (funext fun i => e _)
  · rw [qPart_smul, qPart_vec, qPart_vec, ← map_smul]
    exact congrArg c.e2 (funext fun i => e _)

theorem exists_vec (w : l ⊕ l → ℝ) : ∃ p : (κ → AF F) × (κ → AF F), At (evI F) p ∧ c.vec p = w := by
  refine ⟨(SeminormBoundRestriction.pt (c.e1.symm (pPart w)) 0, SeminormBoundRestriction.pt (c.e2.symm (qPart w)) 0),
    fun a ha => Prod.ext (at_pt _ a ha) (at_pt _ a ha), vec_ext ?_ ?_⟩
  · rw [pPart_vec, evI_pt, ContinuousLinearEquiv.apply_symm_apply]
  · rw [qPart_vec, evI_pt, LinearEquiv.apply_symm_apply]

theorem eq_zero_of_vec {p : (κ → AF F) × (κ → AF F)} (hp : At (evI F) p) (h : c.vec p = 0) : p = 0 := by
  have key : ∀ a : κ → AF F, At (evI F) a → (fun i => evI F (a i)) = 0 → a = 0 := fun a ha h0 => funext fun i =>
    Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i)) ((SeminormBoundRestriction.at_iff a).1 ha i)
  refine Prod.ext (key _ (fun a ha => congrArg Prod.fst (hp a ha)) ?_) (key _ (fun a ha => congrArg Prod.snd (hp a ha)) ?_)
  · exact c.e1.map_eq_zero_iff.1 (congrArg pPart h)
  · exact c.e2.map_eq_zero_iff.1 (congrArg qPart h)

theorem sympl_vec (w w') : sympl (c.vec w) (c.vec w') =
    -Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) := by
  rw [sympl, real_inner_comm, pPart_vec, qPart_vec, pPart_vec, qPart_vec, c.pair, c.pair, ← Fock.evIh_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sub, map_sum, map_mul, Fock.evIh_apply]
  ring

theorem schr_P {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)} (hw : At (evI F) w) (f : Sch l)
    (g : (κ → Af F) → ℂ) : schr ψ w (pureA F (c.P f) g) = pureA F (c.P (rhoS (c.vec w) f)) g := by
  have ha : At (evI F) w.1 := fun a ha => congrArg Prod.fst (hw a ha)
  have hb : At (evI F) w.2 := fun a ha => congrArg Prod.snd (hw a ha)
  have := Der.schr_pure hψ ha hb (c.P f) g 1
  rw [realAd_one ha, realAd_one hb] at this
  rw [this]
  congr 1
  funext x
  rw [P_apply, rhoS_apply, Der.hl, phase, real_inner_comm (qPart _), pPart_vec, qPart_vec, c.pair, c.pair, one_smul,
    P_apply, map_add, Der.linForm_apply, Der.linForm_apply]
  congr 2
  push_cast
  ring

theorem P_dRho (w : (κ → AF F) × (κ → AF F)) (f : Sch l) (x) : c.P (dRho (c.vec w) f) x =
    fderiv ℝ (c.P f) x (fun i => evI F (w.1 i)) - 2 * π * I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (w.2 i)) : ℝ) * c.P f x := by
  have : fderiv ℝ (c.P f) x = (fderiv ℝ f (c.e1 x)).comp (c.e1 : _ →L[ℝ] _) := c.e1.comp_right_fderiv
  rw [P_apply, dRho_apply, pPart_vec, qPart_vec, c.pair, this, P_apply]
  simp
  ring

theorem schur2 {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hadm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ) (ω : Sch l →L[ℂ] Sch l)
    (hfin : ∀ w : (κ → AF F) × (κ → AF F), pairA F 0 1 • w = w → ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ))
    (hinf : ∀ w, At (evI F) w → ∀ f, ∀ g ∈ SB (κ → Af F),
      T (pureA F (c.P (ω (rhoS (c.vec w) f))) g) = schr ψ w (T (pureA F (c.P (ω f)) g))) :
    ∃ z : ℂ, ∀ f, ∀ g ∈ SB (κ → Af F), T (pureA F (c.P (ω f)) g) = z • pureA F (c.P f) g := by
  letI := fun v : HeightOneSpectrum (𝓞 F) => GlobalTheory.LocalData.complRel v
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (0 : κ → AF F) ∘ₗ T
  have hl : L ∈ (adeleClass F).adm κ := hadm _ (SeminormBoundRestriction.eval_adm 0)
  let lf : SInf F κ → ((κ → Af F) → ℂ) →ₗ[ℂ] ℂ := fun f => L ∘ₗ
    { toFun := pureA F f
      map_add' := fun g g' => by funext x; simp [pureA, mul_add]
      map_smul' := fun a g => by funext x; simp [pureA, mul_left_comm] }
  have hfi : ∀ f, ∀ g ∈ SB (κ → Af F), g 0 = 0 → lf f g = 0 := fun f g hg h0 => by
    refine eq_zero_of_mul_invariant (lf f) (Set.range fun p : κ × Σ v, Fv F v => fun u =>
      GlobalTheory.VacAny.psiV ψ p.2.1 (evalV F p.2.1 (u p.1) * p.2.2)) ?_ ?_ hg ?_
    · rintro _ ⟨⟨i, v, c⟩, rfl⟩
      have := GlobalTheory.LocalData.isLocalField v
      have := nonarch_field (Fv F v)
      have h1 := isLocallyConstant_addChar _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v)
      exact h1.comp_continuous (((RestrictedProduct.continuous_eval v).comp (continuous_apply i)).mul continuous_const)
    · rintro _ ⟨⟨i, v, c⟩, rfl⟩ g hg
      let y : κ → AF F := Pi.single i (pairA F 0 (singleV F v c))
      have hy : pairA F 0 1 • ((0 : κ → AF F), y) = (0, y) := by
        refine Prod.ext (smul_zero _) (funext fun j => ?_)
        by_cases h : j = i
        · subst h
          simp only [y, Prod.smul_snd, Pi.smul_apply, Pi.single_eq_same]
          exact Prod.ext (mul_zero _) (one_mul _)
        · simp [y, h]
      have h2 := congrFun (hfin _ hy _ (pure_mem f hg)) 0
      refine Eq.trans (congrArg L (funext fun x => ?_)) (h2.trans (by simp [schr, lf, L]))
      have e : x i * pairA F 0 (singleV F v c) = pairA F 0 (singleV F v (evalV F v (x i).2 * c)) := by
        refine Prod.ext (mul_zero _) (af_ext fun u => ?_)
        show evalV F u ((x i).2 * singleFin v c) = evalV F u (singleFin v _)
        by_cases h : u = v
        · subst h; rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]
        · rw [map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]
      simp only [schr, y, dotProduct_single, e, Pi.zero_apply, zero_mul, mul_zero, add_zero]
      exact mul_left_comm (f _) (ψ _) (g _)
    · intro u hu
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (show u ≠ 0 from fun e => hu (e ▸ h0))
      obtain ⟨v, hv⟩ : ∃ v, evalV F v (u i) ≠ 0 := by
        by_contra h
        push Not at h
        exact hi (af_ext fun v => (h v).trans (map_zero _).symm)
      obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 (GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v)
      refine ⟨_, ⟨⟨i, v, y / evalV F v (u i)⟩, rfl⟩, ?_⟩
      show GlobalTheory.VacAny.psiV ψ v _ ≠ 1
      rwa [mul_div_cancel₀ _ hv]
  have hin : ∀ g ∈ SB (κ → Af F), ∃ a : ℂ, ∀ f, lf (c.P (ω f)) g = a * f 0 := fun g hg => by
    obtain ⟨T₀, hT₀⟩ := hl g hg
    obtain ⟨a, ha⟩ := Delta.eq_delta' (T₀ ∘L c.P ∘L ω) fun m f f' h => by
      let q : EuclideanSpace ℝ l := (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap m)
      let w : (κ → AF F) × (κ → AF F) := (0, SeminormBoundRestriction.pt (c.e2.symm q) 0)
      have hw : At (evI F) w := fun a ha => Prod.ext (smul_zero _) (at_pt _ a ha)
      have h1 : pPart (c.vec w) = 0 := by
        rw [pPart_vec, ← map_zero c.e1]
        exact congrArg c.e1 (funext fun i => Der.evI_zero)
      have h2 : qPart (c.vec w) = q := by rw [qPart_vec, evI_pt, LinearEquiv.apply_symm_apply]
      have e : f' = rhoS (c.vec w) f := by
        ext x
        rw [h, rhoS_apply, phase, h1, h2, add_zero]
        congr 2
        simp [q]
        ring
      show T₀ _ = T₀ _
      rw [← hT₀, ← hT₀, e]
      exact (congrFun (hinf w hw f g hg) 0).trans (by simp [schr, w, L])
    exact ⟨a, fun f => (hT₀ _).trans (ha f)⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ f, ∀ g ∈ SB (κ → Af F), lf (c.P (ω f)) g = a * (f 0 * g 0) := by
    by_cases h : ∃ g ∈ SB (κ → Af F), g 0 ≠ 0
    · obtain ⟨g₀, h0, h1⟩ := h
      obtain ⟨a, ha⟩ := hin g₀ h0
      refine ⟨a / g₀ 0, fun f g hg => ?_⟩
      have := hfi (c.P (ω f)) _ (sub_mem hg (Submodule.smul_mem _ (g 0 / g₀ 0) h0)) (by simp [h1])
      rw [map_sub, map_smul, sub_eq_zero, ha] at this
      rw [this, smul_eq_mul]; ring
    · push Not at h
      exact ⟨0, fun f g hg => by rw [hfi _ g hg (h g hg), zero_mul]⟩
  refine ⟨a, fun f g hg => funext fun x => ?_⟩
  let x1 : κ → AF F := SeminormBoundRestriction.pt (fun i => evI F (x i)) 0
  let x2 : κ → AF F := fun i => pairA F 0 (x i).2
  have hx : x1 + x2 = x := funext fun i => Prod.ext ((add_zero _).trans (RingEquiv.symm_apply_apply _ _)) (zero_add _)
  let g' : (κ → Af F) → ℂ := fun u => g (u + fun i => (x i).2)
  have hg' : g' ∈ SB (κ → Af F) :=
    ⟨hg.1.comp_continuous (continuous_add_const _), hg.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have e1 : ∀ f : SInf F κ, schr ψ (x2, 0) (pureA F f g) = pureA F f g' := fun f => by
    funext u
    simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
    exact congrArg₂ (· * ·) (congrArg f (funext fun i => congrArg _ (add_zero _))) rfl
  have h1 := hfin (x2, 0) (Prod.ext (funext fun i => Prod.ext (mul_zero _) (one_mul _)) (smul_zero _)) _
    (pure_mem (c.P (ω f)) hg)
  have h2 := congrFun (hinf (x1, 0) (fun a ha => Prod.ext (at_pt _ a ha) (smul_zero _)) f g' hg') 0
  rw [← e1 (c.P (ω f)), h1] at h2
  simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, zero_add, hx] at h2
  rw [← h2]
  refine (ha _ g' hg').trans ?_
  have h3 : qPart (c.vec (x1, 0)) = 0 := by
    rw [qPart_vec, ← map_zero c.e2]
    exact congrArg c.e2 (funext fun i => Der.evI_zero)
  rw [rhoS_apply, phase, h3, pPart_vec, evI_pt]
  simp [g', pureA, P_apply, evI]

end Co

end PositivityTheory.RL.Up

end
