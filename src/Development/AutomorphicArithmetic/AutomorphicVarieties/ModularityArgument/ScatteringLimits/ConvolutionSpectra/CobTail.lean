module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobTail
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem expAbs {c : ℝ} (hc : 0 < c) : Integrable fun y : ℝ => Real.exp (-c * |y|) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · exact (integrableOn_exp_mul_Iic hc 0).congr_fun (fun y hy => by simp only [abs_of_nonpos (mem_Iic.1 hy)]; ring_nf) measurableSet_Iic
  · exact (exp_neg_integrableOn_Ioi 0 hc).congr_fun (fun y hy => by simp only [abs_of_pos (mem_Ioi.1 hy)]) measurableSet_Ioi

private theorem wInt (p : L V) (hp : Tail p) : Integrable fun y => Real.exp (|y| / 2) * ‖p y‖ := by
  obtain ⟨C, hC⟩ := hp
  have ip : Integrable fun x => ‖p x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)
  have mp : Measurable fun x => ‖p x‖ ^ 2 := (Lp.stronglyMeasurable p).norm.measurable.pow_const 2
  have m2 : Measurable fun x => Real.exp (3 * |x| / 2) * ‖p x‖ ^ 2 :=
    (by fun_prop : Measurable fun x : ℝ => Real.exp (3 * |x| / 2)).mul mp
  have i2 : Integrable fun x => Real.exp (3 * |x| / 2) * ‖p x‖ ^ 2 := by
    refine ⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2 ?_⟩
    have b1 : ∀ᵐ x : ℝ, ENNReal.ofReal (Real.exp (3 * |x| / 2) * ‖p x‖ ^ 2) ≤ ∑' n : ℕ, (Icc (-(n : ℝ)) n)ᶜ.indicator
        (fun x => ENNReal.ofReal (Real.exp (3 * ((n : ℝ) + 1) / 2) * ‖p x‖ ^ 2)) x := by
      filter_upwards [compl_mem_ae_iff.2 (Real.volume_singleton (a := 0))] with x hx
      have h0 : 0 < |x| := abs_pos.2 hx
      have h1 : 1 ≤ ⌈|x|⌉₊ := Nat.one_le_ceil_iff.2 h0
      have h2 : ((⌈|x|⌉₊ - 1 : ℕ) : ℝ) = ⌈|x|⌉₊ - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
      refine le_trans ?_ (ENNReal.le_tsum (⌈|x|⌉₊ - 1))
      rw [indicator_of_mem (by
        intro h
        have := abs_le.2 h
        linarith [Nat.ceil_lt_add_one h0.le]), h2]
      gcongr
      linarith [Nat.le_ceil |x|]
    refine (lintegral_mono_ae b1).trans_lt ?_
    rw [lintegral_tsum fun n => (Measurable.indicator (by fun_prop) measurableSet_Icc.compl).aemeasurable]
    have b2 : ∀ n : ℕ, ∫⁻ x, (Icc (-(n : ℝ)) n)ᶜ.indicator
        (fun x => ENNReal.ofReal (Real.exp (3 * ((n : ℝ) + 1) / 2) * ‖p x‖ ^ 2)) x ≤
        ENNReal.ofReal (Real.exp (3 / 2) * C ^ 2 * Real.exp (-(1 / 2)) ^ n) := fun n => by
      rw [lintegral_indicator measurableSet_Icc.compl, ← ofReal_integral_eq_lintegral_ofReal (ip.const_mul _).integrableOn
        (Eventually.of_forall fun _ => by positivity), integral_const_mul,
        ← (cutLaws (V := V) _ univ measurableSet_Icc.compl .univ).2.2.2.2.2.2.2.2]
      refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hC n (Nat.cast_nonneg n)) 2) (Real.exp_pos _).le).trans_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add, mul_right_comm, ← Real.exp_add, mul_comm]
      congr 2; push_cast; ring
    refine (ENNReal.tsum_le_tsum b2).trans_lt ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      ((summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by norm_num))).mul_left _)]
    exact ENNReal.ofReal_lt_top
  refine (i2.add (expAbs (c := 1 / 2) (by norm_num))).mono'
    (((by fun_prop : Continuous fun y : ℝ => Real.exp (|y| / 2)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable _).norm)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
  have e1 : Real.exp (3 * |y| / 2) = Real.exp (3 * |y| / 4) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-(1 / 2) * |y|) = Real.exp (-|y| / 4) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (|y| / 2) = Real.exp (3 * |y| / 4) * Real.exp (-|y| / 4) := by rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2, e3]
  nlinarith [sq_nonneg (Real.exp (3 * |y| / 4) * ‖p y‖ - Real.exp (-|y| / 4)),
    mul_nonneg (mul_pos (Real.exp_pos (3 * |y| / 4)) (Real.exp_pos (-|y| / 4))).le (norm_nonneg (p y))]

private theorem aeInt (q : L V) (hq : Integrable (q : ℝ → V)) (a b : ℝ) :
    ∀ᵐ x : ℝ, (∫ s in Ioc a b, sh V (-s) q : L V) x = ∫ s in Ioc a b, q (x - s) := by
  have hI : Integrable (fun z : ℝ × ℝ => q (z.1 - z.2)) (volume.prod (volume.restrict (Ioc a b))) := by
    simpa using (integrable_const (μ := volume.restrict (Ioc a b)) (1 : ℝ)).convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hq
  have ii : IntegrableOn (fun s => sh V (-s) q) (Ioc a b) :=
    ((shF V).rev.cont q).integrableOn_Ioc
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hA => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hA.ne) (fun A _ _ => hI.integral_prod_left.integrableOn)
    fun A hm hA => ext_inner_left ℂ fun e => ?_
  have hA' : Integrable (fun z : ℝ × ℝ => q (z.1 - z.2)) ((volume.restrict A).prod (volume.restrict (Ioc a b))) := by
    rw [Measure.restrict_prod_eq_prod_univ]; exact hI.integrableOn
  rw [integral_integral_swap (f := fun x s => q (x - s)) hA', ← integral_inner hA'.integral_prod_right,
    ← L2.inner_indicatorConstLp_eq_inner_setIntegral ℂ hm hA.ne, ← integral_inner ii]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae ((sh_ae V (-s) q).mono fun x h => h.trans (congrArg q (sub_eq_add_neg x s).symm)))

private theorem cobOf (q : L V) (wq : Integrable fun y => Real.exp (|y| / 2) * ‖q y‖) (hq : Integrable (q : ℝ → V))
    (h0 : ∫ x, q x = 0) : (shF V).Cob q := by
  set D := ∫ y, Real.exp (|y| / 2) * ‖q y‖
  have hb : ∀ (x : ℝ) (S : Set ℝ), MeasurableSet S → (∀ y ∈ S, |x| ≤ |y|) → ‖∫ y in S, q y‖ ≤ D * Real.exp (-(1 / 2) * |x|) := by
    intro x S hS h
    refine (norm_integral_le_of_norm_le (wq.mul_const (Real.exp (-(1 / 2) * |x|))).integrableOn ?_).trans ?_
    · refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun y hy => ?_)
      rw [mul_right_comm, ← Real.exp_add]
      exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by linarith [h y hy]))
    · rw [← integral_mul_const]
      exact setIntegral_le_integral (wq.mul_const _) (Eventually.of_forall fun _ => by positivity)
  let k : ℝ → V := fun x => ∫ y in Iic x, q y
  have hk : ∀ x y, k y - k x = ∫ s in x..y, q s := fun x y =>
    intervalIntegral.integral_Iic_sub_Iic hq.integrableOn hq.integrableOn
  have kb : ∀ x, ‖k x‖ ≤ D * Real.exp (-(1 / 2) * |x|) := fun x => by
    rcases le_total x 0 with h | h
    · exact hb x _ measurableSet_Iic fun y hy => by
        rw [abs_of_nonpos h, abs_of_nonpos (le_trans hy h)]; exact neg_le_neg hy
    · have := intervalIntegral.integral_Iic_add_Ioi (b := x) hq.integrableOn hq.integrableOn
      rw [h0] at this
      rw [show k x = -∫ y in Ioi x, q y from eq_neg_of_add_eq_zero_left this, norm_neg]
      exact hb x _ measurableSet_Ioi fun y hy => by
        rw [abs_of_nonneg h]; exact (le_of_lt hy).trans (le_abs_self y)
  have kc : Continuous k := by
    have : k = fun y => k 0 + ∫ s in (0 : ℝ)..y, q s := funext fun y => by rw [← hk]; abel
    rw [this]
    exact continuous_const.add (hq.continuous_primitive 0)
  have km : MemLp k 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm kc.aestronglyMeasurable).2 ?_
    refine ((expAbs one_pos).const_mul (D ^ 2)).mono' (kc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    refine (pow_le_pow_left₀ (norm_nonneg _) (kb x) 2).trans_eq ?_
    rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  refine ⟨km.toLp k, fun t => ?_⟩
  show ∫ s in (0 : ℝ)..t, sh V s q = sh V t (km.toLp k) - km.toLp k
  have e1 : ∫ s in (0 : ℝ)..t, sh V s q = ∫ s in (-t)..0, sh V (-s) q := by
    rw [intervalIntegral.integral_comp_neg fun s => sh V s q]; simp
  rw [e1, intervalIntegral]
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (∫ s in Ioc (-t) 0, sh V (-s) q) (∫ s in Ioc 0 (-t), sh V (-s) q), aeInt q hq (-t) 0, aeInt q hq 0 (-t),
    Lp.coeFn_sub (sh V t (km.toLp k)) (km.toLp k), sh_ae V t (km.toLp k), km.coeFn_toLp,
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae km.coeFn_toLp] with x h1 h2 h3 h4 h5 h6 h7
  rw [h1, h4, Pi.sub_apply, Pi.sub_apply, h2, h3, h5, h6, h7, hk]
  show ∫ s in (-t)..0, q (x - s) = _
  rw [intervalIntegral.integral_comp_sub_left fun s => q s]; simp
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.cobTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (p : L V), (Bdd p → Tail p) ∧ (Tail p → Integrable (p : ℝ → V) ∧ (shF V).Cob (p - one V (∫ x, p x))) := by
  intro V _ _ _ _ p
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  have bt : ∀ p : L V, Bdd p → Tail p := by
    rintro p ⟨ρ₀, h⟩
    refine ⟨Real.exp ρ₀ * ‖p‖, fun ρ hρ => ?_⟩
    by_cases a : ρ₀ ≤ ρ
    · have h2 := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Icc (-ρ₀) ρ₀) measurableSet_Icc.compl measurableSet_Icc).1 p
      rw [ContinuousLinearMap.comp_apply, h, (disjoint_compl_left_iff_subset.2 (Icc_subset_Icc (by linarith) a)).inter_eq,
        (cl univ univ .univ .univ).2.2.2.2.1] at h2
      rw [h2]; simp only [ContinuousLinearMap.zero_apply, norm_zero]; positivity
    · refine ((cl _ univ measurableSet_Icc.compl .univ).2.2.2.2.2.1 _).trans ?_
      rw [mul_right_comm, ← Real.exp_add]
      exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by linarith [not_le.1 a]))
  refine ⟨bt p, fun hp => ?_⟩
  have wp := wInt p hp
  have toI : ∀ q : L V, Integrable (fun y => Real.exp (|y| / 2) * ‖q y‖) → Integrable (q : ℝ → V) := fun q h =>
    h.mono' (Lp.aestronglyMeasurable q) (Eventually.of_forall fun y =>
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity)))
  refine ⟨toI p wp, ?_⟩
  obtain ⟨-, o2, o3⟩ := (svSpec (V := V)).2 (∫ x, p x)
  have wo := wInt _ (bt _ o2)
  have hq := Lp.coeFn_sub p (one V (∫ x, p x))
  have h0 : ∫ x, (p - one V (∫ x, p x) : L V) x = 0 := by
    rw [integral_congr_ae hq, integral_sub' (toI p wp) (toI _ wo), o3, sub_self]
  have wq : Integrable fun y => Real.exp (|y| / 2) * ‖(p - one V (∫ x, p x) : L V) y‖ := by
    refine (wp.add wo).mono' (((by fun_prop : Continuous fun y : ℝ => Real.exp (|y| / 2)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable _).norm) ?_
    filter_upwards [hq] with y hy
    rw [Real.norm_of_nonneg (by positivity), hy, Pi.add_apply, ← mul_add]
    gcongr
    exact norm_sub_le _ _
  exact cobOf _ wq (toI _ wq) h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ShNull
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.shNull :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V], (shF V).Null := by
  intro V _ _ _ _
  have top : ∀ u u' : L V, Tendsto (fun t => ⟪u', sh V t u⟫_ℂ) atTop (𝓝 0) := by
    intro u u'
    have hi : Integrable fun x => ‖u' x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u')).1 (Lp.memLp u')
    have h1 := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖u' x‖ ^ 2) (s := fun T : ℝ => Iic (-T))
      (fun _ => measurableSet_Iic) (fun x y h => Iic_subset_Iic.2 (by linarith)) ⟨0, hi.integrableOn⟩
    have he : ⋂ T : ℝ, Iic (-T) = ∅ := eq_empty_of_forall_notMem fun x hx => by
      have := mem_iInter.1 hx (1 - x)
      simp at this; linarith
    rw [he, setIntegral_empty] at h1
    have h2 : Tendsto (fun T : ℝ => ‖cut V (Iic (-T)) u'‖ * ‖u‖) atTop (𝓝 0) := by
      have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).mul_const ‖u‖
      rw [Real.sqrt_zero, zero_mul] at h2
      refine h2.congr fun T => ?_
      rw [Function.comp_apply, ← (cutLaws (V := V) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2 u', Real.sqrt_sq (norm_nonneg _)]
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨T, hT⟩ := (h2.eventually (gt_mem_nhds (half_pos hε))).exists
    have h3 : Tendsto (fun t => ‖⟪u', cut V (Ioi (-T)) (sh V t u)⟫_ℂ‖) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := u')).inner (𝕜 := ℂ) ((cutLim u).1 (-T))).norm
    filter_upwards [h3.eventually (gt_mem_nhds (half_pos hε))] with t ht
    obtain ⟨-, c2, c3, c4, -⟩ := cutLaws (V := V) (Iic (-T)) (Ioi (-T)) measurableSet_Iic measurableSet_Ioi
    have h4 := c3 (Iic_disjoint_Ioi le_rfl)
    rw [Iic_union_Ioi, c4] at h4
    have h5 : sh V t u = cut V (Iic (-T)) (sh V t u) + cut V (Ioi (-T)) (sh V t u) := DFunLike.congr_fun h4 _
    rw [h5, inner_add_right, ← c2.isSymmetric.apply_clm]
    refine (norm_add_le _ _).trans_lt ?_
    have h6 := norm_inner_le_norm (𝕜 := ℂ) (cut V (Iic (-T)) u') (sh V t u)
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u] at h6
    linarith
  refine fun u u' => ⟨top u u', ?_⟩
  have h1 := (Complex.continuous_conj.tendsto 0).comp ((top u' u).comp tendsto_neg_atBot_atTop)
  rw [map_zero] at h1
  refine h1.congr fun t => ?_
  have hin := (⟨(sh V t : L V →ₗ[ℂ] L V), (shF V).norm t⟩ : L V →ₗᵢ[ℂ] L V).inner_map_map (sh V (-t) u') u
  have e : sh V t (sh V (-t) u') = u' := by
    have := (shF V).add t (-t) u'
    rw [add_neg_cancel, (shF V).zero] at this
    exact this.symm
  simp only [Function.comp_apply, inner_conj_symm]
  rw [← hin]
  show ⟪sh V t (sh V (-t) u'), sh V t u⟫_ℂ = _
  rw [e]; rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NIso
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Grow
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem tr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (e : V) (t : ℝ) :
    ‖∫ s in (0 : ℝ)..t, sh V s (one V e)‖ = ‖∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1)‖ * ‖e‖ := by
  let T : L ℂ →L[ℂ] L V := (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume
  have hT : ∀ u : L ℂ, ∀ᵐ x : ℝ, T u x = u x • e := fun u =>
    ((ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLpL u).mono fun x h => by rw [h]; simp
  have nsq : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u : L V), ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  have hn : ∀ u, ‖T u‖ = ‖u‖ * ‖e‖ := fun u => by
    refine (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, nsq, nsq, ← integral_mul_const]
    exact integral_congr_ae ((hT u).mono fun x h => by simp only [h, norm_smul, mul_pow])
  have hs : ∀ s, T (sh ℂ s (one ℂ 1)) = sh V s (one V e) := fun s => Lp.ext (by
    have q := (measurePreserving_add_right (volume : Measure ℝ) s).quasiMeasurePreserving
    filter_upwards [hT (sh ℂ s (one ℂ 1)), sh_ae ℂ s (one ℂ 1), sh_ae V s (one V e), q.ae ((svSpec (V := ℂ)).2 1).1,
      q.ae ((svSpec (V := V)).2 e).1] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4, h5]
    by_cases b : x + s ∈ Ioc (0 : ℝ) 1 <;> simp [b])
  have ii : IntervalIntegrable (fun s => sh ℂ s (one ℂ 1)) volume 0 t := ((shF ℂ).cont _).intervalIntegrable _ _
  rw [← hn, ← T.intervalIntegral_comp_comm ii]
  exact congrArg _ (intervalIntegral.integral_congr fun s _ => (hs s).symm)

theorem UpperTheory.V.Z.IntegralApplyAeEq.grow :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W], ∃ g : ℝ → ℝ, Tendsto g atTop atTop ∧ (∀ (e : V) (t : ℝ), ‖∫ s in (0 : ℝ)..t, sh V s (one V e)‖ = g t * ‖e‖) ∧
      ∀ (f : W) (t : ℝ), ‖∫ s in (0 : ℝ)..t, sh W (-s) (one W f)‖ = g t * ‖f‖ := by
  intro V _ _ _ _ W _ _ _ _
  refine ⟨fun t => ‖∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1)‖, ?_, fun e t => tr e t, fun f t => ?_⟩
  · refine tendsto_atTop_mono' _ ?_ (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hf : volume (Ioc (-t) 1) ≠ ⊤ := by simp
    obtain ⟨o1, -, o3⟩ := (svSpec (V := ℂ)).2 1
    have h1 : ⟪indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ), ∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1)⟫_ℂ = t := by
      have := (innerSL ℂ (indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ))).intervalIntegral_comp_comm
        (((shF ℂ).cont (one ℂ 1)).intervalIntegrable (μ := volume) 0 t)
      simp only [innerSL_apply_apply] at this
      refine this.symm.trans ((intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) fun s hs => ?_).trans (by simp))
      rw [uIcc_of_le ht] at hs
      show ⟪indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ), sh ℂ s (one ℂ 1)⟫_ℂ = 1
      rw [L2.inner_indicatorConstLp_one, setIntegral_eq_integral_of_ae_compl_eq_zero, integral_congr_ae (sh_ae ℂ s _),
        integral_add_right_eq_self, o3]
      filter_upwards [sh_ae ℂ s (one ℂ 1), (measurePreserving_add_right volume s).quasiMeasurePreserving.ae o1] with x h1 h2 hx
      rw [h1, h2, indicator_of_notMem fun b => hx ⟨by linarith [b.1, hs.2], by linarith [b.2, hs.1]⟩]
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ)) (∫ s in (0 : ℝ)..t, sh ℂ s (one ℂ 1))
    have h3 : ‖indicatorConstLp 2 measurableSet_Ioc hf (1 : ℂ)‖ ^ 2 = t + 1 := by
      rw [norm_indicatorConstLp (by simp) (by simp), Real.volume_real_Ioc_of_le (by linarith), norm_one, one_mul,
        ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      simp [add_comm]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg ht] at h2
    have h4 := pow_le_pow_left₀ ht h2 2
    rw [mul_pow, h3] at h4
    refine Real.sqrt_le_iff.2 ⟨norm_nonneg _, ?_⟩
    show t + -1 ≤ _
    refine le_of_mul_le_mul_left (le_trans ?_ h4) (by linarith)
    nlinarith
  · have ii : IntervalIntegrable (fun s => sh W s (one W f)) volume 0 t := ((shF W).cont _).intervalIntegrable _ _
    have n1 : ∀ x, ‖sh W (-t) x‖ = ‖x‖ := (shF W).norm (-t)
    rw [← tr f t, ← n1 (∫ s in (0 : ℝ)..t, sh W s (one W f)), ← (sh W (-t)).intervalIntegral_comp_comm ii]
    congr 1
    have e : ∀ s, sh W (-t) (sh W s (one W f)) = sh W (s - t) (one W f) := fun s => by
      rw [← neg_add_eq_sub]; exact ((shF W).add _ _ _).symm
    simp only [e]
    rw [intervalIntegral.integral_comp_neg fun s => sh W s (one W f), intervalIntegral.integral_comp_sub_right fun s => sh W s (one W f)]
    simp
end

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nIso :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), (∀ e, M.F.Cob (M.J (one V e)) → e = 0) ∧ ∀ N, M.IsN N → ∀ w, ‖N w‖ = ‖w‖ := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M
  obtain ⟨g, hg, g1, g2⟩ := grow (V := V) (W := W)
  have hb := (cobLaws M.F).2.2.2.2.2.1
  have e1 : ∀ (e : V) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J (one V e))‖ = g t * ‖e‖ := fun e t => by
    simp only [M.hJ]
    rw [← g1, ← M.J.norm_map]
    exact congrArg _ ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).intervalIntegral_comp_comm
      (((shF V).cont _).intervalIntegrable _ _))
  have e2 : ∀ (f : W) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J' (one W f))‖ = g t * ‖f‖ := fun f t => by
    simp only [M.hJ']
    rw [← g2, ← M.J'.norm_map]
    exact congrArg _ ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).intervalIntegral_comp_comm
      (((shF W).rev.cont _).intervalIntegrable _ _))
  have key : ∀ d C : ℝ, (∀ t, |g t * d| ≤ C) → d = 0 := fun d C h => by
    by_contra hd
    have h1 : Tendsto (fun t => |g t| * |d|) atTop atTop := (tendsto_abs_atTop_atTop.comp hg).atTop_mul_const (abs_pos.2 hd)
    obtain ⟨t, ht⟩ := (h1.eventually_gt_atTop C).exists
    exact absurd (abs_mul (g t) d ▸ h t) (not_le.2 ht)
  refine ⟨fun e he => ?_, fun N hN w => ?_⟩
  · obtain ⟨C, hC⟩ := hb _ he
    exact norm_eq_zero.1 (key _ C fun t => by rw [← e1, abs_norm]; exact hC t)
  · obtain ⟨C, hC⟩ := hb _ (hN w)
    refine (sub_eq_zero.1 (key (‖w‖ - ‖N w‖) C fun t => ?_)).symm
    rw [mul_sub, ← e1, ← e2]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← intervalIntegral.integral_sub ((M.F.cont _).intervalIntegrable _ _) ((M.F.cont _).intervalIntegrable _ _)]
    simpa only [map_sub] using hC t
end
