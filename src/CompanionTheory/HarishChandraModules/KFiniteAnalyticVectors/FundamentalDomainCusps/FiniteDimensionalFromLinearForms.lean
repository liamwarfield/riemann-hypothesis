module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.IntegrableMulBc
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal

noncomputable section

namespace CompanionTheory.D.gk.RF

theorem idemZero : IdemZero := by
  intro A _ Q hc hq ht
  have key : ∀ s, ‖Q s‖ < 1 → Q s = 0 := fun s h => by
    have h1 : ‖Q s‖ ≤ ‖Q s‖ * ‖Q s‖ := by conv_lhs => rw [← hq s]
                                          exact norm_mul_le _ _
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (Q s)])
  have hcl : IsClopen {s | Q s = 0} := ⟨isClosed_eq hc continuous_const, by
    have : {s | Q s = 0} = {s | ‖Q s‖ < 1} := Set.ext fun s => ⟨fun h => by simp [show Q s = 0 from h], key s⟩
    rw [this]; exact isOpen_lt hc.norm continuous_const⟩
  obtain ⟨s₀, hs₀⟩ := ((tendsto_zero_iff_norm_tendsto_zero.1 ht).eventually (gt_mem_nhds one_pos)).exists
  intro s
  exact (hcl.eq_univ ⟨s₀, key s₀ hs₀⟩).ge (Set.mem_univ s)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

theorem tendsto_transl {φ : G → ℂ} (hφ : Integrable φ μ) :
    Tendsto (fun u => ∫ y, ‖φ y - φ (u * y)‖ ∂μ) (𝓝 1) (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let f : Lp ℂ 1 μ := hφ.toL1 φ
  have hc : Continuous fun u : G => DomMulAct.mk u • f := (DomMulAct.continuous_mk).smul continuous_const
  have h1 : Tendsto (fun u : G => ‖f - DomMulAct.mk u • f‖) (𝓝 1) (𝓝 0) := by
    have := (continuous_const.sub hc (f := fun _ => f)).norm.tendsto 1
    simpa using this
  refine h1.congr fun u => ?_
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have h2 := (measurePreserving_mul_left μ u).quasiMeasurePreserving.ae hφ.coeFn_toL1
  filter_upwards [Lp.coeFn_sub f (DomMulAct.mk u • f), DomMulAct.smul_Lp_ae_eq (DomMulAct.mk u) f, hφ.coeFn_toL1, h2]
    with y a b c d
  rw [a, Pi.sub_apply, b, c]
  simp only [Equiv.symm_apply_apply, smul_eq_mul]
  rw [d]

def eI (r : ℝ) : ℂ := Complex.exp ((r : ℂ) * Complex.I)

theorem norm_eI (r : ℝ) : ‖eI r‖ = 1 := Complex.norm_exp_ofReal_mul_I r

theorem eI_add (r r' : ℝ) : eI (r + r') = eI r * eI r' := by
  simp only [eI, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem continuous_eI : Continuous eI := by unfold eI; fun_prop

theorem norm_eI_sub (r r' : ℝ) : ‖eI r - eI r'‖ ≤ min 2 |r - r'| := by
  refine le_min ((norm_sub_le _ _).trans (by rw [norm_eI, norm_eI]; norm_num)) ?_
  have : eI r - eI r' = (eI (r - r') - 1) * eI r' := by rw [sub_mul, ← eI_add, sub_add_cancel, one_mul]
  rw [this, norm_mul, norm_eI, mul_one, eI, mul_comm]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem integrable_mul_bc {φ : G → ℂ} (hφ : Integrable φ μ) {F : G → ℂ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ y, ‖F y‖ ≤ M) : Integrable (fun y => φ y * F y) μ :=
  hφ.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hM)

theorem reprod {φ : G → ℂ} (hφ : Integrable φ μ) (hi : ∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) {F : G → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ y, ‖F y‖ ≤ M) :
    ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ = ∫ w, φ w * F w ∂μ :=
  _root_.Bl.FirstLemmaL.goal1 hφ hi hF hM

end

theorem selTw : SelTw := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P
  let X : Submodule ℂ (G →ᵇ ℂ) :=
    { carrier := {F | (∀ m ∈ N, ∀ x, F (m * x) = F x) ∧ ∀ t x, F (a t * x) = F x}
      add_mem' := fun h h' => ⟨fun m hm x => by simp [h.1 m hm, h'.1 m hm], fun t x => by simp [h.2, h'.2]⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
      smul_mem' := fun c _ h => ⟨fun m hm x => by simp [h.1 m hm], fun t x => by simp [h.2]⟩ }
  let k : ℝ → (G →ᵇ ℂ) → G → G → ℂ := fun s F x y => F (x * y) * eI (s * (Ht (x * y) - Ht x))
  have kc : ∀ s F, Continuous fun p : G × G => k s F p.1 p.2 := fun s F =>
    (F.continuous.comp continuous_mul).mul (continuous_eI.comp (continuous_const.mul
      ((P.hcont.comp continuous_mul).sub (P.hcont.comp continuous_fst))))
  have kb : ∀ s F x y, ‖k s F x y‖ ≤ ‖F‖ := fun s F x y => by
    simp only [k, norm_mul, norm_eI, mul_one]; exact F.norm_coe_le_norm _
  have ki : ∀ s F x, Integrable (fun y => φ y * k s F x y) μ := fun s F x =>
    integrable_mul_bc hφ ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)
  let q : ℝ → (G →ᵇ ℂ) → G → ℂ := fun s F x => ∫ y, φ y * k s F x y ∂μ
  have qb : ∀ s F x, ‖q s F x‖ ≤ (∫ y, ‖φ y‖ ∂μ) * ‖F‖ := fun s F x => by
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le (hφ.norm.mul_const _) (Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
  have qc : ∀ s F, Continuous (q s F) := fun s F =>
    continuous_of_dominated (bound := fun y => ‖φ y‖ * ‖F‖) (fun x => (ki s F x).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
      (hφ.norm.mul_const _) (Eventually.of_forall fun y =>
        continuous_const.mul ((kc s F).comp (continuous_id.prodMk continuous_const)))
  let Ql : ℝ → (X →ₗ[ℂ] X) := fun s =>
    { toFun := fun F => ⟨ofNormedAddCommGroup (q s F) (qc s F) _ (qb s F), fun m hm x => by
          show q s F (m * x) = q s F x
          simp only [q, k, mul_assoc m, F.2.1 m hm, P.hN m hm], fun t x => by
          show q s F (a t * x) = q s F x
          simp only [q, k, mul_assoc (a t), F.2.2, P.ha, add_sub_add_left_eq_sub]⟩
      map_add' := fun F F' => Subtype.ext (BoundedContinuousFunction.ext fun x => by
        show q s (F + F') x = q s F x + q s F' x
        rw [← integral_add (ki s F x) (ki s F' x)]
        simp only [q, k, BoundedContinuousFunction.add_apply, add_mul, mul_add])
      map_smul' := fun c F => Subtype.ext (BoundedContinuousFunction.ext fun x => by
        show q s (c • (F : G →ᵇ ℂ)) x = c * q s F x
        rw [← integral_const_mul]
        simp only [q, k, BoundedContinuousFunction.smul_apply, smul_eq_mul]
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)) }
  have hφ0 : 0 ≤ ∫ y, ‖φ y‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  let Q : ℝ → (X →L[ℂ] X) := fun s => (Ql s).mkContinuous (∫ y, ‖φ y‖ ∂μ) fun F =>
    (BoundedContinuousFunction.norm_le (mul_nonneg hφ0 (norm_nonneg _))).2 (qb s F)
  have Qa : ∀ s (F : X) x, (Q s F : G →ᵇ ℂ) x = q s F x := fun _ _ _ => rfl
  have Qn : ∀ (T : X →L[ℂ] X) (d : ℝ), 0 ≤ d → (∀ (F : X) x, ‖(T F : G →ᵇ ℂ) x‖ ≤ d * ‖(F : G →ᵇ ℂ)‖) → ‖T‖ ≤ d :=
    fun T d hd h => T.opNorm_le_bound hd fun F =>
      (BoundedContinuousFunction.norm_le (mul_nonneg hd (norm_nonneg _))).2 (h F)
  obtain ⟨c, hcc, hc⟩ := P.bd
  have hQc : Continuous Q := by
    refine continuous_iff_continuousAt.2 fun s₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hI : ∀ s, Integrable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ → True := fun _ _ => trivial
    have hc0 : ∀ y, 0 ≤ c y := fun y => (abs_nonneg _).trans (hc 1 y)
    have hb : ∀ s y, ‖‖φ y‖ * min 2 (|s - s₀| * c y)‖ ≤ ‖φ y‖ * 2 := fun s y => by
      rw [norm_mul, norm_norm, Real.norm_of_nonneg (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (norm_nonneg _)
    have hm : ∀ s, AEStronglyMeasurable (fun y => ‖φ y‖ * min 2 (|s - s₀| * c y)) μ := fun s =>
      hφ.norm.aestronglyMeasurable.mul (continuous_const.min (continuous_const.mul hcc)).aestronglyMeasurable
    have hd : Continuous fun s => ∫ y, ‖φ y‖ * min 2 (|s - s₀| * c y) ∂μ :=
      continuous_of_dominated hm (fun s => Eventually.of_forall (hb s)) (hφ.norm.mul_const 2)
        (Eventually.of_forall fun y => by fun_prop)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => Qn _ _ (integral_nonneg fun y =>
      mul_nonneg (norm_nonneg _) (le_min zero_le_two (mul_nonneg (abs_nonneg _) (hc0 y)))) fun F x => ?_)
      (by simpa using hd.tendsto s₀)
    show ‖q s F x - q s₀ F x‖ ≤ _
    rw [← integral_sub (ki s F x) (ki s₀ F x), ← integral_mul_const]
    refine norm_integral_le_of_norm_le
      (((hφ.norm.mul_const 2).mono' (hm s) (Eventually.of_forall (hb s))).mul_const _) (Eventually.of_forall fun y => ?_)
    simp only [k]
    rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, mul_assoc, mul_comm (min _ _)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul ((F : G →ᵇ ℂ).norm_coe_le_norm _) ((norm_eI_sub _ _).trans
      (min_le_min le_rfl ?_)) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hc x y) (abs_nonneg _)
  have hQi : ∀ s, Q s * Q s = Q s := fun s => ContinuousLinearMap.ext fun F => Subtype.ext
    (BoundedContinuousFunction.ext fun x => by
      show ∫ y, φ y * (q s F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = q s F x
      refine Eq.trans ?_ (reprod hφ hi ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x))
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [q, k, Function.comp_apply]
      rw [← integral_mul_const]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [mul_assoc, ← eI_add]
      congr 3
      ring)
  have hQt : Tendsto Q atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 fun e he => ?_
    obtain ⟨τ, hτ, hU⟩ := P.small _ ((tendsto_transl hφ).eventually (gt_mem_nhds he))
    refine ⟨Real.pi / τ + 1, fun s hs => ?_⟩
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
    rw [dist_zero_right]
    refine (Qn _ (e / 2) (by positivity) fun F x => ?_).trans_lt (half_lt_self he)
    obtain ⟨m, hm, hu⟩ := hU (Real.pi / s) (by
      rw [abs_of_pos (by positivity), div_lt_iff₀ hs0, ← div_lt_iff₀' hτ]; linarith) x
    set u := x⁻¹ * (m * a (Real.pi / s)) * x with hu'
    have h1 : ∀ y, k s F x (u * y) = -k s F x y := fun y => by
      have e1 : x * (u * y) = m * (a (Real.pi / s) * (x * y)) := by rw [hu']; group
      simp only [k, e1, F.2.1 m hm, F.2.2, P.hN m hm, P.ha]
      rw [add_sub_assoc, mul_add, eI_add, mul_div_cancel₀ _ hs0.ne']
      simp [eI]
    have h2 : q s F x = -∫ y, φ (u * y) * k s F x y ∂μ := by
      rw [← integral_neg]
      refine (integral_mul_left_eq_self (fun y => φ y * k s F x y) u).symm.trans ?_
      simp only [h1, mul_neg]
    have hi2 : Integrable (fun y => φ (u * y) * k s F x y) μ :=
      integrable_mul_bc (hφ.comp_mul_left u) ((kc s F).comp (continuous_const.prodMk continuous_id)) (kb s F x)
    have h3 : 2 * q s F x = ∫ y, (φ y - φ (u * y)) * k s F x y ∂μ := by
      simp only [sub_mul]
      rw [integral_sub (ki s F x) hi2, two_mul]
      nth_rewrite 2 [h2]
      rfl
    have h4 : ‖2 * q s F x‖ ≤ (∫ y, ‖φ y - φ (u * y)‖ ∂μ) * ‖(F : G →ᵇ ℂ)‖ := by
      rw [h3, ← integral_mul_const]
      exact norm_integral_le_of_norm_le ((hφ.sub (hφ.comp_mul_left u)).norm.mul_const _)
        (Eventually.of_forall fun y => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (kb s F x y) (norm_nonneg _))
    rw [norm_mul, Complex.norm_two] at h4
    rw [Qa]
    have h5 : ∫ y, ‖φ y - φ (u * y)‖ ∂μ < e := hu
    nlinarith [norm_nonneg (F : G →ᵇ ℂ)]
  intro s F ⟨hFc, M, hM⟩ hN ha x
  have h0 := congrArg (fun T : X →L[ℂ] X => (T ⟨ofNormedAddCommGroup F hFc M hM, hN, ha⟩ : G →ᵇ ℂ) x)
    (idemZero _ Q hQc hQi hQt s)
  have h1 : ∫ y, φ y * (F (x * y) * eI (s * (Ht (x * y) - Ht x))) ∂μ = 0 := h0
  have h2 := congrArg (· * eI (s * Ht x)) h1
  simp only [zero_mul, ← integral_mul_const, mul_assoc, ← eI_add] at h2
  rw [← h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  congr 2
  rw [← mul_add, sub_add_cancel]
  rfl

theorem selP : Sel := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hi N a Ht P F ⟨hFc, M, hM⟩ hN x
  let Fr : ℝ → G → ℂ := fun r y => F (a (r - Ht y) * y)
  have Frc : Continuous fun p : ℝ × G => Fr p.1 p.2 :=
    hFc.comp ((P.cont.comp (continuous_fst.sub (P.hcont.comp continuous_snd))).mul continuous_snd)
  have tw : ∀ r s, ∫ y, φ y * (Fr r (x * y) * eI (s * Ht (x * y))) ∂μ = 0 := fun r s =>
    selTw G μ φ hφ hi N a Ht P s (Fr r) ⟨Frc.comp (continuous_const.prodMk continuous_id), M, fun _ => hM _⟩
      (fun m hm y => by
        have := hN _ (P.norm (r - Ht y) m hm) (a (r - Ht y) * y)
        simp only [Fr, P.hN m hm]
        rw [← this]
        congr 1
        group)
      (fun t y => by
        simp only [Fr, P.ha]
        rw [← mul_assoc, ← P.add]
        congr 3
        ring) x

  have step : ∀ r (g : ℝ → ℂ), Integrable g →
      ∫ y, φ y * Fr r (x * y) * (∫ s, g s * eI (s * (r - Ht (x * y)))) ∂μ = 0 := by
    intro r g hg
    have hc1 : Continuous fun y => Fr r (x * y) := Frc.comp (continuous_const.prodMk (continuous_const.mul continuous_id))
    have hI : Integrable (fun p : G × ℝ => φ p.1 * Fr r (x * p.1) * g p.2 * eI (p.2 * (r - Ht (x * p.1))))
        (μ.prod volume) :=
      ((integrable_mul_bc hφ hc1 fun _ => hM _).mul_prod hg).mul_bdd (c := 1)
        (continuous_eI.comp (continuous_snd.mul (continuous_const.sub
          (P.hcont.comp (continuous_const.mul continuous_fst))))).aestronglyMeasurable
        (Eventually.of_forall fun p => (norm_eI _).le)
    simp only [← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap hI]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
    have := congrArg (g s * eI (s * r) * ·) (tw r (-s))
    simp only [mul_zero, ← integral_const_mul] at this
    beta_reduce
    rw [Pi.zero_apply, ← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [mul_sub, sub_eq_add_neg, eI_add, neg_mul]
    ring
  let ψ : ℝ → ℂ := fun u => ∫ y, φ y * F (a u * (x * y)) ∂μ
  have hc2 : Continuous fun p : ℝ × G => F (a p.1 * (x * p.2)) :=
    hFc.comp ((P.cont.comp continuous_fst).mul (continuous_const.mul continuous_snd))
  have ψc : Continuous ψ :=
    continuous_of_dominated (bound := fun y => ‖φ y‖ * M)
      (fun u => (integrable_mul_bc hφ (hc2.comp (continuous_const.prodMk continuous_id)) fun _ => hM _).aestronglyMeasurable)
      (fun u => Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
      (hφ.norm.mul_const _) (Eventually.of_forall fun y =>
        continuous_const.mul (hc2.comp (continuous_id.prodMk continuous_const)))
  have key : ∀ g ρ : ℝ → ℂ, Integrable g → Integrable ρ → Continuous ρ → (∀ u, ρ u = ∫ s, g s * eI (s * u)) →
      ∫ u, ρ u * ψ u = 0 := by
    intro g ρ hg hρ hρc he
    have hI : Integrable (fun p : G × ℝ => φ p.1 * ρ p.2 * F (a p.2 * (x * p.1))) (μ.prod volume) :=
      (hφ.mul_prod hρ).mul_bdd (c := M) (hc2.comp continuous_swap).aestronglyMeasurable
        (Eventually.of_forall fun _ => hM _)
    have hmp : MeasurePreserving (fun p : G × ℝ => (p.1, p.2 - Ht (x * p.1))) (μ.prod volume) (μ.prod volume) :=
      MeasurePreserving.skew_product (g := fun y r => r - Ht (x * y)) (MeasurePreserving.id μ)
        (continuous_snd.sub (P.hcont.comp (continuous_const.mul continuous_fst))).measurable
        (Eventually.of_forall fun y => (measurePreserving_sub_right volume _).map_eq)
    have hI2 := hmp.integrable_comp_of_integrable hI
    calc ∫ u, ρ u * ψ u = ∫ u, ∫ y, φ y * ρ u * F (a u * (x * y)) ∂μ := by
          simp only [ψ, ← integral_const_mul]
          congr 1; funext u; congr 1; funext y; ring
      _ = ∫ y, (∫ u, φ y * ρ u * F (a u * (x * y))) ∂μ := (integral_integral_swap hI).symm
      _ = ∫ y, (∫ r, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y))) ∂μ := by
          congr 1; funext y
          exact (integral_sub_right_eq_self (fun u => φ y * ρ u * F (a u * (x * y))) _).symm
      _ = ∫ r, ∫ y, φ y * ρ (r - Ht (x * y)) * F (a (r - Ht (x * y)) * (x * y)) ∂μ := integral_integral_swap hI2
      _ = 0 := by
          refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
          beta_reduce
          rw [Pi.zero_apply, ← step r g hg]
          congr 1; funext y
          rw [← he]
          simp only [Fr]
          ring
  have hψ : ∀ u, ψ u = 0 := by
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ)) ψc.locallyIntegrable
      fun ρ hρ hs => by
        let f : SchwartzMap ℝ ℂ := (hs.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
          (Complex.ofRealCLM.contDiff.comp hρ)
        let g : ℝ → ℂ := fun s => ((2 * Real.pi)⁻¹ : ℝ) • FourierTransform.fourier (f : ℝ → ℂ) ((2 * Real.pi)⁻¹ * s)
        have hf : Integrable (FourierTransform.fourier (f : ℝ → ℂ)) := (FourierTransform.fourier f).integrable
        have h2 : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
        have := key g f ((hf.comp_mul_left' h2).smul ((2 * Real.pi)⁻¹ : ℝ)) f.integrable f.continuous fun u => by
          rw [← congrFun (f.continuous.fourierInv_fourier_eq f.integrable hf) u, Real.fourierInv_eq']
          have e := Measure.integral_comp_mul_left
            (fun v => Complex.exp ((2 * Real.pi * inner ℝ v u : ℝ) * Complex.I) • FourierTransform.fourier (f : ℝ → ℂ) v)
            (2 * Real.pi)⁻¹
          rw [inv_inv, abs_of_pos (by positivity)] at e
          rw [← inv_smul_smul₀ (show (2 * Real.pi) ≠ 0 by positivity) (∫ v, _), ← e, ← integral_smul]
          congr 1; funext s
          simp only [g, eI, smul_eq_mul, Complex.real_smul, RCLike.inner_apply, conj_trivial]
          rw [show 2 * Real.pi * (u * ((2 * Real.pi)⁻¹ * s)) = s * u by field_simp]
          ring
        rw [← this]
        simp only [Complex.real_smul]
        rfl
    exact congrFun ((ψc.ae_eq_iff_eq volume continuous_const).1 hae)
  have a0 : a 0 = 1 := by
    have := P.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  simpa [ψ, a0] using hψ 0

end CompanionTheory.D.gk.RF
end
end

open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise

noncomputable section

namespace CompanionTheory.D.gk.RF

theorem sq_lintegral_le {X : Type} [MeasurableSpace X] (μ : Measure X) {θ f : X → ℝ≥0∞} (hθ : AEMeasurable θ μ)
    (hf : AEMeasurable f μ) : (∫⁻ y, θ y * f y ∂μ) ^ 2 ≤ (∫⁻ y, θ y ∂μ) * ∫⁻ y, θ y * f y ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun y => θ y ^ (1 / 2 : ℝ)) (g := fun y => θ y ^ (1 / 2 : ℝ) * f y) (hθ.pow_const _) ((hθ.pow_const _).mul hf)
  have e0 : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a := fun a => by rw [← ENNReal.rpow_mul]; norm_num
  have e1 : ∀ a : ℝ≥0∞, a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := fun a => by
    rw [← _root_.sq, ← ENNReal.rpow_two, e0]
  simp only [Pi.mul_apply, ← mul_assoc, e1, e0, ENNReal.mul_rpow_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2),
    ENNReal.rpow_two] at h
  have e2 : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by rw [← ENNReal.rpow_two, e0]
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, e2, e2]

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem setLIntegral_right [μ.IsMulRightInvariant] (hD : IsFundamentalDomain Γ D μ) {f : G → ℝ≥0∞}
    (hΓ : LInv Γ f) (y : G) : ∫⁻ x in D, f (x * y) ∂μ = ∫⁻ x in D, f x ∂μ := by
  have hmp := measurePreserving_mul_right μ y⁻¹
  have hD' : IsFundamentalDomain Γ ((fun x => x * y⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (e := id) hmp.quasiMeasurePreserving Function.bijective_id fun g x => by
      show ((g : G) * x) * y⁻¹ = (g : G) * (x * y⁻¹)
      rw [mul_assoc]
  rw [← hD'.setLIntegral_eq hD f fun g x => hΓ g g.2 x,
    ← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_mulRight y⁻¹) (fun x => f (x * y)) D]
  simp

end

theorem young_convolution_inequality : Young := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Γ _ D hD f θ hf hθ hΓ
  have hm : Measurable fun p : G × G => f (p.1 * p.2) := hf.comp measurable_mul
  calc ∫⁻ x in D, (∫⁻ y, θ y * f (x * y) ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ x in D, (∫⁻ y, θ y ∂μ) * ∫⁻ y, θ y * f (x * y) ^ 2 ∂μ ∂μ :=
        lintegral_mono fun x => sq_lintegral_le μ hθ (hf.comp (measurable_const_mul x)).aemeasurable
    _ = (∫⁻ y, θ y ∂μ) * ∫⁻ x in D, ∫⁻ y, θ y * f (x * y) ^ 2 ∂μ ∂μ :=
        lintegral_const_mul'' _ (AEMeasurable.lintegral_prod_right' (f := fun p : G × G => θ p.2 * f (p.1 * p.2) ^ 2)
          (hθ.comp_snd.mul (hm.pow_const 2).aemeasurable))
    _ = (∫⁻ y, θ y ∂μ) * ∫⁻ y, (∫⁻ x in D, θ y * f (x * y) ^ 2 ∂μ) ∂μ := by
        rw [lintegral_lintegral_swap (hθ.comp_snd.mul (hm.pow_const 2).aemeasurable)]
    _ = (∫⁻ y, θ y ∂μ) * ∫⁻ y, θ y * ∫⁻ x in D, f x ^ 2 ∂μ ∂μ := by
        congr 2
        funext y
        rw [lintegral_const_mul (f := fun x => f (x * y) ^ 2) _ ((hf.comp (measurable_mul_const y)).pow_const 2),
          setLIntegral_right hD (f := fun x => f x ^ 2) (fun g hg x => by simp only [hΓ g hg]) y]
    _ = _ := by rw [lintegral_mul_const'' _ hθ, _root_.sq, mul_assoc]

theorem compact_integral_quotient_bound : CompactIntegralBoundedByQuotientNorm := by
  classical
  intro G _ _ _ _ _ _ _ _ μ _ Γ _ D hD hd B hB
  have hfin := hd _ (hB.mul hB.inv)
  refine ⟨μ B * hfin.toFinset.card, ENNReal.mul_ne_top hB.measure_lt_top.ne (by simp), fun f hf hΓ => ?_⟩
  have h1 := sq_lintegral_le (μ.restrict B) (θ := fun _ => 1) aemeasurable_const hf.aemeasurable
  simp only [one_mul, lintegral_const, Measure.restrict_apply_univ] at h1
  refine h1.trans ?_
  rw [mul_assoc]
  gcongr
  have hm : Measurable (B.indicator fun x => f x ^ 2) := (hf.pow_const 2).indicator hB.measurableSet
  rw [← lintegral_indicator hB.measurableSet, hD.lintegral_eq_tsum'', ← lintegral_tsum (f := fun (g : Γ) x => B.indicator (fun y => f y ^ 2) (g • x)) fun g =>
    (hm.comp (measurable_const_smul g)).aemeasurable, ← lintegral_const_mul _ (hf.pow_const 2)]
  refine lintegral_mono fun x => ?_
  by_cases h : ∃ g₀ : Γ, g₀ • x ∈ B
  · obtain ⟨g₀, h₀⟩ := h
    let s : Finset Γ := hfin.toFinset.preimage (fun g : Γ => (g : G) * (g₀ : G)⁻¹)
      ((mul_left_injective _).comp Subtype.val_injective).injOn
    rw [tsum_eq_sum (s := s) fun g hg => indicator_of_notMem (fun hgB => hg ?_) _]
    · refine (Finset.sum_le_card_nsmul _ _ (f x ^ 2) fun g _ => (indicator_le_self _ _ _).trans
        (le_of_eq (by rw [show g • x = (g : G) * x from rfl, hΓ g g.2]))).trans ?_
      rw [nsmul_eq_mul]
      gcongr
      exact Finset.card_le_card_of_injOn (fun g : Γ => (g : G) * (g₀ : G)⁻¹) (fun g hg => by
        simpa only [s, Finset.mem_coe, Finset.mem_preimage] using hg)
        ((mul_left_injective _).comp Subtype.val_injective).injOn
    · rw [Finset.mem_preimage, Set.Finite.mem_toFinset]
      refine ⟨⟨_, hgB, _, Set.inv_mem_inv.2 h₀, ?_⟩, Γ.mul_mem g.2 (Γ.inv_mem g₀.2)⟩
      show (g : G) * x * ((g₀ : G) * x)⁻¹ = _
      group
  · push Not at h
    simp [indicator_of_notMem (h _)]

theorem near_cusp_measure_estimate : NearMeas := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ _ D hD C hC
  have e : {x | ∃ γ ∈ Γ, γ * x ∈ C} = ⋃ g : Γ, (fun x => (g : G) * x) ⁻¹' C := by
    ext x; simp
  rw [e]
  refine ⟨MeasurableSet.iUnion fun g => measurable_const_mul _ hC.measurableSet, ?_⟩
  rw [inter_iUnion, hD.measure_eq_tsum C, ← (Equiv.inv Γ).tsum_eq]
  refine (measure_iUnion_le _).trans (le_of_eq ?_)
  refine tsum_congr fun g => ?_
  rw [inter_comm]
  congr 2
  ext x
  simp only [Equiv.inv_apply, inv_inv, mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem uniform_continuity_estimate : UnifC := by
  intro G _ _ _ _ _ α hc hs
  obtain ⟨U₀, hU₀, hU₀c⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨U₀ * tsupport α, hU₀.mul hs, fun e he => ?_⟩
  have h1 : ∀ᶠ u in 𝓝 (1 : G), ∀ y ∈ U₀ * tsupport α, ‖α (u⁻¹ * y) - α y‖ ≤ e := by
    refine (hU₀.mul hs).eventually_forall_of_forall_eventually fun y _ => ?_
    have : Continuous fun p : G × G => ‖α (p.1⁻¹ * p.2) - α p.2‖ := by fun_prop
    exact (this.tendsto (1, y)).eventually (ge_mem_nhds (by simpa using he))
  refine ⟨_, inter_mem h1 hU₀c, fun u hu y => ?_⟩
  have h2 : y ∉ U₀ * tsupport α → α (u⁻¹ * y) = 0 ∧ α y = 0 := fun hy =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hy ⟨u, hu.2, _, h, by simp⟩,
      image_eq_zero_of_notMem_tsupport fun h => hy ⟨1, mem_of_mem_nhds hU₀c, _, h, by simp⟩⟩
  refine ⟨?_, h2⟩
  by_cases hy : y ∈ U₀ * tsupport α
  · exact hu.1 y hy
  · rw [(h2 hy).1, (h2 hy).2]; simpa using he.le

theorem approximation_of_square_identity : Approx := by
  intro G _ _ _ _ _ _ _ _ μ _ φ O hφ hO h0 e he
  obtain ⟨g, hgs, hge, hgc, hgi⟩ := hφ.exists_hasCompactSupport_integral_sub_le he
  refine ⟨O.indicator g, hO.continuous_indicator hgc, hgs.mono (fun y hy h => hy (by simp [indicator, h])), fun y hy =>
    indicator_of_notMem hy _, le_trans (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hφ.sub hgi).norm (Eventually.of_forall fun y => ?_)) hge⟩
  by_cases hy : y ∈ O
  · simp [indicator_of_mem hy]
  · simp [indicator_of_notMem hy, h0 y hy]

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

theorem diff_est {α h : G → ℂ} (hα : Integrable α μ) (hh : BC h) {B : Set G} (hB : IsCompact B) {e : ℝ} {u : G}
    (hu : ∀ y, ‖α (u⁻¹ * y) - α y‖ ≤ e ∧ (y ∉ B → α (u⁻¹ * y) = 0 ∧ α y = 0)) (x : G) :
    ‖∫ y, α y * h (x * u * y) ∂μ - ∫ y, α y * h (x * y) ∂μ‖ₑ ≤ ENNReal.ofReal e * ∫⁻ y in B, ‖h (x * y)‖ₑ ∂μ := by
  obtain ⟨hc, M, hM⟩ := hh
  have hc' : Continuous fun y => h (x * y) := hc.comp (continuous_const.mul continuous_id)
  have e1 : ∫ y, α y * h (x * u * y) ∂μ = ∫ y, α (u⁻¹ * y) * h (x * y) ∂μ := by
    rw [← integral_mul_left_eq_self (fun y => α (u⁻¹ * y) * h (x * y)) u]
    simp only [inv_mul_cancel_left, mul_assoc]
  rw [e1, ← integral_sub (integrable_mul_bc (hα.comp_mul_left _) hc' fun _ => hM _)
    (integrable_mul_bc hα hc' fun _ => hM _), ← lintegral_indicator hB.measurableSet,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy, ← sub_mul, enorm_mul]
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hu y).1
  · simp [((hu y).2 hy).1, ((hu y).2 hy).2]

end

theorem far_from_cusp_estimate : FarEst := by
  intro G _ _ _ _ _ _ _ _ μ _ φ α Γ O U B e hc hs h0 hB hU x ⟨ν, hν, hνU, hv⟩ h hh
  have hα : Integrable α μ := hc.integrable_of_hasCompactSupport hs
  obtain ⟨hhc, M, hM⟩ := hh.1
  have hI : Integrable (fun p : G × G => α p.2 * h (p.1 * x * p.2)) (ν.prod μ) :=
    (hα.comp_snd ν).mul_bdd (by fun_prop : Continuous fun p : G × G => h (p.1 * x * p.2)).aestronglyMeasurable
      (Eventually.of_forall fun _ => hM _)
  have h1 : ∫ m, ∫ y, α y * h (m * x * y) ∂μ ∂ν = 0 := by
    rw [integral_integral_swap hI]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [integral_const_mul]
    by_cases hy : y ∈ O
    · simp [hv h hh y hy]
    · simp [h0 y hy]
  have h2 : ∫ y, α y * h (x * y) ∂μ = -∫ m, (∫ y, α y * h (m * x * y) ∂μ - ∫ y, α y * h (x * y) ∂μ) ∂ν := by
    rw [integral_sub hI.integral_prod_left (integrable_const _), h1]
    simp
  rw [h2, enorm_neg]
  refine (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono_ae ?_).trans
    (le_of_eq (by rw [lintegral_const, measure_univ, mul_one])))
  filter_upwards [hνU] with m hm
  have := diff_est hα hh.1 hB (hU _ hm) x
  rwa [show x * (x⁻¹ * m * x) = m * x by group] at this

theorem near_cusp_estimate : NearEst := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ _ D hD hd α hc hs C hC e he
  have hα : Integrable α μ := hc.integrable_of_hasCompactSupport hs
  obtain ⟨B, hB, hU⟩ := uniform_continuity_estimate G α hc hs
  obtain ⟨M, hM, hL⟩ := compact_integral_quotient_bound G μ Γ D hD hd _ (hC.mul hB)
  obtain ⟨d, hd0, hde⟩ : ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ^ 2 * M ≤ e := by
    have ht : Tendsto (fun d : ℝ => ENNReal.ofReal d ^ 2 * M) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0 ^ 2 * M)) :=
      ENNReal.Tendsto.mul_const (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).continuousWithinAt)
        (Or.inr hM)
    rw [ENNReal.ofReal_zero, zero_pow two_ne_zero, zero_mul] at ht
    exact ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ))).and (ht.eventually (ge_mem_nhds he))).exists
  obtain ⟨U, hU1, hUe⟩ := hU d hd0
  obtain ⟨t, htC, ht⟩ := hC.elim_nhds_subcover (fun p => (fun x => p⁻¹ * x) ⁻¹' U) fun p _ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU1)
  refine ⟨t.card, fun i => t.equivFin.symm i, fun h hh hΓ h0 x hx => ?_⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (ht hx)
  have h1 := diff_est hα hh hB (hUe _ hxp) p
  have h2 := h0 (t.equivFin ⟨p, hp⟩)
  simp only [Equiv.symm_apply_apply] at h2
  rw [mul_inv_cancel_left, h2, sub_zero] at h1
  have h3 : ∫⁻ y in B, ‖h (p * y)‖ₑ ∂μ ≤ ∫⁻ y in C * B, ‖h y‖ₑ ∂μ := by
    rw [← (measurePreserving_mul_left μ p).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft p)
      (fun y => ‖h y‖ₑ) (C * B)]
    exact lintegral_mono_set fun y hy => ⟨p, htC p hp, y, hy, rfl⟩
  have h4 := hL (fun y => ‖h y‖ₑ) hh.1.measurable.enorm fun g hg y => by simp only [hΓ g hg]
  calc _ ≤ (ENNReal.ofReal d * ∫⁻ y in C * B, ‖h y‖ₑ ∂μ) ^ 2 := by gcongr; exact h1.trans (by gcongr)
    _ ≤ ENNReal.ofReal d ^ 2 * (M * sq μ D h) := by rw [mul_pow]; gcongr; exact h4
    _ ≤ _ := by rw [← mul_assoc]; gcongr

theorem exists_small {M : ℝ≥0∞} (hM : M ≠ ∞) : ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d * M ≤ 8⁻¹ := by
  have ht : Tendsto (fun d : ℝ => ENNReal.ofReal d * M) (𝓝[>] 0) (𝓝 (ENNReal.ofReal 0 * M)) :=
    ENNReal.Tendsto.mul_const ENNReal.continuous_ofReal.continuousWithinAt (Or.inr hM)
  rw [ENNReal.ofReal_zero, zero_mul] at ht
  exact ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ))).and (ht.eventually (ge_mem_nhds (by simp)))).exists

theorem add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) one_le_two
  norm_num at this
  exact this

theorem discrete_series_bound_of_inputs : Core := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Γ _ D hD hd φ O hφ hO h0 hcusp
  obtain ⟨α, hc, hs, hα0, hap⟩ := approximation_of_square_identity G μ φ O hφ hO h0 8⁻¹ (by norm_num)
  have hα : Integrable α μ := hc.integrable_of_hasCompactSupport hs
  obtain ⟨B, hB, hU⟩ := uniform_continuity_estimate G α hc hs
  obtain ⟨e, he, heB⟩ := exists_small (hB.measure_lt_top (μ := μ)).ne
  obtain ⟨U, hU1, hUe⟩ := hU e he
  obtain ⟨C, hC, hCx⟩ := hcusp U hU1
  obtain ⟨e₂, he₂, he₂C⟩ := exists_small (hC.measure_lt_top (μ := μ)).ne
  obtain ⟨m, p, hp⟩ := near_cusp_estimate G μ Γ D hD hd α hc hs C hC (ENNReal.ofReal e₂) (by simpa using he₂)
  refine ⟨m, α, p, hc, hs, fun h hh hfin hz => ?_⟩
  obtain ⟨hhc, M, hM⟩ := hh.1
  obtain ⟨hZm, hZ⟩ := near_cusp_measure_estimate G μ Γ D hD C hC
  set Z := {x | ∃ γ ∈ Γ, γ * x ∈ C}
  set S := sq μ D h with hS
  have hf : Measurable fun y => ‖h y‖ₑ := hhc.measurable.enorm
  have hfΓ : LInv Γ fun y => ‖h y‖ₑ := fun g hg y => by simp only [hh.2.1 g hg]
  have hm2 : Measurable fun p : G × G => ‖h (p.1 * p.2)‖ₑ := hf.comp measurable_mul
  let θ₁ : G → ℝ≥0∞ := fun y => ‖φ y - α y‖ₑ
  let θ₂ : G → ℝ≥0∞ := B.indicator fun _ => ENNReal.ofReal e
  have hθ₁ : AEMeasurable θ₁ μ := (hφ.sub hα).aestronglyMeasurable.enorm
  have hθ₂ : Measurable θ₂ := measurable_const.indicator hB.measurableSet
  have i₁ : ∫⁻ y, θ₁ y ∂μ ≤ 8⁻¹ := by
    refine (ofReal_integral_norm_eq_lintegral_enorm (hφ.sub hα)).symm.trans_le ?_
    refine (ENNReal.ofReal_le_ofReal hap).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  have i₂ : ∫⁻ y, θ₂ y ∂μ ≤ 8⁻¹ := by
    rw [lintegral_indicator_const hB.measurableSet]; exact heB
  let r₁ : G → ℝ≥0∞ := fun x => (∫⁻ y, θ₁ y * ‖h (x * y)‖ₑ ∂μ) ^ 2
  let r₂ : G → ℝ≥0∞ := fun x => (∫⁻ y, θ₂ y * ‖h (x * y)‖ₑ ∂μ) ^ 2
  have y₁ : ∫⁻ x in D, r₁ x ∂μ ≤ 8⁻¹ ^ 2 * S := (young_convolution_inequality G μ Γ D hD _ θ₁ hf hθ₁ hfΓ).trans (by gcongr; rfl)
  have y₂ : ∫⁻ x in D, r₂ x ∂μ ≤ 8⁻¹ ^ 2 * S :=
    (young_convolution_inequality G μ Γ D hD _ θ₂ hf hθ₂.aemeasurable hfΓ).trans (by gcongr; rfl)
  have hr₂ : Measurable r₂ := (((hθ₂.comp measurable_snd).mul hm2).lintegral_prod_right').pow_const 2
  have pt : ∀ x, ‖h x‖ₑ ^ 2 ≤ 2 * (Z.indicator (fun _ => ENNReal.ofReal e₂ * S) x + r₂ x + r₁ x) := by
    intro x
    have hc' : Continuous fun y => h (x * y) := hhc.comp (continuous_const.mul continuous_id)
    have e1 : h x = ∫ y, α y * h (x * y) ∂μ + ∫ y, (φ y - α y) * h (x * y) ∂μ := by
      rw [← integral_add (integrable_mul_bc hα hc' fun _ => hM _) (integrable_mul_bc (φ := fun y => φ y - α y) (hφ.sub hα) hc' fun _ => hM _),
        hh.2.2 x]
      congr 1; funext y; ring
    have b1 : ‖∫ y, (φ y - α y) * h (x * y) ∂μ‖ₑ ^ 2 ≤ r₁ x := by
      refine pow_le_pow_left' ?_ 2
      exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_mul, θ₁]))
    have b2 : ‖∫ y, α y * h (x * y) ∂μ‖ₑ ^ 2 ≤ Z.indicator (fun _ => ENNReal.ofReal e₂ * S) x + r₂ x := by
      rcases hCx x with hx | hx
      · rw [indicator_of_mem (show x ∈ Z from hx)]
        obtain ⟨γ, hγ, hγx⟩ := hx
        have := hp h hh.1 hh.2.1 hz _ hγx
        simp only [mul_assoc, hh.2.1 γ hγ] at this
        exact this.trans le_self_add
      · refine le_trans ?_ le_add_self
        refine pow_le_pow_left' ?_ 2
        refine (far_from_cusp_estimate G μ φ α Γ O U B e hc hs hα0 hB hUe x hx h hh).trans (le_of_eq ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hB.measurableSet]
        congr 1; funext y
        by_cases hy : y ∈ B <;> simp [θ₂, hy]
    rw [e1]
    refine (pow_le_pow_left' (enorm_add_le _ _) 2).trans ((add_sq_le _ _).trans ?_)
    gcongr
  have tot : S ≤ 2 * (8⁻¹ * S + 8⁻¹ ^ 2 * S + 8⁻¹ ^ 2 * S) := by
    refine (lintegral_mono pt).trans ?_
    rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left
      (f := fun a => Z.indicator (fun _ => ENNReal.ofReal e₂ * S) a + r₂ a) ((measurable_const.indicator hZm).add hr₂),
      lintegral_add_left (measurable_const.indicator hZm), lintegral_indicator_const hZm,
      Measure.restrict_apply hZm, inter_comm]
    refine mul_le_mul_right (add_le_add (add_le_add ?_ y₂) y₁) 2
    calc ENNReal.ofReal e₂ * S * μ (D ∩ Z) ≤ ENNReal.ofReal e₂ * S * μ C := by gcongr
      _ = ENNReal.ofReal e₂ * μ C * S := by ring
      _ ≤ _ := by gcongr
  lift S to NNReal using hfin with S' hS'
  have tot' : (S' : ℝ) ≤ 2 * (8⁻¹ * S' + 8⁻¹ ^ 2 * S' + 8⁻¹ ^ 2 * S') := by
    have := ENNReal.toReal_mono (by finiteness) tot
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)] at this
    simpa using this
  have : (S' : ℝ) = 0 := le_antisymm (by nlinarith [S'.2]) S'.2
  exact_mod_cast this

theorem finite_dimensional_from_linear_forms : FiniteDimensionalFromLinearForms := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ D φ hφ ⟨m, α, p, hc, hs, hdet⟩ S hS
  have hα : Integrable α μ := hc.integrable_of_hasCompactSupport hs
  have hi : ∀ {θ h : G → ℂ}, Integrable θ μ → BC h → ∀ x, Integrable (fun y => θ y * h (x * y)) μ :=
    fun hθ ⟨h1, _, hM⟩ x => integrable_mul_bc hθ (h1.comp (continuous_const.mul continuous_id)) fun _ => hM _
  let H₂ : Submodule ℂ (G → ℂ) :=
    { carrier := {h | IsRep μ φ Γ h ∧ MemLp h 2 (μ.restrict D)}
      add_mem' := fun {a b} ha hb => by
        obtain ⟨M, hM⟩ := ha.1.1.2
        obtain ⟨M', hM'⟩ := hb.1.1.2
        refine ⟨⟨⟨ha.1.1.1.add hb.1.1.1, M + M', fun x => norm_add_le_of_le (hM x) (hM' x)⟩,
          fun g hg x => by simp only [Pi.add_apply, ha.1.2.1 g hg, hb.1.2.1 g hg], fun x => ?_⟩, ha.2.add hb.2⟩
        simp only [Pi.add_apply, mul_add]
        rw [integral_add (hi hφ ha.1.1 x) (hi hφ hb.1.1 x), ← ha.1.2.2, ← hb.1.2.2]
      zero_mem' := ⟨⟨⟨continuous_const, 0, by simp⟩, fun _ _ _ => rfl, by simp⟩, MemLp.zero⟩
      smul_mem' := fun c a ha => by
        obtain ⟨M, hM⟩ := ha.1.1.2
        refine ⟨⟨⟨ha.1.1.1.const_smul c, ‖c‖ * M, fun x => by
          rw [Pi.smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)⟩,
          fun g hg x => by simp only [Pi.smul_apply, ha.1.2.1 g hg], fun x => ?_⟩, ha.2.const_smul c⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, ← ha.1.2.2] }
  let r : H₂ →ₗ[ℂ] Lp ℂ 2 (μ.restrict D) :=
    { toFun := fun h => h.2.2.toLp _
      map_add' := fun a b => MemLp.toLp_add _ _
      map_smul' := fun c a => MemLp.toLp_const_smul c _ }
  let l : H₂ →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun h i => ∫ y, α y * h.1 (p i * y) ∂μ
      map_add' := fun a b => funext fun i => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hi hα a.2.1.1 _) (hi hα b.2.1.1 _)
      map_smul' := fun c a => funext fun i => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, RingHom.id_apply]
        exact integral_const_mul _ _ }
  have hker : LinearMap.ker l ≤ LinearMap.ker r := fun h hh => by
    have hfin : sq μ D h.1 ≠ ∞ := by
      have := (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero (by simp) h.2.2).ne
      simpa [sq] using this
    have h0 := hdet h.1 h.2.1 hfin fun i => congrFun hh i
    rw [sq, lintegral_eq_zero_iff (h.2.1.1.1.measurable.enorm.pow_const 2)] at h0
    refine (Lp.eq_zero_iff_ae_eq_zero).2 (h.2.2.coeFn_toLp.trans ?_)
    filter_upwards [h0] with x hx
    simpa using hx
  have hfd : FiniteDimensional ℂ (LinearMap.range r) := by
    have : FiniteDimensional ℂ (H₂ ⧸ LinearMap.ker l) := l.quotKerEquivRange.symm.finiteDimensional
    rw [← Submodule.range_liftQ _ r hker]
    infer_instance
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range r) fun F hF => ?_
  refine (LinearMap.range r).closed_of_finiteDimensional.closure_subset_iff.2 ?_ (hS F hF)
  rintro F' ⟨h, hh, hae⟩
  exact ⟨⟨h, hh, (memLp_congr_ae hae).1 (Lp.memLp F')⟩, Lp.ext ((MemLp.coeFn_toLp
    ((memLp_congr_ae hae).1 (Lp.memLp F'))).trans hae.symm)⟩

theorem representation_of_convolution : RepOfConv := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ φ φ₀ s hφ hφ₀ hconv hs ⟨M, hM⟩ hΓ
  have e : ∀ x, ∫ y, φ₀ y * s (x * y) ∂μ = ∫ y, φ₀ (x⁻¹ * y) * s y ∂μ := fun x => by
    rw [← integral_mul_left_eq_self (fun y => φ₀ (x⁻¹ * y) * s y) x]
    simp only [inv_mul_cancel_left]
  have hi : ∀ {θ : G → ℂ}, Integrable θ μ → ∀ x, Integrable (fun y => θ y * s (x * y)) μ := fun hθ x =>
    hθ.mul_bdd (hs.comp (measurable_const_mul x)).aestronglyMeasurable (Eventually.of_forall fun _ => hM _)
  have hb : ∀ {θ : G → ℂ}, Integrable θ μ → ∀ x, ‖∫ y, θ y * s (x * y) ∂μ‖ ≤ (∫ y, ‖θ y‖ ∂μ) * M := fun hθ x => by
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le (hθ.norm.mul_const _) (Eventually.of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
  refine ⟨⟨continuous_iff_continuousAt.2 fun x₀ => tendsto_iff_norm_sub_tendsto_zero.2 ?_, _, hb hφ₀⟩,
    fun g hg x => ?_, fun x => ?_⟩
  · have ht : Tendsto (fun x : G => x⁻¹ * x₀) (𝓝 x₀) (𝓝 1) := by
      have h : Continuous fun x : G => x⁻¹ * x₀ := by fun_prop
      simpa using h.tendsto x₀
    refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_)
      (by simpa using ((tendsto_transl hφ₀).comp ht).mul_const M)
    have e2 : ∫ y, φ₀ y * s (x * y) ∂μ = ∫ y, φ₀ (x⁻¹ * x₀ * y) * s (x₀ * y) ∂μ := by
      rw [← integral_mul_left_eq_self (fun y => φ₀ y * s (x * y)) (x⁻¹ * x₀)]
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    rw [norm_sub_rev, e2, ← integral_sub (hi hφ₀ x₀) (hi (hφ₀.comp_mul_left _) x₀)]
    simp only [← sub_mul]
    exact hb (hφ₀.sub (hφ₀.comp_mul_left _)) x₀
  · beta_reduce
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae (hΓ g hg)] with y hy
    rw [mul_assoc, hy]
  · have h1 : Integrable (fun p : G × G => φ p.1 * φ₀ (p.1⁻¹ * p.2)) (μ.prod μ) :=
      (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable (hφ.mul_prod hφ₀)
    have h2 : Integrable (fun p : G × G => φ p.1 * φ₀ (p.1⁻¹ * p.2) * s (x * p.2)) (μ.prod μ) :=
      h1.mul_bdd (hs.comp (measurable_snd.const_mul x)).aestronglyMeasurable (Eventually.of_forall fun p => hM _)
    symm
    calc ∫ y, φ y * ∫ z, φ₀ z * s (x * y * z) ∂μ ∂μ = ∫ y, ∫ w, φ y * φ₀ (y⁻¹ * w) * s (x * w) ∂μ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          beta_reduce
          rw [← integral_mul_left_eq_self (fun w => φ y * φ₀ (y⁻¹ * w) * s (x * w)) y, ← integral_const_mul]
          simp only [inv_mul_cancel_left, mul_assoc]
      _ = ∫ w, ∫ y, φ y * φ₀ (y⁻¹ * w) * s (x * w) ∂μ ∂μ := integral_integral_swap h2
      _ = _ := by simp only [integral_mul_const, hconv]

end CompanionTheory.D.gk.RF
