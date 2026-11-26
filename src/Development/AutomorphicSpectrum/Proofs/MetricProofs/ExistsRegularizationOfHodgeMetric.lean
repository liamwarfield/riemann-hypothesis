module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPotentialChartsWithRadii
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgePotentialSmoothOffBoundary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPotentialFromSncCharts

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsTiedRegularSetting
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExpLeLogR
open Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open scoped ContDiff

namespace LevelTowerAlt.Reg

variable {n : ℕ}

theorem usc_comp {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : UpperSemicontinuousOn φ U)
    {g : (Fin n → ℂ) → Fin n → ℂ} (hg : Continuous g) : UpperSemicontinuousOn (fun t => φ (g t)) (g ⁻¹' U) := by
  intro z hz y hy
  have h1 : ∀ᶠ x in 𝓝[U] (g z), φ x < y := h _ hz y hy
  exact (hg.continuousWithinAt.tendsto_nhdsWithin (Set.mapsTo_preimage g U)).eventually h1

theorem isPsh_aff {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : IsPsh U φ) (t₀ : Fin n → ℂ) (c : ℂ) :
    IsPsh ((fun t => t₀ + c • t) ⁻¹' U) fun t => φ (t₀ + c • t) := by
  refine ⟨usc_comp h.1 (by fun_prop), fun z w hd => ?_⟩
  have e : ∀ ζ : ℂ, t₀ + c • (z + ζ • w) = t₀ + c • z + ζ • (c • w) := fun ζ => by
    rw [smul_add, smul_comm c ζ, add_assoc]
  simp only [e]
  exact h.2 _ _ fun ζ hζ => e ζ ▸ hd ζ hζ

theorem isPsh_star {U : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (h : IsPsh U φ) :
    IsPsh (star ⁻¹' U) fun t => φ (star t) := by
  refine ⟨usc_comp h.1 continuous_star, fun z w hd => ?_⟩
  have e : ∀ ζ : ℂ, star (z + ζ • w) = star z + star ζ • star w := fun ζ => by rw [star_add, star_smul]
  obtain ⟨h1, h2⟩ := h.2 (star z) (star w) fun ζ hζ => by
    have := hd (star ζ) (by rwa [norm_star])
    rwa [Set.mem_preimage, e, star_star] at this
  have hc : ∀ θ : ℝ, star (circleMap 0 1 θ) = circleMap 0 1 (2 * Real.pi - θ) := fun θ => by
    rw [sub_eq_add_neg, add_comm, periodic_circleMap]
    simp [circleMap, ← Complex.exp_conj]
  refine ⟨?_, h2.trans_eq ?_⟩
  · unfold CircleIntegrable at h1 ⊢
    simp only [e, hc]
    have := (h1.comp_sub_left (2 * Real.pi)).symm
    simpa using this
  · unfold Real.circleAverage
    simp only [e, hc]
    rw [intervalIntegral.integral_comp_sub_left (fun θ => φ (star z + circleMap 0 1 θ • star w))]
    simp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
  {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd)

theorem exp_le_logR {t : Fin n → ℂ} (ht : ‖t‖ < 1) : Real.exp 1 ≤ χ.logR t := by
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ?_)
  split_ifs
  · rw [one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) ((norm_le_pi_norm t i).trans ht.le))
  · exact le_rfl

theorem piece {F : (Fin n → ℂ) → ℝ} (hO : IsOpen {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd})
    (hFs : ContDiffOn ℝ ∞ F {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd})
    (hFp : IsPsh {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd} F) {t₀ : Fin n → ℂ} {ε C Q : ℝ}
    (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) (hsep : ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖) (hC : 0 < C)
    (hb : ∀ t ∈ {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd}, ‖t - t₀‖ < 2 * ε →
      -(C * Real.log (χ.logR t)) ≤ F t ∧ F t ≤ C ∧
        ‖fderiv ℝ F t‖ ≤ C * χ.logR t ^ C * Real.exp (χ.logR t / 2))
    (L : (Fin n → ℂ) →L[ℝ] Fin n → ℂ) (hL : ∀ t i, ‖L t i‖ = ‖t i‖)
    (hLp : ∀ U φ, IsPsh U φ → IsPsh (L ⁻¹' U) fun t => φ (L t))
    {S : Finset (Fin n)} (hS : ∀ i, i ∈ S ↔ (i : ℕ) < χ.a ∧ t₀ i = 0) {q p : (Fin n → ℂ) → ℝ}
    (hq : ∀ t ∈ ball (0 : Fin n → ℂ) 1, |q t| ≤ Q)
    (hu : ∀ t ∈ ball (0 : Fin n → ℂ) 1, χ.γ (t₀ + (ε : ℂ) • L t) ∉ Bd → q t + p t = F (t₀ + (ε : ℂ) • L t)) :
    ContDiffOn ℝ ∞ (fun y => q y + p y) (ball 0 1 \ coordDiv S) ∧
      IsPsh (ball 0 1 \ coordDiv S) (fun y => q y + p y) ∧
      ∃ C' c : ℝ, 0 < C' ∧ ∀ t ∈ ball (0 : Fin n → ℂ) 1 \ coordDiv S, ∀ ρ : ℝ,
        Real.exp 1 + c + ∑ i ∈ S, Real.log (‖t i‖ ^ 2)⁻¹ ≤ ρ →
          p t ≤ C' ∧ -C' * Real.log ρ ≤ p t ∧
            ‖fderiv ℝ (fun y => q y + p y) t‖ ≤ C' * ρ ^ C' * Real.exp (ρ / 2) := by
  classical
  set O := {t | t ∈ ball (0 : Fin n → ℂ) 1 ∧ χ.γ t ∉ Bd} with hOdef
  have hLn : ∀ t, ‖L t‖ ≤ ‖t‖ := fun t =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (hL t i).trans_le (norm_le_pi_norm t i)
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
  have hT : ∀ t, ‖(ε : ℂ) • L t‖ ≤ ε * ‖t‖ := fun t => by
    rw [norm_smul, hεn]; exact mul_le_mul_of_nonneg_left (hLn t) hε.le
  have hTi : ∀ t i, ‖((ε : ℂ) • L t) i‖ = ε * ‖t i‖ := fun t i => by
    rw [Pi.smul_apply, norm_smul, hεn, hL]
  have hlow : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ∀ i, t₀ i ≠ 0 → ε ≤ ‖(t₀ + (ε : ℂ) • L t) i‖ := fun t ht i hi => by
    have h1 := hsep i hi
    have h2 := hTi t i
    have h3 := norm_sub_le ((t₀ + (ε : ℂ) • L t) i) (((ε : ℂ) • L t) i)
    rw [Pi.add_apply, add_sub_cancel_right] at h3
    rw [Pi.add_apply]
    nlinarith [norm_le_pi_norm t i]
  have hball : ∀ t : Fin n → ℂ, ‖t‖ < 1 → ‖t₀ + (ε : ℂ) • L t‖ < 1 := fun t ht => by
    have := norm_add_le t₀ ((ε : ℂ) • L t)
    nlinarith [hT t, norm_nonneg t]
  have hmap : ∀ t ∈ ball (0 : Fin n → ℂ) 1 \ coordDiv S, t₀ + (ε : ℂ) • L t ∈ O := by
    rintro t ⟨ht, htS⟩
    rw [mem_ball_zero_iff] at ht
    have hb' := mem_ball_zero_iff.2 (hball t ht)
    refine ⟨hb', fun h => ?_⟩
    obtain ⟨i, hi, h0⟩ := (χ.boundary _ hb').1 h
    by_cases h1 : t₀ i = 0
    · refine htS ⟨i, (hS i).2 ⟨hi, h1⟩, ?_⟩
      have h2 := hTi t i
      rw [Pi.add_apply, h1, zero_add] at h0
      rw [h0, norm_zero] at h2
      exact norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hε.ne')
    · have := hlow t ht i h1
      rw [h0, norm_zero] at this
      linarith
  have hV : IsOpen (ball (0 : Fin n → ℂ) 1 \ coordDiv S) :=
    isOpen_ball.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
  have heq : Set.EqOn (fun t => F (t₀ + (ε : ℂ) • L t)) (fun y => q y + p y) (ball 0 1 \ coordDiv S) :=
    fun t ht => (hu t ht.1 (hmap t ht).2).symm
  have hσ : ContDiff ℝ ∞ fun t => t₀ + (ε : ℂ) • L t := contDiff_const.add (L.contDiff.const_smul _)
  have hpsh : IsPsh (ball 0 1 \ coordDiv S) (fun t => F (t₀ + (ε : ℂ) • L t)) := by
    have h := hLp _ _ (isPsh_aff hFp t₀ ε)
    exact ⟨h.1.mono hmap, fun z w hd => h.2 z w fun ζ hζ => hmap _ (hd ζ hζ)⟩
  have hpsh' : IsPsh (ball 0 1 \ coordDiv S) (fun t => q t + p t) := by
    refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
    · have h1 := hpsh.1 z hz y (by
        change F (t₀ + (ε : ℂ) • L z) < y
        simpa only [heq hz] using hy)
      filter_upwards [h1, self_mem_nhdsWithin] with x hx hxU
      simpa only [heq hxU] using hx
    · have hs : Set.EqOn (fun ζ : ℂ => F (t₀ + (ε : ℂ) • L (z + ζ • w)))
          (fun ζ => q (z + ζ • w) + p (z + ζ • w)) (sphere 0 |(1 : ℝ)|) :=
        fun ζ hζ => heq (hd ζ (by simp at hζ; rw [hζ]))
      obtain ⟨h1, h2⟩ := hpsh.2 z w hd
      refine ⟨(circleIntegrable_congr hs).1 h1, ?_⟩
      have hz : z ∈ ball 0 1 \ coordDiv S := by simpa using hd 0 (by simp)
      rw [← Real.circleAverage_congr_sphere hs, ← heq hz]
      exact h2
  refine ⟨(hFs.comp hσ.contDiffOn hmap).congr fun t ht => (heq ht).symm,
    hpsh', C + |Q|, n * Real.log (1 / ε ^ 2), by positivity,
    fun t ht ρ hρ => ?_⟩
  have ht1 : ‖t‖ < 1 := mem_ball_zero_iff.1 ht.1
  set s := t₀ + (ε : ℂ) • L t with hs
  have hsO : s ∈ O := hmap t ht
  obtain ⟨b1, b2, b3⟩ := hb s hsO (by
    rw [hs, add_sub_cancel_left]
    nlinarith [hT t, norm_nonneg t])
  have hRe := exp_le_logR χ (hball t ht1)
  have hRρ : χ.logR s ≤ ρ := by
    refine le_trans ?_ hρ
    have hl0 : 0 ≤ Real.log (1 / ε ^ 2) := Real.log_nonneg (by
      rw [le_div_iff₀ (by positivity)]; nlinarith)
    have : ∑ i : Fin n, (if (i : ℕ) < χ.a then Real.log (1 / ‖s i‖ ^ 2) else 0) ≤
        ∑ i : Fin n, (Real.log (1 / ε ^ 2) + if i ∈ S then Real.log (‖t i‖ ^ 2)⁻¹ else 0) := by
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : (i : ℕ) < χ.a
      · by_cases h1 : t₀ i = 0
        · have hiS := (hS i).2 ⟨hi, h1⟩
          have hti : ‖t i‖ ≠ 0 := norm_ne_zero_iff.2 fun h => ht.2 ⟨i, hiS, h⟩
          rw [if_pos hi, if_pos hiS, hs, Pi.add_apply, h1, zero_add, hTi,
            ← Real.log_mul (by positivity) (by positivity)]
          refine le_of_eq (congrArg _ ?_)
          field_simp
        · rw [if_pos hi, if_neg fun h => h1 ((hS i).1 h).2, add_zero]
          have h2 := hlow t ht1 i h1
          have h3 : 0 < ‖s i‖ := hε.trans_le h2
          exact Real.log_le_log (by positivity)
            (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hε.le h2 2))
      · rw [if_neg hi, if_neg fun h => hi ((hS i).1 h).1, add_zero]
        exact hl0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter] at this
    unfold SncChart.logR
    linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hl1 : 1 ≤ Real.log ρ := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  have hl2 : Real.log (χ.logR s) ≤ Real.log ρ := Real.log_le_log (by linarith) hRρ
  have hqt := abs_le.1 ((hq t ht.1).trans (le_abs_self Q))
  have hut : q t + p t = F s := hu t ht.1 hsO.2
  refine ⟨by linarith, by nlinarith [abs_nonneg Q], ?_⟩
  have hFd : HasFDerivAt F (fderiv ℝ F s) s :=
    ((hFs.contDiffAt (hO.mem_nhds hsO)).differentiableAt (by simp)).hasFDerivAt
  have hσd : HasFDerivAt (fun t => t₀ + (ε : ℂ) • L t) ((ε : ℂ) • L) t :=
    (L.hasFDerivAt.const_smul (ε : ℂ)).const_add t₀
  have hd : HasFDerivAt (fun y => q y + p y) ((fderiv ℝ F s).comp ((ε : ℂ) • L)) t :=
    (hFd.comp t hσd).congr_of_eventuallyEq
      (by filter_upwards [hV.mem_nhds ht] with y hy using (heq hy).symm)
  rw [hd.fderiv]
  have hn : ‖(fderiv ℝ F s).comp ((ε : ℂ) • L)‖ ≤ ‖fderiv ℝ F s‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    refine ((fderiv ℝ F s).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine (hT v).trans ?_
    nlinarith [norm_nonneg v]
  refine hn.trans (b3.trans ?_)
  have hp : χ.logR s ^ C ≤ ρ ^ (C + |Q|) :=
    (Real.rpow_le_rpow (by linarith) hRρ hC.le).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_add_of_nonneg_right (abs_nonneg Q)))
  have hρ0 : 0 ≤ χ.logR s := by linarith
  have hρ1 : 0 ≤ ρ := by linarith
  have hC' : C ≤ C + |Q| := le_add_of_nonneg_right (abs_nonneg Q)
  exact mul_le_mul (mul_le_mul hC' hp (Real.rpow_nonneg hρ0 _) (by positivity))
    (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)

end LevelTowerAlt.Reg
end

namespace LevelTowerAlt.Reg

open Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.Regular
open ReciprocityTheory.AnForm.A (IsPsh coordDiv)
open scoped ContDiff

section Ratio

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {d : ℕ}

noncomputable def logRat (M : CxModel P d) (A R : HermLine J) (x : M.Xc) : ℝ :=
  Real.log (A.h (M.surj x).choose) - Real.log (R.h (M.surj x).choose)

theorem logRat_proj (M : CxModel P d) {A R : HermLine J} (h : R.a = A.a) {z : (Σ k, J k) → ℂ}
    (hz : z ∈ mcPts P) : logRat M A R (M.proj z) = Real.log (A.h z) - Real.log (R.h z) := by
  obtain ⟨hw, he⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, hcz⟩ := (M.fibre z hz _ hw).1 he.symm
  have hp := (prod_norm_zpow_pos hc A.a).ne'
  unfold logRat
  rw [hcz]
  change Real.log (A.h fun p => c p.1 * z p) - Real.log (R.h fun p => c p.1 * z p) = _
  rw [A.smul c z hc, R.smul c z hc, h, Real.log_mul hp (A.pos z hz.1).ne', Real.log_mul hp (R.pos z hz.1).ne']
  ring

theorem exists_bound_log {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {R : HermLine J}
    (hR : IsSmoothHerm R) : ∃ Q : ℝ, ∀ s : Fin n → ℂ, ‖s‖ ≤ 3 / 4 → |Real.log (R.h (χ.γ s))| ≤ Q := by
  have hsub : closedBall (0 : Fin n → ℂ) (3 / 4) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have h1 : ContinuousOn (fun s => R.h (χ.γ s)) (closedBall (0 : Fin n → ℂ) (3 / 4)) :=
    hR.continuousOn.comp (χ.analytic.continuousOn.mono hsub) fun s hs => (χ.mem s (hsub hs)).1
  obtain ⟨Q, hQ⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (3 / 4)).exists_bound_of_continuousOn
    (h1.log fun s hs => (R.pos _ (χ.mem s (hsub hs)).1).ne')
  exact ⟨Q, fun s hs => hQ s (mem_closedBall_zero_iff.2 hs)⟩

end Ratio

theorem exists_radius {n : ℕ} (t₀ : Fin n → ℂ) {e : ℝ} (he : 0 < e) :
    ∃ r > (0 : ℝ), r ≤ e ∧ ∀ i, t₀ i ≠ 0 → r ≤ ‖t₀ i‖ := by
  have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i, t₀ i ≠ 0 → r ≤ ‖t₀ i‖ := eventually_all.2 fun i => by
    by_cases hi : t₀ i = 0
    · exact Eventually.of_forall fun _ h => absurd hi h
    · filter_upwards [Ioc_mem_nhdsGT (norm_pos_iff.2 hi)] with r hr _ using hr.2
  obtain ⟨r, hr⟩ := (h.and (Ioc_mem_nhdsGT he)).exists
  exact ⟨r, hr.2.1, hr.2.2, hr.1⟩

noncomputable def starL (n : ℕ) : (Fin n → ℂ) →L[ℝ] Fin n → ℂ :=
  ContinuousLinearMap.pi fun i => Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj i)

theorem margin_tendsto (C : ℝ) :
    Tendsto (fun t : ℝ => max t (C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => Real.log (Real.log t⁻¹) / Real.log t⁻¹) (𝓝[>] 0) (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have h2 := h0.max ((h1.const_mul C).add (h0.const_mul C))
  simpa [mul_div_assoc] using h2

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

theorem exists_tied {M : XModel D} {A ref : HermLine J} (hra : ref.a = A.a) (hrs : IsSmoothHerm ref)
    (R : RegChartData M.atlas) (hth : ThRef M ref R.th)
    (hY : ∀ x ∈ R.Yo, ∃ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), M.proj z = x)
    (hph : ∀ z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y), M.proj z ∈ R.Yo →
      R.ph (M.proj z) = Real.log (A.h z) - Real.log (ref.h z)) :
    ∃ S : LogLogRegularisationSetting M D.Xo A, S.IsTied := by
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D.n
  have hcut := CutoffsExist.proof M.Xc D.n M.atlas R.toPotentialCharts
  obtain ⟨cut, Cc, hcut⟩ := hcut
  obtain ⟨C, t₀, ht₀, hcmp⟩ := ChartComparison.proof MollifiedLowerBound.closed PolyMaxOscillation.proof_closed
    PolyMaxLowerBound.proof TruncPsh.proof TruncTransfer.proof M.Xc D.n M.atlas R ρ
  have hll : Tendsto (fun t : ℝ => Real.log (Real.log t⁻¹)) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  refine ⟨{ ref := ref, ref_deg := hra, ref_smooth := hrs, R := R, th_ref := hth, Yo_sub := hY, ph_eq := hph,
            ρ := ρ, η := cut, Cη := Cc, cutoff := hcut,
            K := fun t => (|C| + |R.Clog| + 1) * Real.log (Real.log t⁻¹),
            e1 := fun t => max t (C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t),
            e1_ge := fun _ _ => le_max_left _ _ }, margin_tendsto C,
    hll.const_mul_atTop (by positivity), ?_, ?_⟩
  · filter_upwards [hll.eventually_ge_atTop 0] with t ht
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self R.Clog, abs_nonneg C]) ht
  · filter_upwards [hll.eventually_ge_atTop 0, Ioo_mem_nhdsGT ht₀] with t h0 ht j k x hx
    exact (hcmp t ht.1 ht.2 _ (mul_le_mul_of_nonneg_right
      (by linarith [le_abs_self C, abs_nonneg R.Clog]) h0) j k x hx).trans (le_max_right _ _)

theorem mem_Yo {M : XModel D} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (∃ z' ∈ D.Xo, M.proj z' = M.proj z) ↔ z ∉ D.Bd := by
  refine ⟨?_, fun h => ⟨z, ⟨hz, h⟩, rfl⟩⟩
  rintro ⟨z', hz', e⟩ hB
  have hf := (M.fibre z hz z' hz'.1).1 e.symm
  obtain ⟨c, hc, rfl⟩ := hf
  exact hz'.2 (D.bd_torus z hB c hc)

theorem main (Hd : HodgeData D) (M : XModel D) (hP : ChartPsh D (phMu Hd)) :
    ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied := by
  classical
  obtain ⟨ref, hra, hrs, hrc⟩ := GlobalTheory.T.exists_smooth_conj_invariant_metric K J Hd.aMu
  have hreg := GlobalTheory.T.hodge_potential_smooth_off_boundary K J II Ψ Ω W D Hd
  obtain ⟨hsm, hbd⟩ := hreg
  obtain ⟨-, -, -, hO⟩ := GlobalTheory.T.hodge_metric_frame_properties K J II Ψ Ω W D Hd
  have hrad : ∀ (a : Fin D.nCharts) (t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), ∃ r > (0 : ℝ), (∀ i, t₀ i ≠ 0 → r ≤ ‖t₀ i‖) ∧
      (‖t₀‖ ≤ 1 / 2 → ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < r →
        -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧
          ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤
            C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2)) := by
    intro a t₀
    by_cases h : ‖t₀‖ ≤ 1 / 2
    · obtain ⟨e, he, C, hC, hb⟩ := hbd a t₀ h
      obtain ⟨r, hr, hre, hri⟩ := exists_radius t₀ he
      exact ⟨r, hr, hri, fun _ => ⟨C, hC, fun t ht h' => hb t ht (h'.trans_le hre)⟩⟩
    · obtain ⟨r, hr, -, hri⟩ := exists_radius t₀ one_pos
      exact ⟨r, hr, hri, fun h' => absurd h' h⟩
  choose r hr hri hrb using hrad
  obtain ⟨P, S, -, hth, had, hsnc, -, hpc⟩ := GlobalTheory.T.exists_potential_charts_with_radii K J II Ψ Ω W D M ref r hrs hrc hr
  obtain ⟨rf, f, Bf, hr1, hf, hrf⟩ := GlobalTheory.T.exists_potential_from_snc_charts K J II Ψ Ω W D M P S had hsnc
  let ph : M.Xc → ℝ := logRat M (muLine Hd) ref
  have hph : ∀ z ∈ mcPts (mCoordIdeal D.y), ph (M.proj z) = phMu Hd z - Real.log (ref.h z) :=
    fun z hz => logRat_proj M hra hz
  have hT : ∀ j, (P.chart j).target = ball 0 1 := fun j => (hsnc j).1
  have key : ∀ j, ContDiffOn ℝ ∞ (fun y => P.q j y + ph ((P.chart j).symm y)) (ball 0 1 \ coordDiv (S j)) ∧
      IsPsh (ball 0 1 \ coordDiv (S j)) (fun y => P.q j y + ph ((P.chart j).symm y)) ∧
      ∃ C' c : ℝ, 0 < C' ∧ ∀ t ∈ ball (0 : Fin D.n → ℂ) 1 \ coordDiv (S j), ∀ ρ : ℝ,
        Real.exp 1 + c + ∑ i ∈ S j, Real.log (‖t i‖ ^ 2)⁻¹ ≤ ρ →
          ph ((P.chart j).symm t) ≤ C' ∧ -C' * Real.log ρ ≤ ph ((P.chart j).symm t) ∧
            ‖fderiv ℝ (fun y => P.q j y + ph ((P.chart j).symm y)) t‖ ≤ C' * ρ ^ C' * Real.exp (ρ / 2) := by
    intro j
    obtain ⟨a, t₀, ε, h₀, hε, hεr, hε', hγ⟩ := hpc j
    have hsep : ∀ i, t₀ i ≠ 0 → 2 * ε ≤ ‖t₀ i‖ := fun i hi => hεr.trans (hri a t₀ i hi)
    have hS := had.mem_iff_of_piece (hT j) h₀ hε hε' (fun i _ => hsep i)
      (hγ.imp (fun h t ht => (h t ht).1) fun h t ht => (h t ht).1)
    obtain ⟨C, hC, hb⟩ := hrb a t₀ h₀
    obtain ⟨Q, hQ⟩ := exists_bound_log (n := D.n) (D.chart a) hrs
    have hn : ∀ t : Fin D.n → ℂ, ‖t‖ < 1 → ‖t₀ + (ε : ℂ) • t‖ ≤ 3 / 4 := fun t ht => by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε.le]
      nlinarith [norm_nonneg t]
    have hm : ∀ t : Fin D.n → ℂ, ‖t‖ < 1 → (D.chart a).γ (t₀ + (ε : ℂ) • t) ∈ mcPts (mCoordIdeal D.y) :=
      fun t ht => (D.chart a).mem _ (SncPiece.add_smul_mem_ball h₀ hε hε' (ht.trans one_lt_two))
    rw [hT j] at hγ
    rcases hγ with hγ | hγ
    · refine piece (n := D.n) (D.chart a) (SncPiece.isOpen_offBd D a) (hsm a) (hP a) h₀ hε hε' hsep hC
        (fun t ht h' => hb t ht (h'.trans_le hεr)) (ContinuousLinearMap.id ℝ _) (fun _ _ => rfl)
        (fun _ _ h => h) hS (Q := Q) (fun t ht => ?_) (fun t ht _ => ?_)
      · rw [(hγ t ht).2]
        exact hQ _ (hn t (mem_ball_zero_iff.1 ht))
      · rw [(hγ t ht).1, (hγ t ht).2, hph _ (hm t (mem_ball_zero_iff.1 ht))]
        exact add_sub_cancel _ _
    · refine piece (n := D.n) (D.chart a) (SncPiece.isOpen_offBd D a) (hsm a) (hP a) h₀ hε hε' hsep hC
        (fun t ht h' => hb t ht (h'.trans_le hεr)) (starL _) (fun _ _ => norm_star _)
        (fun _ _ h => isPsh_star h) hS (Q := Q) (fun t ht => ?_) (fun t ht hB => ?_)
      · rw [(hγ t ht).2]
        exact hQ _ (hn _ (by rw [norm_star]; exact mem_ball_zero_iff.1 ht))
      · have hz := hm (star t) (by rw [norm_star]; exact mem_ball_zero_iff.1 ht)
        have e1 : ref.h (conjVec ((D.chart a).γ (t₀ + (ε : ℂ) • star t))) = _ := hrc _
        rw [(hγ t ht).1, (hγ t ht).2, hph _ (SncPiece.conj_mem hz), hO _ ⟨hz, hB⟩, e1]
        exact add_sub_cancel _ _
  choose hks hkp C' c hC' hk using key
  set Cs : ℝ := ∑ j, C' j with hCs
  set cs : ℝ := |Bf| + ∑ j, |c j| with hcs
  have hCle : ∀ j, C' j ≤ Cs := fun j => Finset.single_le_sum (fun i _ => (hC' i).le) (Finset.mem_univ j)
  have hcle : ∀ j, |c j| ≤ ∑ j, |c j| := fun j =>
    Finset.single_le_sum (f := fun j => |c j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hcs0 : 0 ≤ cs := by positivity
  let Yo : Set M.Xc := {x | ∃ z ∈ D.Xo, M.proj z = x}
  have hYo : ∀ j, ∀ x ∈ (P.chart j).source, x ∈ Yo ↔ P.chart j x ∉ coordDiv (S j) := by
    intro j x hx
    obtain ⟨z, hz, rfl⟩ := M.surj x
    exact (mem_Yo hz).trans (had j z hz hx).not
  have hr1' : ∀ x ∈ Yo, 1 ≤ rf x + cs := by
    rintro _ ⟨z, hz, rfl⟩
    linarith [hr1 z hz]
  have hk' : ∀ j, ∀ t ∈ (P.chart j).target \ coordDiv (S j),
      ph ((P.chart j).symm t) ≤ Cs ∧ -Cs * Real.log (rf ((P.chart j).symm t) + cs) ≤ ph ((P.chart j).symm t) ∧
        ‖fderiv ℝ (fun y => P.q j y + ph ((P.chart j).symm y)) t‖ ≤
          Cs * (rf ((P.chart j).symm t) + cs) ^ Cs * Real.exp ((rf ((P.chart j).symm t) + cs) / 2) := by
    intro j t ht
    have h1 := hr1' _ ((hYo j _ ((P.chart j).map_target ht.1)).2 (by rw [(P.chart j).right_inv ht.1]; exact ht.2))
    obtain ⟨b1, b2, b3⟩ := hk j t (hT j ▸ ht) (rf ((P.chart j).symm t) + cs) (by
      rw [hrf j t ht]
      linarith [(abs_le.1 ((hf j).2 t ht.1)).1, le_abs_self Bf, le_abs_self (c j), hcle j])
    refine ⟨b1.trans (hCle j), le_trans ?_ b2, b3.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (neg_le_neg (hCle j)) (Real.log_nonneg h1)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul (hCle j) (Real.rpow_le_rpow_of_exponent_le h1 (hCle j))
        (Real.rpow_nonneg (by linarith) _) ((hC' j).le.trans (hCle j))) (Real.exp_pos _).le
  have hpt : ∀ x ∈ Yo, ∃ j, x ∈ (P.chart j).source ∧ P.chart j x ∈ (P.chart j).target \ coordDiv (S j) := by
    intro x hx
    obtain ⟨j, hj⟩ := P.cover x
    have hs := P.mid_subset_source j (P.inner_subset_mid j hj)
    exact ⟨j, hs, (P.chart j).map_source hs, (hYo j x hs).1 hx⟩
  have hsmooth : M.atlas.SmoothOn Yo ph := by
    intro k y hy
    obtain ⟨j, hs, ht⟩ := hpt _ hy.2
    have hV : IsOpen ((P.chart j).target \ coordDiv (S j)) :=
      (P.chart j).open_target.sdiff (ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed _)
    have h1 : ContDiffOn ℝ ∞ (fun y => ph ((P.chart j).symm y)) ((P.chart j).target \ coordDiv (S j)) := by
      have h2 := hks j
      rw [← hT j] at h2
      exact (h2.sub ((P.q_smooth j).mono Set.diff_subset)).congr fun y _ => by simp
    have h3 : ContDiffAt ℝ ∞ (P.chart j ∘ (M.atlas.chart k).symm) y :=
      (((P.compat j k).1 y ⟨hy.1, hs⟩).restrictScalars (𝕜 := ℝ)).contDiffAt
    have h4 : ∀ᶠ y' in 𝓝 y, (M.atlas.chart k).symm y' ∈ (P.chart j).source :=
      ((M.atlas.chart k).continuousAt_symm hy.1).preimage_mem_nhds ((P.chart j).open_source.mem_nhds hs)
    refine (((h1.contDiffAt (hV.mem_nhds ht)).comp y h3).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [h4] with y' hy'
    simp [(P.chart j).left_inv hy']
  let R : RegChartData M.atlas :=
    { toPotentialCharts := P, S := S, Yo := Yo, mem_Yo := hYo, ph := ph, ph_smooth := hsmooth,
      u_psh := fun j => by rw [hT j]; exact hkp j
      r := fun x => rf x + cs
      one_le_r := hr1'
      f := fun j y => f j y + cs
      f_smooth := fun j => (hf j).1.add contDiffOn_const
      f_bdd := ⟨Bf + cs, fun j y hy => (abs_add_le _ _).trans
        (add_le_add ((hf j).2 y hy) (abs_of_nonneg hcs0).le)⟩
      r_chart := fun j y hy => by rw [hrf j y hy]; ring
      Clog := Cs
      Cph := Cs
      ph_le := fun x hx => by
        obtain ⟨j, hs, ht⟩ := hpt x hx
        have := (hk' j _ ht).1
        rwa [(P.chart j).left_inv hs] at this
      ph_ge := fun x hx => by
        obtain ⟨j, hs, ht⟩ := hpt x hx
        have := (hk' j _ ht).2.1
        rwa [(P.chart j).left_inv hs] at this
      Cgrad := Cs
      grad_le := fun j y hy => (hk' j y hy).2.2 }
  refine exists_tied (A := muLine Hd) hra hrs R hth ?_ fun z hz _ => hph z hz.2
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz, hz.1⟩, rfl⟩

end LevelTowerAlt.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem LevelTowerAlt.exists_tied_regular_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D), ChartPsh D (phMu Hd) → ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hd M hP => LevelTowerAlt.Reg.main Hd M hP
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationOfHodgeMetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D), ChartPsh D (phMu Hd) → ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied := by
  first | exact @LevelTowerAlt.exists_tied_regular_setting | exact LevelTowerAlt.exists_tied_regular_setting
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationOfHodgeMetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regularization_of_hodge_metric : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D), ChartPsh D (phMu Hd) → ∃ S : LogLogRegularisationSetting M D.Xo (muLine Hd), S.IsTied := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric | exact GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_regularization_of_hodge_metric <;> assumption)
end
