module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ProjectiveLineZeroFormHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace PolydiscLelongLimit

theorem hypIncl_mem_ball {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · simp only [mem_ball_zero_iff, pi_norm_lt_iff hr, Fin.forall_fin_succ, hypIncl, Fin.cons_zero,
      Fin.cons_succ, norm_zero, hr, true_and]

theorem extend_by_zero {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by
  have h0 : ∀ τ ∉ Metric.closedBall (0 : Fin D → ℂ) ρ,
      (Metric.ball (0 : Fin D → ℂ) r).indicator χ τ = 0 := by
    intro τ hτ
    by_cases hU : τ ∈ Metric.ball (0 : Fin D → ℂ) r
    · rw [Set.indicator_of_mem hU]
      by_contra h
      exact hτ (Metric.ball_subset_closedBall (hsupp τ hU h))
    · exact Set.indicator_of_notMem hU _
  have heq : Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) :=
    fun τ hτ => Set.indicator_of_mem hτ _
  exact ⟨contDiff_of_contDiffOn_zero_off Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball hρ) (hχ.congr heq) h0,
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) h0,
    closure_minimal (fun τ hτ => by_contra fun h => (Function.mem_support.1 hτ) (h0 τ h))
      Metric.isClosed_closedBall, heq⟩

theorem logReg_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ F z :=
    ((ReciprocityTheory.AnForm.Osgood.osgood D U F hU hF z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun τ => ‖F τ‖ ^ 2 + ε) z := (h1.norm_sq ℝ).add contDiffAt_const
  exact ((h2.log (by positivity)).div_const 2).contDiffWithinAt

end PolydiscLelongLimit


open PolydiscLelongLimit in
theorem PolydiscLelongLimit.proof : PolydiscLelongLimit.Statement := by
  intro d m r ρ F χ ψ hρ hF hχ hsupp hψ
  obtain ⟨H, hHd, hH0, hFH⟩ := hF
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  obtain ⟨hv, hvc, hvt, hvχ⟩ := extend_by_zero hρ hχ hsupp
  set U : Set (Fin (d + 1) → ℂ) := Metric.ball 0 r with hUdef
  set v := U.indicator χ with hvdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hvU : tsupport v ⊆ U := hvt.trans (Metric.closedBall_subset_ball hρ)
  have hFd : DifferentiableOn ℂ F U :=
    (((differentiable_apply 0).pow m).differentiableOn.mul hHd).congr fun t ht => hFH t ht
  have hFne : ∀ τ ∈ U, τ 0 ≠ 0 → F τ ≠ 0 := fun τ hτ h0 => by
    rw [hFH τ hτ]; exact mul_ne_zero (pow_ne_zero _ h0) (hH0 τ hτ)
  have hdens0 : ∀ τ, τ ∉ tsupport v → densV v ψ τ = 0 := fun τ hτ => maDens_cons_eq_zero ψ hτ
  have hIon : ∀ f : (Fin (d + 1) → ℂ) → ℝ, IntegrableOn (fun z => f z * densV v ψ z) U →
      Integrable (fun z => f z * densV v ψ z) := fun f h =>
    (integrableOn_iff_integrable_of_support_subset fun z hz => by_contra fun h' =>
      (Function.mem_support.1 hz) (mul_eq_zero_of_right _ (hdens0 z fun h'' => h' (hvU h'')))).1 h

  have hgood : ∀ ε : ℝ, 0 < ε →
      Integrable (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) ∧
      maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U =
        ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
    intro ε hε
    have hP := parts_thm d ψ v (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, (logReg_contDiffOn hU hFd hε).of_le h3,
        fun k => (hψ k).of_le h3⟩
    refine ⟨hIon _ hP.2.1, ?_⟩
    calc maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U
        = maInt (Fin.cons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) v U := by
          unfold maInt
          exact setIntegral_congr_fun hU.measurableSet fun τ hτ => by
            simp only [hvχ hτ]; try rfl
      _ = maInt (Fin.cons v ψ) (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := hP.2.2.2.2.symm
      _ = ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
          unfold maInt
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ =>
            mul_eq_zero_of_right _ (hdens0 τ fun h => hτ (hvU h))

  have hL0 := log_norm_integral_formula_unit d (m : ℤ) U v ψ H ⟨hU, hv.of_le h3, hvc, hvU, hψ⟩ hHd hH0
  have hlogF : (fun z => Real.log ‖F z‖ * densV v ψ z) =
      fun z => Real.log ‖z 0 ^ (m : ℤ) * H z‖ * densV v ψ z := by
    funext z
    by_cases hz : z ∈ U
    · rw [hFH z hz, zpow_natCast]
    · rw [hdens0 z fun h => hz (hvU h), mul_zero, mul_zero]
  have hint : Integrable (fun τ => Real.log ‖F τ‖ * densV v ψ τ) := by rw [hlogF]; exact hL0.1
  have hdensI : Integrable (densV v ψ) := by
    have hP1 := parts_thm d ψ v (fun _ => (1 : ℝ)) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, contDiffOn_const, fun k => (hψ k).of_le h3⟩
    exact (hIon (fun _ => 1) hP1.2.1).congr (Eventually.of_forall fun z => one_mul _)
  obtain ⟨C, hC⟩ : ∃ C, ∀ τ ∈ tsupport v, ‖(1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1)‖ ≤ C :=
    hvc.isCompact.exists_bound_of_continuousOn fun τ hτ =>
      (continuousAt_const.mul ((((hFd.continuousOn.continuousAt (hU.mem_nhds (hvU hτ))).norm.pow 2).add
        continuousAt_const).log (by positivity : ‖F τ‖ ^ 2 + 1 ≠ 0))).continuousWithinAt

  have hlim : Tendsto (fun ε : ℝ => ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) (𝓝[>] 0)
      (𝓝 (∫ τ, Real.log ‖F τ‖ * densV v ψ τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => |Real.log ‖F τ‖ * densV v ψ τ| + C * |densV v ψ τ|)
      (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).1.aestronglyMeasurable) ?_
      (hint.abs.add (hdensI.abs.const_mul C)) ?_
    · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
      filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ tsupport v
      · have h1 := gReg_abs_le hε.1 hε.2 (hFne τ (hvU hτ) hτ0)
        have h2 := hC τ hτ
        rw [Real.norm_eq_abs] at h2
        have e : Real.log (‖F τ‖ ^ 2 + ε) / 2 = gReg ε (F τ) := by unfold gReg; ring
        have h4 : |gReg ε (F τ)| ≤ |Real.log ‖F τ‖| + C :=
          h1.trans (by linarith [le_abs_self ((1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1))])
        rw [Real.norm_eq_abs, abs_mul, abs_mul, e]
        calc |gReg ε (F τ)| * |densV v ψ τ| ≤ (|Real.log ‖F τ‖| + C) * |densV v ψ τ| :=
              mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
          _ = _ := by ring
      · rw [hdens0 τ hτ]; simp
    · filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ U
      · have hpos : 0 < ‖F τ‖ ^ 2 := pow_pos (norm_pos_iff.2 (hFne τ hτ hτ0)) 2
        have hc : Tendsto (fun ε : ℝ => ‖F τ‖ ^ 2 + ε) (𝓝[>] 0) (𝓝 (‖F τ‖ ^ 2 + 0)) :=
          (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
        rw [add_zero] at hc
        have e : Real.log ‖F τ‖ = Real.log (‖F τ‖ ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
        rw [e]
        exact (((Real.continuousAt_log hpos.ne').tendsto.comp hc).div_const 2).mul_const _
      · rw [hdens0 τ fun h => hτ (hvU h)]
        simp only [mul_zero]
        exact tendsto_const_nhds

  have hR : ∫ w in Metric.ball (0 : Fin d → ℂ) r, χ (hypIncl w) * densHyp ψ w =
      ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [setIntegral_congr_fun (g := fun w => v (hypIncl w) * densHyp ψ w)
      Metric.isOpen_ball.measurableSet fun w hw => by
      simp only [hvχ ((hypIncl_mem_ball w).2 hw)]]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
      mul_eq_zero_of_left (Set.indicator_of_notMem (mt (hypIncl_mem_ball w).1 hw) _) _
  have hlimF : ∫ τ, Real.log ‖F τ‖ * densV v ψ τ = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [hlogF, hL0.2, Int.cast_natCast]
  rw [hR, ← hlimF]
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).2.symm)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneUniformiser
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

noncomputable section

theorem isDiscreteValuationRing_localization_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hbot : q ≠ ⊥ := by
    intro h
    rw [← Ideal.height_eq_zero_iff_eq_bot] at h
    rw [h] at hq
    exact zero_ne_one hq
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]
    rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := IsLocalization.AtPrime.not_isField A hbot _
  have huniq : ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal (Localization.AtPrime q), ?_, fun P hP => ?_⟩
    · exact And.intro (isField_iff_maximalIdeal_eq.not.mp hnf) inferInstance
    have : P.IsPrime := hP.2
    exact IsLocalRing.eq_maximalIdeal (this.isMaximal_of_ne_bot hP.1)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∃! P : Ideal (Localization.AtPrime q), P ≠ ⊥ ∧ P.IsPrime := And.intro inferInstance huniq
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 4).mpr h3

theorem NormalCodimOneUniformiser.proof : NormalCodimOneUniformiser.Statement := by
  intro σ _ P Q e x hP hQ hPQ hnorm hdimP hdimQ hxQ hxP
  let π : MvPolynomial σ ℂ →+* MvPolynomial σ ℂ ⧸ P := Ideal.Quotient.mk P
  have : IsDomain (MvPolynomial σ ℂ ⧸ P) := Ideal.Quotient.isDomain P
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  have : IsNoetherianRing (MvPolynomial σ ℂ ⧸ P) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial σ ℂ ⧸ P) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by rw [hdimP]; exact WithBot.natCast_ne_bot _, by
      rw [hdimP]
      rw [← WithBot.coe_natCast, Ne, WithBot.coe_eq_top]
      exact ENat.natCast_ne_top _⟩
  set q : Ideal (MvPolynomial σ ℂ ⧸ P) := Q.map π with hqdef
  have : q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have hmem : ∀ r, π r ∈ q ↔ r ∈ Q := fun r => by
    rw [← Ideal.mem_comap, hqdef, Ideal.comap_map_mk hPQ]

  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial σ ℂ ⧸ P)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial σ ℂ ⧸ P)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ), hdimQ, hdimP] at key
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.height = n :=
    ⟨q.height.toNat, (ENat.natCast_toNat (Ideal.height_ne_top Ideal.IsPrime.ne_top')).symm⟩
  rw [hn] at key
  have hn1 : n = 1 := by
    have : ((e + n : ℕ) : WithBot ℕ∞) = ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast key
    have : e + n = e + 1 := by exact_mod_cast this
    omega
  have hht : q.height = 1 := by rw [hn, hn1]; rfl

  have : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) := hnorm
  have : IsDiscreteValuationRing (Localization.AtPrime q) :=
    isDiscreteValuationRing_localization_of_height_eq_one q hht
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q)) :=
    IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
  have hmax : ∀ y, algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) y ∈ maximalIdeal (Localization.AtPrime q) ↔ y ∈ q := fun y =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q y

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨a₀, s₀⟩, hs₀⟩ := IsLocalization.mk'_surjective q.primeCompl ϖ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hgirr : Irreducible (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π g)) := by
    have h1 : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π g) = ϖ * algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) s₀ := by
      rw [← hs₀]; exact (IsLocalization.mk'_spec (Localization.AtPrime q) (Ideal.Quotient.mk P g) s₀).symm
    rw [h1]
    exact (irreducible_mul_isUnit (IsLocalization.map_units (Localization.AtPrime q) s₀)).mpr hϖ
  have hgQ : g ∈ Q := by
    rw [← hmem, ← hmax, IsLocalRing.mem_maximalIdeal]
    exact hgirr.not_isUnit

  have hx0 : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π x) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q)), hinj.eq_iff]
    intro h
    exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := Localization.AtPrime q) hx0 hgirr
  have hxmax : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π x) ∈ maximalIdeal (Localization.AtPrime q) := (hmax _).mpr ((hmem x).mpr hxQ)
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, mul_one] at hu
      rw [IsLocalRing.mem_maximalIdeal, hu] at hxmax
      exact absurd u.isUnit hxmax
    · exact h
  obtain ⟨⟨c, d⟩, hcd⟩ := IsLocalization.mk'_surjective q.primeCompl (u : (Localization.AtPrime q))
  have hcu : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) c = (u : (Localization.AtPrime q)) * algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) d := by
    rw [← hcd]; exact (IsLocalization.mk'_spec (Localization.AtPrime q) c d).symm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (d : MvPolynomial σ ℂ ⧸ P)
  have haQ : a ∉ Q := by
    rw [← hmem, ← hmax, IsLocalRing.mem_maximalIdeal, hcu]
    exact fun h => h ((u.isUnit).mul (IsLocalization.map_units (Localization.AtPrime q) d))
  have hbQ : b ∉ Q := by
    rw [← hmem]
    change Ideal.Quotient.mk P b ∈ q → False
    rw [hb]
    exact d.2
  have hrel : b * x - a * g ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change π (b * x - a * g ^ k) = 0
    apply hinj
    simp only [map_zero, map_sub, map_mul, map_pow]
    change algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P b) * _ - algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P a) * _ = 0
    rw [hb, hcu, hu]
    ring

  have hunif := (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := Localization.AtPrime q) _).mp hgirr
  have hgen : ∀ p ∈ Q, ∃ t : MvPolynomial σ ℂ, t ∉ Q ∧ t * p ∈ P ⊔ Ideal.span {g} := by
    intro p hp
    have hpm : algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π p) ∈ maximalIdeal (Localization.AtPrime q) := (hmax _).mpr ((hmem p).mpr hp)
    rw [hunif] at hpm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hpm
    obtain ⟨⟨c', d'⟩, hcd'⟩ := IsLocalization.mk'_surjective q.primeCompl y
    obtain ⟨c₁, rfl⟩ := Ideal.Quotient.mk_surjective c'
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (d' : MvPolynomial σ ℂ ⧸ P)
    refine ⟨t, ?_, ?_⟩
    · rw [← hmem]
      change Ideal.Quotient.mk P t ∈ q → False
      rw [ht]
      exact d'.2
    · have hrel' : t * p - c₁ * g ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change π (t * p - c₁ * g) = 0
        apply hinj
        simp only [map_zero, map_sub, map_mul]
        change algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (Ideal.Quotient.mk P t) * _ - _ = 0
        have hspec : IsLocalization.mk' (Localization.AtPrime q) (Ideal.Quotient.mk P c₁) d' *
            algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) d' =
            algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime q) (π c₁) :=
          IsLocalization.mk'_spec _ _ _
        dsimp only at hcd'
        rw [ht, ← hy, ← hcd', ← hspec]
        ring
      have : t * p = (t * p - c₁ * g) + c₁ * g := by ring
      rw [this]
      exact add_mem (Ideal.mem_sup_left hrel')
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian Q : Q.FG)
  have hgenS : ∀ y ∈ S, ∃ t : MvPolynomial σ ℂ, t ∉ Q ∧ t * y ∈ P ⊔ Ideal.span {g} := fun y hy =>
    hgen y (hS ▸ Submodule.subset_span hy)
  choose! T hTQ hT using hgenS
  refine ⟨g, a, b, ∏ y ∈ S, T y, k, hgQ, hk, haQ, hbQ, ?_, hrel, fun p hp => ⟨1, ?_⟩⟩
  · rw [hQ.prod_mem_iff]
    rintro ⟨y, hy, h⟩
    exact hTQ y hy h
  · rw [pow_one]
    rw [← hS] at hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.prod_erase_mul S T hy, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hT y hy)
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hy

end

end GroundTheory.Heights₂.Heights
end
