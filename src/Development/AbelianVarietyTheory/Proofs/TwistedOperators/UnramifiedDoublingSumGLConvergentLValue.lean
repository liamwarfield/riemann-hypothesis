module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatFunDifferentiableOn
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DoublingSeries

def ratFun (q N : ℕ) (α : Fin N → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - (α i : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
    (∏ i, (1 - (((α i)⁻¹ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X)⁻¹) *
      ∏ i ∈ Finset.Icc 1 N, (1 - (q : ℂ) ^ (-(i : ℂ)) * X ^ 2)

theorem ratFun_cpow {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (s : ℂ) :
    lFactor q α (s + 1 / 2) * lFactor q α⁻¹ (s + 1 / 2) * invNormFactor q N s =
      ratFun q N α ((q : ℂ) ^ (-s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h1 : (q : ℂ) ^ (-(s + 1 / 2)) = (q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hq0]; ring_nf
  have h2 : ∀ i : ℕ, (q : ℂ) ^ (-(2 * s + i)) = (q : ℂ) ^ (-(i : ℂ)) * ((q : ℂ) ^ (-s)) ^ 2 := fun i => by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]; push_cast; ring_nf
  simp only [lFactor, invNormFactor, ratFun, h1, h2, Pi.inv_apply, mul_assoc]

theorem ratFun_differentiableOn {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (ρ : ℝ)
    (hα : ∀ x, ‖(α x : ℂ)‖ ≤ (q : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (q : ℝ) ^ ρ) :
    DifferentiableOn ℂ (ratFun q N α) (Metric.ball 0 ((q : ℝ) ^ (1 / 2 - ρ))) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have key : ∀ a : ℂ, ‖a‖ ≤ (q : ℝ) ^ ρ → ∀ X ∈ Metric.ball (0 : ℂ) ((q : ℝ) ^ (1 / 2 - ρ)),
      1 - a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X ≠ 0 := by
    intro a ha X hX
    rw [mem_ball_zero_iff] at hX
    have hn : ‖a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X‖ < 1 := by
      rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
      rw [hre]
      calc ‖a‖ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ ≤ (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * ‖X‖ := by gcongr
        _ < (q : ℝ) ^ ρ * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (q : ℝ) ^ (1 / 2 - ρ) := by gcongr
        _ = 1 := by rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, show ρ + -(1 / 2 : ℝ) + (1 / 2 - ρ) = 0 by ring, Real.rpow_zero]
    intro h
    have e : a * (q : ℂ) ^ (-(1 / 2 : ℂ)) * X = 1 := by linear_combination -h
    rw [e, norm_one] at hn
    exact lt_irrefl _ hn
  unfold ratFun
  refine DifferentiableOn.mul (DifferentiableOn.mul ?_ ?_) ?_
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key _ (hα i).1 X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id)).inv
        fun X hX => key (((α i)⁻¹ : ℂˣ) : ℂ) (by rw [Units.val_inv_eq_inv_val, norm_inv]; exact (hα i).2) X hX
  · exact DifferentiableOn.fun_finsetProd fun i _ =>
      (differentiableOn_const (𝕜 := ℂ) (1 : ℂ)).sub ((differentiableOn_const (𝕜 := ℂ) ((q : ℂ) ^ (-(i : ℂ)))).mul (differentiableOn_id (𝕜 := ℂ).pow 2))

theorem exists_cpow_neg_eq {q : ℕ} (hq : 1 < q) (s₀ : ℝ) {z : ℂ} (hz : z ≠ 0) (hzs : ‖z‖ < (q : ℝ) ^ (-s₀)) :
    ∃ s : ℂ, s₀ < s.re ∧ (q : ℂ) ^ (-s) = z := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hl : 0 < Real.log q := Real.log_pos hq1
  refine ⟨-Complex.log z / (Real.log q : ℂ), ?_, ?_⟩
  · have e : (-Complex.log z / (Real.log q : ℂ)).re = -Real.log ‖z‖ / Real.log q := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rw [e, lt_div_iff₀ hl]
    have := Real.log_lt_log (norm_pos_iff.2 hz) hzs
    rw [Real.log_rpow (by linarith)] at this
    linarith
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
    have hl' : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hl.ne'
    rw [show (Real.log q : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z by field_simp]
    exact Complex.exp_log hz

theorem cpow_split {q : ℕ} (hq : 1 < q) (N : ℕ) (s : ℂ) {m : ℤ} (hm : 0 ≤ m) :
    (q : ℂ) ^ (-((N : ℂ) / 2 + s) * (m : ℂ)) =
      (((q : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) * ((q : ℂ) ^ (-s)) ^ m.toNat := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]
  congr 1
  have : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hm
  push_cast
  rw [this]
  ring

theorem sumAbs_nonneg {D : Type} [Fintype D] (e : D → ℤ) : 0 ≤ sumAbs e :=
  Finset.sum_nonneg fun i _ => abs_nonneg (e i)

end GlobalTheory.DoublingSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumOfDominatedOfEqNearZero
open Metric Filter Topology

namespace GlobalTheory

theorem hasSum_of_dominated_of_eq_near_zero {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ)
    (hbc : ∀ i, ‖b i‖ ≤ c i)
    (hc : ∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hnear : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by
  intro z hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hbound : ∀ i (w : ℂ), ‖b i * w ^ n i‖ ≤ c i * ‖w‖ ^ n i := by
    intro i w
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc i) (pow_nonneg (norm_nonneg w) _)
  have hsum : ∀ w : ℂ, ‖w‖ < r → Summable (fun i => b i * w ^ n i) := by
    intro w hw
    exact Summable.of_norm_bounded (hc ‖w‖ (norm_nonneg w) hw) (fun i => hbound i w)
  let F : ℂ → ℂ := fun w => ∑' i, b i * w ^ n i
  have hFd : DifferentiableOn ℂ F (ball 0 r) := by
    intro w hw
    have hw' : ‖w‖ < r := by simpa using hw
    obtain ⟨s, hws, hsr⟩ := exists_between hw'
    have hs0 : 0 ≤ s := le_trans (norm_nonneg w) hws.le
    have hd : DifferentiableOn ℂ F (ball 0 s) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := fun i => c i * s ^ n i) (hc s hs0 hsr)
        (fun i => ?_) isOpen_ball (fun i v hv => ?_)
      · exact ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn
      · refine (hbound i v).trans ?_
        have hv' : ‖v‖ < s := by simpa using hv
        have hci : 0 ≤ c i := (norm_nonneg _).trans (hbc i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv'.le _) hci
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hws))).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F (ball 0 r) := hFd.analyticOnNhd isOpen_ball
  have hRa : AnalyticOnNhd ℂ R (ball 0 r) := hR.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = R w := by
    apply Eventually.frequently
    have h1 : ∀ᶠ w in 𝓝 (0:ℂ), w ∈ ball (0:ℂ) ε := isOpen_ball.mem_nhds (mem_ball_self hε)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hw0
    have hw0' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwε : ‖w‖ < ε := by simpa using hw
    exact (hnear w hw0' hwε).tsum_eq
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hRa (convex_ball (0:ℂ) r).isPreconnected
    (mem_ball_self hr) hfreq
  have hzb : z ∈ ball (0:ℂ) r := by simpa using hz
  rw [← heq hzb]
  exact (hsum z hz).hasSum

theorem hasSum_of_dominated_of_eq_near_zero' : ∀ {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ) (R : ℂ → ℂ) (r ε : ℝ), (∀ i, ‖b i‖ ≤ c i) →
    (∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) → 0 < ε →
    DifferentiableOn ℂ R (Metric.ball 0 r) →
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) →
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) :=
  fun b c n R r ε h1 h2 h3 h4 h5 => hasSum_of_dominated_of_eq_near_zero b c n R r ε h1 h2 h3 h4 h5

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNonnegFamilyOfDifferentiableOn
open Filter Topology

namespace GlobalTheory

theorem summable_nonneg_family_of_differentiableOn {ι : Type} (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ) (hc : ∀ i, 0 ≤ c i) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hser : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => (c i : ℂ) * z ^ n i) (R z))
    (x : ℝ) (hx0 : 0 ≤ x) (hxr : x < r) : Summable (fun i => c i * x ^ n i) := by
  have hr : 0 < r := lt_of_le_of_lt hx0 hxr
  set t0 : ℝ := ε / 2 with ht0
  have ht0pos : 0 < t0 := by positivity
  have ht0ε : t0 < ε := by linarith
  have hnt0 : ‖(t0 : ℂ)‖ = t0 := by simp [abs_of_pos ht0pos]
  have hsum0 : Summable (fun i => c i * t0 ^ n i) := by
    have h := (hser (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun i => (c i : ℂ) * (t0 : ℂ) ^ n i) = fun i => ((c i * t0 ^ n i : ℝ) : ℂ) := by
      funext i; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  have hfib : ∀ m : ℕ, Summable (fun i : n ⁻¹' {m} => c i) := by
    intro m
    have h1 := (hsum0.subtype (fun i => n i = m)).mul_right (t0 ^ m)⁻¹
    refine h1.congr fun i => ?_
    have hi : n i.val = m := i.2
    simp only [Function.comp_apply]
    rw [hi, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0pos.ne'), mul_one]
  set C : ℕ → ℝ := fun m => ∑' i : n ⁻¹' {m}, c i with hC
  have hCnn : ∀ m, 0 ≤ C m := fun m => tsum_nonneg (fun i => hc i)
  have hgroup : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun m => (C m : ℂ) * z ^ m) (R z) := by
    intro z hz1 hz2
    refine ((hser z hz1 hz2).tsum_fiberwise n).congr_fun fun m => ?_
    have e1 : (∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ n i) = ∑' i : n ⁻¹' {m}, (c i : ℂ) * z ^ m :=
      tsum_congr fun i => by rw [show n i = m from i.2]
    rw [e1, tsum_mul_right, hC, Complex.ofReal_tsum]
  have hCt0 : Summable (fun m => C m * t0 ^ m) := by
    have h := (hgroup (t0 : ℂ) (by rw [hnt0]; exact ht0pos) (by rw [hnt0]; exact ht0ε)).summable
    have e : (fun m => (C m : ℂ) * (t0 : ℂ) ^ m) = fun m => ((C m * t0 ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => (C m : ℂ)) with hq
  have hqapply : ∀ (m : ℕ) (z : ℂ), q m (fun _ => z) = (C m : ℂ) * z ^ m := by
    intro m z; rw [hq, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  set t0n : NNReal := ⟨t0, ht0pos.le⟩ with ht0n
  have hrad : (t0n : ENNReal) ≤ q.radius := by
    refine q.le_radius_of_bound (∑' m, C m * t0 ^ m) fun m => ?_
    rw [show ((t0n : ℝ)) = t0 from rfl]
    have hn : ‖q m‖ = C m := by
      rw [hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hCnn m)]
    rw [hn]
    exact hCt0.le_tsum m (fun j _ => mul_nonneg (hCnn j) (pow_nonneg ht0pos.le _))
  have hradpos : 0 < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (NNReal.coe_pos.mp (show (0:ℝ) < (t0n : ℝ) from ht0pos))) hrad
  have hqball := q.hasFPowerSeriesOnBall hradpos
  have hRan : AnalyticAt ℂ R 0 := hR.analyticAt (Metric.ball_mem_nhds 0 hr)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), R z = q.sum z := by
    apply Eventually.frequently
    have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball (0 : ℂ) ε :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hb, self_mem_nhdsWithin] with z hz hz0
    have hz0' : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [mem_ball_zero_iff] at hz
    rw [FormalMultilinearSeries.sum]
    simp_rw [hqapply]
    exact ((hgroup z hz0' hz).tsum_eq).symm
  have hev := (hRan.frequently_eq_iff_eventually_eq hqball.analyticAt).mp hfreq
  have hRq : HasFPowerSeriesAt R q 0 := hqball.hasFPowerSeriesAt.congr (hev.mono fun z h => h.symm)
  set ρ : ℝ := (x + r) / 2 with hρ
  have hρpos : 0 < ρ := by linarith
  set ρn : NNReal := ⟨ρ, hρpos.le⟩ with hρn
  have hcl : DifferentiableOn ℂ R (Metric.closedBall 0 (ρn : ℝ)) :=
    hR.mono (Metric.closedBall_subset_ball (by show ρ < r; linarith))
  have hp := hcl.hasFPowerSeriesOnBall (by exact_mod_cast hρpos)
  have hpq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hRq
  rw [hpq] at hp
  have hxn : ‖(x : ℂ)‖₊ < ρn := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    show x < ρ
    linarith
  have hxmem : (x : ℂ) ∈ Metric.eball (0 : ℂ) (ρn : ENNReal) := by
    show edist (x : ℂ) 0 < ρn
    rw [edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast hxn
  have hsx := (hp.hasSum hxmem).summable
  simp_rw [hqapply] at hsx
  have hCx : Summable (fun m => C m * x ^ m) := by
    have e : (fun m => (C m : ℂ) * (x : ℂ) ^ m) = fun m => ((C m * x ^ m : ℝ) : ℂ) := by
      funext m; push_cast; rfl
    rw [e] at hsx
    exact Complex.summable_ofReal.mp hsx
  rw [← (Equiv.sigmaFiberEquiv n).summable_iff]
  refine (summable_sigma_of_nonneg fun p => ?_).mpr ⟨fun m => ?_, ?_⟩
  · exact mul_nonneg (hc _) (pow_nonneg hx0 _)
  · refine ((hfib m).mul_right (x ^ m)).congr fun i => ?_
    simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
  · refine hCx.congr fun m => ?_
    have e1 : (∑' i : {i // n i = m}, ((fun i => c i * x ^ n i) ∘ (Equiv.sigmaFiberEquiv n))
        ⟨m, i⟩) = ∑' i : n ⁻¹' {m}, c i * x ^ m :=
      tsum_congr fun i => by simp [Equiv.sigmaFiberEquiv, show n i = m from i.2]
    rw [e1, tsum_mul_right]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValue
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DoublingSeries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem isMulRightInvariant_haar [m : MeasurableSpace (GL (Fin N) k)] [hm : BorelSpace (GL (Fin N) k)]
    (μ : Measure (GL (Fin N) k)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  borelize k
  have e : m = _ := hm.measurable_eq.trans (SplitFlip.borel_GL (k := k) (n := Fin N)).measurable_eq.symm
  subst e
  exact SplitFlip.isMulRightInvariant_of_haar μ

theorem isBorelSph_unique {γ : Fin N → ℂ} {ψ ψ' : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ) (h' : IsBorelSph k γ ψ') :
    ψ = ψ' := by
  funext g
  obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
  have hb' : b ∈ borel k (Fin N) := (mem_borel _).2 hb
  have ht := fun i => (GlobalTheory.CuspRep.ParLaws.val_diagU ⟨b, hb'⟩ i).symm
  rw [h.1 _ _ hx, h'.1 _ _ hx, h.2 b hb' _ ht, h'.2 b hb' _ ht]

theorem isBorelSph_norm {α β : Fin N → ℂˣ} (hβ : ∀ x, (β x : ℂ) = ((‖(α x : ℂ)‖ : ℝ) : ℂ)) {ψ : GL (Fin N) k → ℂ}
    (h : IsBorelSph k (borelParam (resCard k) α) ψ) :
    IsBorelSph k (borelParam (resCard k) β) fun g => ((‖ψ g‖ : ℝ) : ℂ) := by
  refine ⟨fun g x hx => by simp only [h.1 g x hx], fun b hb t ht => ?_⟩
  have hq : 0 < resCard k := zero_lt_one.trans (one_lt_resCard k)
  simp only [h.2 b hb t ht, norm_prod, norm_zpow, Complex.ofReal_prod, Complex.ofReal_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  have e : (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) = ((((i : ℕ) : ℝ) - ((N : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [borelParam, borelParam, hβ, norm_mul, Complex.norm_natCast_cpow_of_pos hq, e, Complex.ofReal_re,
    Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem zonalInt_norm [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) :
    (zonalInt μK (fun g => ((‖ψ g‖ : ℝ) : ℂ)) g).im = 0 ∧ 0 ≤ (zonalInt μK (fun g => ((‖ψ g‖ : ℝ) : ℂ)) g).re ∧
      ‖zonalInt μK ψ g‖ ≤ (zonalInt μK (fun g => ((‖ψ g‖ : ℝ) : ℂ)) g).re := by
  simp only [zonalInt, integral_complex_ofReal, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨trivial, integral_nonneg fun _ => norm_nonneg _, norm_integral_le_integral_norm _⟩

theorem exists_isZonal_of_form {G X V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G X}
    {π : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (hs : fixed π K ≠ ⊥) (L : X →ₗ[ℂ] ℂ) (hL : ∀ x ∈ K, ∀ u, L (ρ x u) = L u)
    (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → L u = 0 → u = 0) :
    ∃ w : X, (∀ x ∈ K, ρ x w = w) ∧ L w = 1 ∧ GlobalTheory.SmGL.IsZonal π K fun g => L (ρ g w) := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw0 : f w ≠ 0 := fun h => hv0 (hfw.symm.trans h)
  have hEw : L w ≠ 0 := fun h => hfw0 (by rw [hE w hw' h, map_zero])
  obtain ⟨z, hz, hEz, hfz⟩ : ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ L z = 1 ∧ f z ≠ 0 :=
    ⟨(L w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], by
      rw [map_smul]; exact smul_ne_zero (inv_ne_zero hEw) hfw0⟩
  have hker : LinearMap.ker f.toLinearMap ≤ LinearMap.ker L := fun y hy => by
    have hy0 : f y = 0 := hy
    obtain ⟨y', hy', e⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK (f.toLinearMap.prod L) y fun h hh => by
      refine Prod.ext ?_ (hL h hh y)
      show f (ρ h y) = f y
      rw [f.isIntertwining, hy0, map_zero]
    have hy'' : ∀ x ∈ K, ρ x y' = y' := fun x hx => by simpa using hy' ⟨x, hx⟩
    have e1 : f y' = f y := congrArg Prod.fst e
    have e2 : L y' = L y := congrArg Prod.snd e
    have h1 := hE (y' - L y' • z) (fun x hx => by rw [map_sub, map_smul, hy'' x hx, hz x hx])
      (by rw [map_sub, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
    have h2 := congrArg f (sub_eq_zero.1 h1)
    rw [map_smul, e1, hy0, eq_comm, smul_eq_zero] at h2
    show L y = 0
    rw [← e2]
    exact h2.resolve_right hfz
  let l : Module.Dual ℂ V := (LinearMap.ker f.toLinearMap).liftQ L hker ∘ₗ
    (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hl : ∀ y, l (f y) = L y := fun y => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hf).symm (f y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker f.toLinearMap).liftQ L hker ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f y)) = _
    rw [this]; rfl
  refine ⟨z, hz, hEz, f z, fun x => ?_, l, fun x => ?_, by rw [hl, hEz], fun g => ?_⟩
  · have := f.isIntertwining _ _ (x : G) z
    rw [hz x x.2] at this
    simpa using this.symm
  · ext v
    obtain ⟨y, rfl⟩ := hf v
    have := f.isIntertwining _ _ (x : G)⁻¹ y
    simp [Module.Dual.transpose_apply, ← this, hl, hL _ (inv_mem x.2)]
  · show L (ρ g z) = _
    rw [← hl, f.isIntertwining]

theorem exists_isZonal_zonalInt [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure] (hμ : μK (KO k (Fin N)) = 1) (α : Fin N → ℂˣ)
    (ψ : GL (Fin N) k → ℂ) (hψ : IsBorelSph k (borelParam (resCard k) α) ψ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π : Representation ℂ (GL (Fin N) k) V),
      HasSatake π α ∧ GlobalTheory.SmGL.IsZonal π (KO k (Fin N)) (zonalInt μK ψ) := by
  obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := k) α
  refine ⟨_, _, _, π.ρ, hπ, ?_⟩
  obtain ⟨-, hs, S, f, hf⟩ := hπ
  haveI := isMulRightInvariant_haar μK
  have hKm : MeasurableSet (KO k (Fin N) : Set (GL (Fin N) k)) := SplitFlip.isOpen_KO.measurableSet
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  have hcont : ∀ u : S.toSubmodule, Continuous u.1.1.1 := fun u => by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x | S.toRepresentation x u = u}) := (hsm u).preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show S.toRepresentation (g⁻¹ * g) u = u by rw [inv_mul_cancel, map_one]; rfl)] with x hx
    have hx' : S.toRepresentation (g⁻¹ * x) u = u := hx
    have h1 : u.1.1.1 (g * (g⁻¹ * x)) = u.1.1.1 g := congrArg (fun z : S.toSubmodule => z.1.1.1 g) hx'
    rwa [mul_inv_cancel_left] at h1
  have hint : ∀ u : S.toSubmodule, IntegrableOn u.1.1.1 (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun u =>
    (hcont u).continuousOn.integrableOn_compact SplitFlip.isCompact_KO
  let L : S.toSubmodule →ₗ[ℂ] ℂ :=
    { toFun := fun u => ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 κ ∂μK
      map_add' := fun u v => integral_add (hint u) (hint v)
      map_smul' := fun c u => integral_const_mul c _ }
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin N), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin N), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  have hL1 : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin N), S.toRepresentation x u = u) → L u = u.1.1.1 1 := fun u h => by
    show ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 κ ∂μK = _
    rw [setIntegral_congr_fun hKm (g := fun _ => u.1.1.1 1) fun x hx => by
      simpa using hr u h 1 x hx]
    simp [Measure.real, hμ]
  have hL : ∀ x ∈ KO k (Fin N), ∀ u, L (S.toRepresentation x u) = L u := fun x hx u => by
    show ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 (κ * x) ∂μK =
      ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), u.1.1.1 κ ∂μK
    rw [← integral_indicator hKm, ← integral_indicator hKm,
      ← integral_mul_right_eq_self ((KO k (Fin N) : Set (GL (Fin N) k)).indicator u.1.1.1) x]
    congr 1
    funext κ
    by_cases h : κ ∈ KO k (Fin N)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mul_mem h hx)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((Subgroup.mul_mem_cancel_right _ hx).1 h')]
  obtain ⟨w, hw, hw1, hz⟩ := exists_isZonal_of_form hsm SplitFlip.isCompact_KO f hf hs L hL fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := (hL1 u h).symm.trans h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1
  have hw2 : IsBorelSph k (borelParam (resCard k) α) w.1.1.1 := by
    refine ⟨hr w hw, fun b hb t ht => ?_⟩
    have h1 := GlobalTheory.SatakeBound.Rep.law α w.1 b hb t ht 1
    have h2 : w.1.1.1 1 = 1 := (hL1 w hw).symm.trans hw1
    rw [h2, mul_one, mul_one] at h1
    rw [h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [borelParam, Complex.ofReal_cpow (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [isBorelSph_unique hψ hw2]
  exact hz

theorem unramified_doubling_sum : GlobalTheory.Published.UnramifiedDoublingGL →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (α : Fin N → ℂˣ) (ρ : ℝ), (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) →
  ∀ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ →
  ∀ s : ℂ, ρ - 1 / 2 < s.re →
    Summable (fun e : {e : Fin N → ℤ // Antitone e} => ‖(μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e))‖) ∧
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} => (μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)))
      (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
  intro H k _ _ _ _ _ N _ _ μK _ hμK ϖ hϖ α ρ hα ψ hψ s hs
  have hq : 1 < resCard k := one_lt_resCard k
  have hq1 : (1 : ℝ) < resCard k := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < resCard k := by linarith
  let β : Fin N → ℂˣ := fun x => Units.mk0 ((‖(α x : ℂ)‖ : ℝ) : ℂ) (by simp)
  have hβ : ∀ x, (β x : ℂ) = ((‖(α x : ℂ)‖ : ℝ) : ℂ) := fun x => rfl
  have hβn : ∀ x, ‖(β x : ℂ)‖ = ‖(α x : ℂ)‖ := fun x => by rw [hβ]; simp
  obtain ⟨ψ', hψ', hM⟩ : ∃ ψ' : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) β) ψ' ∧
      ∀ g, (zonalInt μK ψ' g).im = 0 ∧ 0 ≤ (zonalInt μK ψ' g).re ∧ ‖zonalInt μK ψ g‖ ≤ (zonalInt μK ψ' g).re :=
    ⟨_, isBorelSph_norm hβ hψ, zonalInt_norm μK ψ⟩
  have hZ : ∀ (γ : Fin N → ℂˣ) (φ : GL (Fin N) k → ℂ), IsBorelSph k (borelParam (resCard k) γ) φ →
      ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re → HasSum (fun e : {e : Fin N → ℤ // Antitone e} =>
        (μK.real (cell k (Fin N) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) *
          zonalInt μK φ (torusElt k (Fin N) ϖ e)))
        (lFactor (resCard k) γ (s + 1 / 2) * lFactor (resCard k) γ⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
    intro γ φ hφ
    obtain ⟨V, _, _, π, hπ, hz⟩ := exists_isZonal_zonalInt μK hμK γ φ hφ
    exact GlobalTheory.Published.UnramifiedDoublingGL.hasSum H k N μK hμK hϖ hπ hz
  let n : {e : Fin N → ℤ // Antitone e} → ℕ := fun e => (sumAbs e.1).toNat
  let wR : {e : Fin N → ℤ // Antitone e} → ℝ := fun e =>
    μK.real (cell k (Fin N) ϖ e) * (resCard k : ℝ) ^ (-((N : ℝ) / 2) * (sumAbs e.1 : ℝ))
  have hw0 : ∀ e, 0 ≤ wR e := fun e => mul_nonneg measureReal_nonneg (Real.rpow_nonneg hq0.le _)
  let b : {e : Fin N → ℤ // Antitone e} → ℂ := fun e => (wR e : ℂ) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)
  let c : {e : Fin N → ℤ // Antitone e} → ℝ := fun e => wR e * (zonalInt μK ψ' (torusElt k (Fin N) ϖ e)).re
  have hterm : ∀ (e : {e : Fin N → ℤ // Antitone e}) (s : ℂ) (u : ℂ),
      (μK.real (cell k (Fin N) ϖ e) : ℂ) * ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * u) =
        ((wR e : ℂ) * u) * ((resCard k : ℂ) ^ (-s)) ^ n e := by
    intro e s u
    have h := cpow_split hq N s (sumAbs_nonneg e.1)
    rw [h]
    simp only [wR, Complex.ofReal_mul]
    push_cast
    ring
  have hbc : ∀ e, ‖b e‖ ≤ c e := fun e => by
    simp only [b, c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 e)]
    exact mul_le_mul_of_nonneg_left (hM _).2.2 (hw0 e)
  have hc0 : ∀ e, 0 ≤ c e := fun e => mul_nonneg (hw0 e) (hM _).2.1
  have hcb : ∀ e, (wR e : ℂ) * zonalInt μK ψ' (torusElt k (Fin N) ϖ e) = (c e : ℂ) := fun e => by
    have h := (hM (torusElt k (Fin N) ϖ e)).1
    simp only [c, Complex.ofReal_mul]
    congr 1
    exact Complex.ext (by simp) (by simp [h])
  have hbα : ∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ := hα
  have hbβ : ∀ x, ‖(β x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(β x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ := fun x => by
    rw [hβn]; exact hα x
  have dα := ratFun_differentiableOn hq N α ρ hbα
  have dβ := ratFun_differentiableOn hq N β ρ hbβ

  have near : ∀ (γ : Fin N → ℂˣ) (φ : GL (Fin N) k → ℂ), IsBorelSph k (borelParam (resCard k) γ) φ →
      ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε →
        HasSum (fun e => ((wR e : ℂ) * zonalInt μK φ (torusElt k (Fin N) ϖ e)) * z ^ n e)
          (ratFun (resCard k) N γ z) := by
    intro γ φ hφ
    obtain ⟨s₀, h⟩ := hZ γ φ hφ
    refine ⟨(resCard k : ℝ) ^ (-s₀), Real.rpow_pos_of_pos hq0 _, fun z hz hzε => ?_⟩
    obtain ⟨s', hs', rfl⟩ := exists_cpow_neg_eq hq s₀ (norm_pos_iff.1 hz) hzε
    have := h s' hs'
    rw [ratFun_cpow hq N γ s'] at this
    exact (funext fun e => hterm e s' _) ▸ this
  obtain ⟨εα, hεα, hnα⟩ := near α ψ hψ
  obtain ⟨εβ, hεβ, hnβ⟩ := near β ψ' hψ'
  have hsum := GlobalTheory.summable_nonneg_family_of_differentiableOn c n (ratFun (resCard k) N β) _ εβ hc0 hεβ dβ fun z h1 h2 => by
    have := hnβ z h1 h2
    simpa only [hcb] using this
  have hid := GlobalTheory.hasSum_of_dominated_of_eq_near_zero' b c n (ratFun (resCard k) N α) _ εα hbc hsum hεα dα hnα
  have hz : ‖(resCard k : ℂ) ^ (-s)‖ = (resCard k : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have hzr : ‖(resCard k : ℂ) ^ (-s)‖ < (resCard k : ℝ) ^ (1 / 2 - ρ) := by
    rw [hz, Real.rpow_lt_rpow_left_iff hq1]
    linarith
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun e => norm_nonneg _) (fun e => ?_) (hsum _ (norm_nonneg _) hzr)
    rw [hterm, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc e) (pow_nonneg (norm_nonneg _) _)
  · have := hid _ hzr
    rw [← ratFun_cpow hq N α s] at this
    exact (funext fun e => hterm e s _) ▸ this

end GlobalTheory.DoublingSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValueStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_doubling_sum_GL_convergent_L_value : GlobalTheory.Published.UnramifiedDoublingGL →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 →
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (α : Fin N → ℂˣ) (ρ : ℝ), (∀ x, ‖(α x : ℂ)‖ ≤ (resCard k : ℝ) ^ ρ ∧ ‖(α x : ℂ)‖⁻¹ ≤ (resCard k : ℝ) ^ ρ) →
  ∀ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ →
  ∀ s : ℂ, ρ - 1 / 2 < s.re →
    Summable (fun e : {e : Fin N → ℤ // Antitone e} => ‖(μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e))‖) ∧
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} => (μK.real (cell k (Fin N) ϖ e) : ℂ) *
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s) * (sumAbs e.1 : ℂ)) * zonalInt μK ψ (torusElt k (Fin N) ϖ e)))
      (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) * invNormFactor (resCard k) N s) := by
  first | exact @GlobalTheory.DoublingSeries.unramified_doubling_sum | exact GlobalTheory.DoublingSeries.unramified_doubling_sum | (intros; apply GlobalTheory.DoublingSeries.unramified_doubling_sum <;> assumption)
end
