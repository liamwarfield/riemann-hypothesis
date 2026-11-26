module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferentiableOnAvg
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IntegrableAbsThetaToReal
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ}

def thS (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ℂ := ∑' ξ, f (invPt V h ξ)

theorem leftInv_thS (V : HSp D) (f : Mx D V.rank n → ℂ) : LeftInv (GQ V) (thS V f) := by
  intro γ hγ h
  obtain ⟨δ, -, hδ⟩ : ∃ δ : GL (Fin V.rank) D.host.E, _ ∧ Formalism.UG.bc (incA D) δ = Formalism.L2.Theta.matHom V γ⁻¹ := inv_mem hγ
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    ⟨fun ξ => δ.1 * ξ, fun ξ => δ⁻¹.1 * ξ, fun ξ => by simp, fun ξ => by simp⟩
  have h1 : Formalism.L2.Theta.mt V γ⁻¹ = δ.1.map (incA D) := (congrArg Units.val hδ).symm
  have h2 : Formalism.L2.Theta.mt V (γ * h)⁻¹ = Formalism.L2.Theta.mt V h⁻¹ * Formalism.L2.Theta.mt V γ⁻¹ := by rw [mul_inv_rev]; rfl
  refine (tsum_congr fun ξ => ?_).trans (e.tsum_eq fun ξ => f (invPt V h ξ))
  simp only [invPt, e, Equiv.coe_fn_mk, h2, h1, Matrix.mul_assoc, Matrix.map_mul]

theorem enorm_thS_le (V : HSp D) (f : Mx D V.rank n → ℂ) (h : GA D V) : ‖thS V f h‖ₑ ≤ absTheta V f h :=
  enorm_tsum_le_tsum_enorm

theorem absTheta_mono (V : HSp D) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) (h : GA D V) :
    absTheta V f h ≤ absTheta V M h :=
  ENNReal.tsum_le_tsum fun _ => enorm_le_iff_norm_le.2 (hfM _)

theorem absThetaInt_mono (V : HSp D) (ν : Measure (GA D V)) {f M : Mx D V.rank n → ℂ} (hfM : ∀ x, ‖f x‖ ≤ ‖M x‖) :
    absThetaInt V ν f ≤ absThetaInt V ν M :=
  lintegral_mono fun q => absTheta_mono V hfM _

theorem absThetaInt_smul_lt (V : HSp D) (ν : Measure (GA D V)) (c : ℂ) {M : Mx D V.rank n → ℂ}
    (hM : absThetaInt V ν M < ⊤) : absThetaInt V ν (c • M) < ⊤ := by
  unfold absThetaInt
  have : ∀ q, descend (GQ V) (absTheta V (c • M)) q = ‖c‖ₑ * descend (GQ V) (absTheta V M) q := fun q =>
    GlobalTheory.AbsThetaSemi.absTheta_smul V c M q.out
  simp_rw [this]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top hM

theorem aestronglyMeasurable_thS (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {f : Mx D V.rank n → ℂ} (hf : Continuous f)
    (hfin : absThetaInt V ν f < ⊤) : AEStronglyMeasurable (descend (GQ V) (thS V f)) (autMeasure V ν) := by
  rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_thS V f).lift_descend]
  have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V f) q < ⊤ :=
    ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hf) hfin.ne
  have hae' : ∀ᵐ h ∂ν, absTheta V f h < ⊤ := by
    have := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)) hae
    filter_upwards [this] with h hh
    rwa [(leftInv_absTheta V f).descend_mk] at hh
  have := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  have : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
  have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => f (invPt V h ξ) :=
    hae'.mono fun h hh => Summable.of_enorm hh.ne
  exact aestronglyMeasurable_of_tendsto_ae (μ := ν)
    (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
    (f := fun F h => ∑ ξ ∈ F, f (invPt V h ξ))
    (fun F => (continuous_finsetSum F fun ξ _ =>
      hf.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
    (hsum.mono fun h hh => hh.hasSum)

theorem ae_absTheta_lt (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (absTheta V M) q < ⊤ :=
  ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM) hfin.ne

theorem integrable_absTheta_toReal (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {M : Mx D V.rank n → ℂ} (hM : Continuous M)
    (hfin : absThetaInt V ν M < ⊤) :
    Integrable (fun q => (descend (GQ V) (absTheta V M) q).toReal) (autMeasure V ν) :=
  integrable_toReal_of_lintegral_ne_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hM).aemeasurable hfin.ne

theorem sch_facts (hP : GlobalTheory.Published.WeilThetaConvergence) (V : HSp D) (hn : 1 ≤ n) (hr : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank)
    (θ : InfFam D) (hθ : IsInfFam θ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {M : Mx D V.rank n → ℂ}
    (hM : M ∈ schwartzA θ V.rank n) : Continuous M ∧ absThetaInt V ν M < ⊤ :=
  ⟨(GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ _ M (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ M hM)).1,
    hP D n V hn (Or.inr hr) θ hθ ν hν ⟨M, hM⟩⟩

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DHolH

variable {D : D7} {n : ℕ} {V : HSp D}

structure Fam (V : HSp D) (ν : Measure (GA D V)) (U : Set ℂ) (f : ℂ → Mx D V.rank n → ℂ) : Prop where
  diff : ∀ x, DifferentiableOn ℂ (fun z => f z x) U
  maj : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ M : Mx D V.rank n → ℂ, Continuous M ∧ absThetaInt V ν M < ⊤ ∧
    ∀ z ∈ Metric.ball z₀ ε, ∀ x, ‖f z x‖ ≤ ‖M x‖
  meas : ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (f z))) (autMeasure V ν)

def dF (f : ℂ → Mx D V.rank n → ℂ) : ℂ → Mx D V.rank n → ℂ := fun z x => deriv (fun w => f w x) z

def iF (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : ℂ → Mx D V.rank n → ℂ := fun z x => iteratedDeriv r (fun w => f w x) z

theorem iF_zero (f : ℂ → Mx D V.rank n → ℂ) : iF f 0 = f := by
  funext z x; simp [iF]

theorem iF_succ (f : ℂ → Mx D V.rank n → ℂ) (r : ℕ) : iF f (r + 1) = dF (iF f r) := by
  funext z x; simp only [iF, dF, iteratedDeriv_succ]

theorem cauchy_le {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} {r C : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall z r ⊆ U) (hC : ∀ w ∈ Metric.sphere z r, ‖g w‖ ≤ C) : ‖deriv g z‖ ≤ C / r := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ hC
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball z hr.ne']
  exact hg.mono hsub

theorem fam_hasDeriv (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) ∧
    HasDerivAt (fun z => ∫ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν)
      (∫ q, descend (GQ V) (thS V (dF f z₀)) q ∂autMeasure V ν) z₀ := by
  obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsubU : ∀ z ∈ Metric.ball z₀ r, Metric.closedBall z r ⊆ U := by
    intro z hz w hw
    apply hball
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_closedBall] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hmemM : ∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.sphere z r, w ∈ Metric.ball z₀ ε := by
    intro z hz w hw
    rw [Metric.mem_ball] at hz ⊢
    rw [Metric.mem_sphere] at hw
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < r + r := by linarith
      _ ≤ ε := by rw [hr]; linarith
  have hcb : ∀ z ∈ Metric.ball z₀ r, ∀ x, ‖dF f z x‖ ≤ ‖M x‖ / r := fun z hz x =>
    cauchy_le (hf.diff x) hr0 (hsubU z hz) fun w hw => hMb w (hmemM z hz w hw) x
  have hballU : Metric.ball z₀ r ⊆ U := fun z hz => hsubU z hz (Metric.mem_closedBall_self hr0.le)
  have hz₀r : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr0
  have hz₀ε : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε

  have hfinq := ae_absTheta_lt V ν hMc hMfin
  have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
    intro q hq
    refine Summable.of_eNorm ?_
    simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
  have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ = (descend (GQ V) (absTheta V M) q).toReal := by
    intro q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
    rw [ENNReal.tsum_toReal_eq fun ξ => eNorm_ne_top]
    simp

  have hdiff : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      HasDerivAt (fun z => descend (GQ V) (thS V (f z)) q) (descend (GQ V) (thS V (dF f z)) q) z := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
    refine hasDerivAt_tsum_of_isPreconnected (u := fun ξ => ‖M (invPt V q.out ξ)‖ / r) (hs.div_const r)
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected (fun ξ y hy => ?_) (fun ξ y hy => hcb y hy _) hz₀r ?_ hz
    · exact ((hf.diff _).differentiableAt (hU.mem_nhds (hballU hy))).hasDerivAt
    · exact Summable.of_norm_bounded hs fun ξ => hMb z₀ hz₀ε _

  have hmeas' : AEStronglyMeasurable (descend (GQ V) (thS V (dF f z₀))) (autMeasure V ν) := by
    let s : ℕ → ℂ := fun k => z₀ + ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ)
    have hs_ne : ∀ k, s k ≠ z₀ := by
      intro k h
      have : ((r / 2 / ((k : ℝ) + 1) : ℝ) : ℂ) = 0 := by simpa [s] using h
      have h2 : r / 2 / ((k : ℝ) + 1) ≠ 0 := by positivity
      exact h2 (by exact_mod_cast this)
    have hs_mem : ∀ k, s k ∈ Metric.ball z₀ r := by
      intro k
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [s, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      calc r / 2 / ((k : ℝ) + 1) ≤ r / 2 := div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        _ < r := by linarith
    have hs_lim : Tendsto s atTop (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hs_ne⟩
      have : Tendsto (fun k : ℕ => r / 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (r / 2)
        rw [mul_zero] at h0
        refine h0.congr fun k => ?_
        ring
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      simpa [s] using (tendsto_const_nhds (x := z₀)).add h2
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun k q => (s k - z₀)⁻¹ • (descend (GQ V) (thS V (f (s k))) q - descend (GQ V) (thS V (f z₀)) q))
      (fun k => ((hf.meas _ (hballU (hs_mem k))).sub (hf.meas _ hz₀)).const_smul (s k - z₀)⁻¹) ?_
    filter_upwards [hdiff] with q hq
    have hd := hq z₀ hz₀r
    exact (hasDerivAt_iff_tendsto_slope.1 hd).comp hs_lim
  refine ⟨hmeas', ?_⟩
  have hint0 : Integrable (descend (GQ V) (thS V (f z₀))) (autMeasure V ν) := by
    refine ⟨hf.meas _ hz₀, lt_of_le_of_lt (lintegral_mono fun q => ?_) (lt_of_le_of_lt (le_refl _) hMfin)⟩
    exact (enorm_thS_le V _ q.out).trans (absTheta_mono V (hMb z₀ hz₀ε) q.out)
  have hbound : ∀ᵐ q ∂autMeasure V ν, ∀ z ∈ Metric.ball z₀ r,
      ‖descend (GQ V) (thS V (dF f z)) q‖ ≤ (descend (GQ V) (absTheta V M) q).toReal / r := by
    filter_upwards [hfinq] with q hq z hz
    have hs := hsumM q hq
    have hs' : Summable fun ξ => ‖dF f z (invPt V q.out ξ)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hcb z hz _) (hs.div_const r)
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS] at *
    calc ‖∑' ξ, dF f z (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖dF f z (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
      _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ / r := hs'.tsum_le_tsum (fun ξ => hcb z hz _) (hs.div_const r)
      _ = (∑' ξ, ‖M (invPt V q.out ξ)‖) / r := tsum_div_const
      _ = _ := by rw [htsM q hq]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ hr0) (Eventually.mono (hU.mem_nhds hz₀) fun z hz => hf.meas z hz)
    hint0 hmeas' hbound ((integrable_absTheta_toReal V ν hMc hMfin).div_const r) hdiff).2

theorem fam_dF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) : Fam V ν U (dF f) := by
  refine { diff := fun x => (hf.diff x).deriv hU, maj := ?_, meas := ?_ }
  · intro z₀ hz₀
    obtain ⟨ε, hε, hball, M, hMc, hMfin, hMb⟩ := hf.maj z₀ hz₀
    refine ⟨ε / 2, by positivity, (Metric.ball_subset_ball (by linarith)).trans hball, ((2 / ε : ℝ) : ℂ) • M,
      hMc.const_smul _, absThetaInt_smul_lt V ν _ hMfin, ?_⟩
    intro z hz x
    have hsub : Metric.closedBall z (ε / 2) ⊆ U := by
      intro w hw
      apply hball
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have hmem : ∀ w ∈ Metric.sphere z (ε / 2), w ∈ Metric.ball z₀ ε := by
      intro w hw
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_sphere] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    have h := cauchy_le (hf.diff x) (by positivity : (0 : ℝ) < ε / 2) hsub fun w hw => hMb w (hmem w hw) x
    calc ‖dF f z x‖ ≤ ‖M x‖ / (ε / 2) := h
      _ = ‖(((2 / ε : ℝ) : ℂ) • M) x‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        field_simp
  · exact fun z hz => (fam_hasDeriv V ν hU hf hz).1

theorem fam_iF (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) : Fam V ν U (iF f r) := by
  induction r with
  | zero => rwa [iF_zero]
  | succ r ih => rw [iF_succ]; exact fam_dF V ν hU ih

theorem iteratedDeriv_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) (r : ℕ) :
    ∀ z ∈ U, iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) z =
      ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν := by
  have hder : ∀ r, ∀ z ∈ U, HasDerivAt (fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν)
      (⨍ q, descend (GQ V) (thS V (iF f (r + 1) z)) q ∂autMeasure V ν) z := by
    intro r z hz
    simp only [average_eq]
    rw [iF_succ]
    exact (fam_hasDeriv V ν hU (fam_iF V ν hU hf r) hz).2.const_smul _
  induction r with
  | zero => intro z _; simp [iF_zero]
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv r (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) =ᶠ[𝓝 z]
        fun z => ⨍ q, descend (GQ V) (thS V (iF f r z)) q ∂autMeasure V ν :=
      Eventually.mono (hU.mem_nhds hz) fun w hw => ih w hw
    rw [heq.deriv_eq]
    exact (hder r z hz).deriv

theorem differentiableOn_avg (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → Mx D V.rank n → ℂ} (hf : Fam V ν U f) :
    DifferentiableOn ℂ (fun z => ⨍ q, descend (GQ V) (thS V (f z)) q ∂autMeasure V ν) U := by
  intro z hz
  simp only [average_eq]
  exact ((fam_hasDeriv V ν hU hf hz).2.const_smul _).differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.Glob.DHolH
end
end

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open DHolH

theorem dHol : DHol := by
  intro hP D n V hn hr θ hθ ν hν P _ _ U hU φ h1 h2 h3 h4 h5
  intro F

  have hfacts : ∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      Continuous M ∧ absThetaInt V ν M < ⊤ ∧ ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N, M, hN, hM, hb⟩ := h5 p₀ z₀ hz₀
    obtain ⟨hMc, hMf⟩ := sch_facts hP V hn hr θ hθ ν hν hM
    exact ⟨N, M, hN, hMc, hMf, hb⟩
  have hcontx : ∀ p, ∀ z ∈ U, Continuous (φ p z) := by
    intro p z hz
    exact (h4 p).comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩
  have hfin : ∀ p, ∀ z ∈ U, absThetaInt V ν (φ p z) < ⊤ := by
    intro p z hz
    obtain ⟨N, M, hN, -, hMf, hb⟩ := hfacts p z hz
    exact lt_of_le_of_lt (absThetaInt_mono V ν (hb (p, z) (mem_of_mem_nhds hN) hz)) hMf
  have hmeas : ∀ p, ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (φ p z))) (autMeasure V ν) :=
    fun p z hz => aestronglyMeasurable_thS V ν (hcontx p z hz) (hfin p z hz)
  have hfam : ∀ p, Fam V ν U (φ p) := by
    intro p
    refine ⟨h2 p, fun z₀ hz₀ => ?_, hmeas p⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p z₀ hz₀
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hv
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hb₂, M, hMc, hMf, ?_⟩
    intro z hz x
    have hzv : z ∈ v := hb₁ (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hzU : z ∈ U := hb₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact hb (p, z) (huv ⟨mem_of_mem_nhds hu, hzv⟩) hzU x
  refine ⟨?_, fun p => ?_, fun p r z hz => ?_⟩
  ·
    rintro ⟨p₀, z₀⟩ ⟨-, hz₀⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p₀ z₀ hz₀
    have hfinq := ae_absTheta_lt V ν hMc hMf
    have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
      intro q hq
      refine Summable.of_enorm ?_
      simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
    have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ =
          (descend (GQ V) (absTheta V M) q).toReal := by
      intro q hq
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
      rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
      simp
    have hs : Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := self_mem_nhdsWithin
    have hNs : N ∩ Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := inter_mem (mem_nhdsWithin_of_mem_nhds hN) hs
    have hint : ContinuousWithinAt (fun pz : P × ℂ => ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν)
        (Set.univ ×ˢ U) (p₀, z₀) := by
      refine continuousWithinAt_of_dominated (bound := fun q => (descend (GQ V) (absTheta V M) q).toReal) ?_ ?_
        (integrable_absTheta_toReal V ν hMc hMf) ?_
      · exact Eventually.mono hs fun pz hpz => hmeas pz.1 pz.2 hpz.2
      · refine Eventually.mono hNs fun pz hpz => ?_
        filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hs' : Summable fun ξ => ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
        calc ‖∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
          _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ := hs'.tsum_le_tsum (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
          _ = _ := htsM q hq
      · filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hon : ContinuousOn (fun pz : P × ℂ => ∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)) (N ∩ Set.univ ×ˢ U) :=
          continuousOn_tsum (fun ξ => (h3 _).mono Set.inter_subset_right) hs1
            (fun ξ pz hpz => hb pz hpz.1 hpz.2.2 _)
        exact (hon.continuousWithinAt ⟨mem_of_mem_nhds hN, ⟨Set.mem_univ _, hz₀⟩⟩).mono_of_mem_nhdsWithin hNs
    have : (fun pz : P × ℂ => F pz.1 pz.2) = fun pz => ((autMeasure V ν) Set.univ).toReal⁻¹ •
        ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν := by
      funext pz
      simp only [F, average_eq]
      rfl
    rw [this]
    exact hint.const_smul ((autMeasure V ν) Set.univ).toReal⁻¹
  · exact differentiableOn_avg V ν hU (hfam p)
  · exact iteratedDeriv_avg V ν hU (hfam p) r z hz

end PositivityTheory.Rg.Sw.Glob
