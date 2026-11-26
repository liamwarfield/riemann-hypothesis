module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerRankCuspFormsDetWeightOneComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroBoundedSectionShiftedWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIndependentBoundedSectionsShiftedWeightLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIndependentBoundedSectionsShiftedWeightLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.QuotientMax GlobalTheory.QuotNoMax
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

noncomputable section

namespace GlobalTheory.UpperShift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section
variable (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (T : ℕ) (f : Frame X.Ψ r → ℂ)

def quotT (x : Frame X.Ψ r) : ℝ :=
  X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * thetaFac X Xa x /
    sumSq X Xa Fl x ^ ((T : ℝ) + nd X + 6 + 1 / 2)

theorem quotT_inv (hf : X.IsSec (Xa.Fp + T • Xa.L) f) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    quotT X Xa Fl T f (lact γ (rmul x b)) = quotT X Xa Fl T f x := by
  unfold quotT thetaFac sumSq
  rw [pointwiseNorm_invariance_holds r X _ _ Xa.et_sec γ hγ x hx b hb, pointwiseNorm_invariance_holds r X _ _ hf γ hγ x hx b hb,
    pointwiseNorm_invariance_holds r X _ _ Xa.firstTheta_vanishes.1.1.1 γ hγ x hx b hb,
    pointwiseNorm_invariance_holds r X _ _ Xa.secondTheta_vanishes.1.1.1 γ hγ x hx b hb]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pointwiseNorm_invariance_holds r X _ _ (Fl.s_van k).1.1.1 γ hγ x hx b hb]

theorem quotT_contOn (hf : X.IsSec (Xa.Fp + T • Xa.L) f) {A : Set (Frame X.Ψ r)} (hA : A ⊆ X.dom)
    (hS : ∀ x ∈ A, 0 < sumSq X Xa Fl x) : ContinuousOn (quotT X Xa Fl T f) A := by
  have h1 : ContinuousOn (thetaFac X Xa) X.dom :=
    (((BigB.pnorm_contOn X _ Xa.secondTheta_vanishes.1.1.1).pow 2).mul
      ((BigB.pnorm_contOn X _ Xa.firstTheta_vanishes.1.1.1).pow 2)).mul
      (((BigB.pnorm_contOn X _ Xa.et_sec).pow 2).rpow_const fun _ _ => Or.inr (by positivity))
  have h2 : ContinuousOn (sumSq X Xa Fl) X.dom :=
    continuousOn_finsetSum _ fun k _ => (BigB.pnorm_contOn X _ (Fl.s_van k).1.1.1).pow 2
  refine ContinuousOn.div ((((BigB.pnorm_contOn X _ hf).pow 2).mul h1).mono hA)
    ((h2.mono hA).rpow_const fun _ _ => Or.inr (by positivity)) fun x hx => ?_
  exact (Real.rpow_pos_of_pos (hS x hx) _).ne'

theorem quotT_near (j : Fin Fl.δ)
    (hO : (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (T + nd X + 7))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ z in 𝓝 (0 : V (nd X)),
      cpt X (Fl.xs j) z ∈ X.dom ∧ quotT X Xa Fl T f (cpt X (Fl.xs j) z) < ε := by
  have hx := Fl.xs_mem j
  obtain ⟨d, hd, ev1⟩ := sumSq_lower X Xa Fl j
  obtain ⟨C, hC, ev2⟩ := hO.exists_pos
  obtain ⟨B, hB, hBle⟩ := thetaFac_bdd X Xa
  have hc0 : Filter.Tendsto (cpt X (Fl.xs j)) (𝓝 0) (𝓝 (Fl.xs j)) := by
    have := (KU.cont_cpt X (Fl.xs j)).tendsto 0
    rwa [VanishPf.cpt_zero] at this
  have hnb := (PoinPf.isOpenDom X).mem_nhds hx
  set N := X.nfac (Xa.Fp + T • Xa.L) (Fl.xs j) + 1 with hN
  have hN0 : 0 < N := by have := BoundedSectionAlgebra.nfac_pos X hx (Xa.Fp + T • Xa.L); linarith
  have ev3 : ∀ᶠ z in 𝓝 (0 : V (nd X)), X.nfac (Xa.Fp + T • Xa.L) (cpt X (Fl.xs j) z) < N :=
    (((ExtFPf.nfac_contOn X _).continuousAt hnb).tendsto.comp hc0).eventually
      (Iio_mem_nhds (by linarith))
  set p : ℝ := (T : ℝ) + nd X + 6 + 1 / 2 with hp
  have hp0 : 0 < p := by positivity
  set K : ℝ := (C * N) ^ 2 * B / d ^ p with hK
  have hK0 : 0 < K := by positivity
  have ev4 : ∀ᶠ z in 𝓝 (0 : V (nd X)), ‖z‖ < ε / K := by
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) (div_pos hε hK0)] with z hz
    simpa using hz
  filter_upwards [ev1, ev2.bound, ev3, ev4, hc0.eventually hnb] with z h1 h2 h3 h4 hy
  refine ⟨hy, ?_⟩
  set y := cpt X (Fl.xs j) z with hydef
  rw [Real.norm_of_nonneg (by positivity)] at h2
  have hf : X.pnorm (Xa.Fp + T • Xa.L) f y ≤ C * ‖z‖ ^ (T + nd X + 7) * N :=
    mul_le_mul h2 h3.le (BoundedSectionAlgebra.nfac_pos X hy _).le (by positivity)
  have hnum : X.pnorm (Xa.Fp + T • Xa.L) f y ^ 2 * thetaFac X Xa y ≤
      (C * ‖z‖ ^ (T + nd X + 7) * N) ^ 2 * B :=
    mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg X _ _ hy) hf 2) (hBle y hy) (thetaFac_nonneg X Xa y)
      (by positivity)
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · have h5 : X.pnorm (Xa.Fp + T • Xa.L) f y ^ 2 * thetaFac X Xa y ≤ 0 := by
      rw [← h0] at hnum
      simpa using hnum
    exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg h5
      (Real.rpow_nonneg (sumSq_nonneg X Xa Fl y) _)) hε
  · have hden : d ^ p * ‖z‖ ^ (2 * (T + nd X) + 13) ≤ sumSq X Xa Fl y ^ p := by
      refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (by positivity) h1 hp0.le)
      rw [Real.mul_rpow hd.le (by positivity), ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul h0.le,
        ← Real.rpow_natCast]
      congr 2
      rw [hp]; push_cast; ring
    have h6 : quotT X Xa Fl T f y ≤ (C * ‖z‖ ^ (T + nd X + 7) * N) ^ 2 * B /
        (d ^ p * ‖z‖ ^ (2 * (T + nd X) + 13)) :=
      div_le_div₀ (by positivity) hnum (by positivity) hden
    have h7 : (C * ‖z‖ ^ (T + nd X + 7) * N) ^ 2 * B /
        (d ^ p * ‖z‖ ^ (2 * (T + nd X) + 13)) = ‖z‖ * K := by
      rw [hK]
      have : 0 < d ^ p := by positivity
      field_simp
      ring
    rw [h7] at h6
    exact h6.trans_lt ((lt_div_iff₀ hK0).mp h4)

theorem quotT_far (hf : X.IsBddSec (Xa.Fp + T • Xa.L) f)
    (hrate : 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((T : ℝ) + nd X + 6 + 1 / 2)) {A : Set (Frame X.Ψ r)} {d : ℝ}
    (hd : 0 < d) (hA : ∀ x ∈ X.dom, x ∈ A → d * Real.exp (-(2 * Xa.c * Xa.ph x)) ≤ sumSq X Xa Fl x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ X.dom, x ∈ A → X.la1 x < δ → quotT X Xa Fl T f x < ε := by
  obtain ⟨Cf, hCf⟩ := hf.2
  obtain ⟨B, hB, hBle⟩ := thetaFac_le X Xa
  obtain ⟨ca, ε0, hca, hε0, hp1⟩ := Xa.p1
  have hβ := hrate
  set p : ℝ := (T : ℝ) + nd X + 6 + 1 / 2 with hp
  have hp0 : 0 < p := by positivity
  set β : ℝ := 4 / (Xa.g0 : ℝ) - 2 * Xa.c * p with hβdef
  set K : ℝ := (max Cf 1) ^ 2 * B / d ^ p with hK
  have hK0 : 0 < K := by positivity
  set M : ℝ := K / (ε * β) with hM
  have hM0 : 0 < M := by positivity
  refine ⟨min ε0 (Real.sqrt (ca / M)), lt_min hε0 (Real.sqrt_pos.mpr (by positivity)),
    fun x hx hxA hl => ?_⟩
  have hlpos : 0 < X.la1 x := ModeHalfC.first_minimum_pos X hx (BigB.lam_ne X Xa)
  have hph : ca / X.la1 x ^ 2 ≤ Xa.ph x := hp1 x hx (lt_of_lt_of_le hl (min_le_left _ _))
  have hl2 : X.la1 x ^ 2 < ca / M :=
    (Real.lt_sqrt hlpos.le).mp (lt_of_lt_of_le hl (min_le_right _ _))
  have hbig : M < Xa.ph x := by
    refine lt_of_lt_of_le ?_ hph
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ hM0] at hl2
    linarith
  have hnum : X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * thetaFac X Xa x ≤
      (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) :=
    mul_le_mul (pow_le_pow_left₀ (pnorm_nonneg X _ _ hx) ((hCf x hx).trans (le_max_left _ _)) 2)
      (hBle x hx) (thetaFac_nonneg X Xa x) (by positivity)
  have hden : d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p) ≤ sumSq X Xa Fl x ^ p := by
    refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow (by positivity) (hA x hx hxA) hp0.le)
    rw [Real.mul_rpow hd.le (Real.exp_pos _).le, ← Real.exp_mul]
  have h6 : quotT X Xa Fl T f x ≤ (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) /
      (d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p)) :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  have h7 : (max Cf 1) ^ 2 * (B * Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x)) /
      (d ^ p * Real.exp (-(2 * Xa.c * Xa.ph x) * p)) = K / Real.exp (β * Xa.ph x) := by
    have e : Real.exp (-(2 * Xa.c * Xa.ph x) * p) =
        Real.exp (-(4 / (Xa.g0 : ℝ)) * Xa.ph x) * Real.exp (β * Xa.ph x) := by
      rw [← Real.exp_add]; congr 1; rw [hβdef]; ring
    have : 0 < d ^ p := by positivity
    rw [e, hK]
    field_simp
  rw [h7] at h6
  refine h6.trans_lt ?_
  rw [div_lt_iff₀ (Real.exp_pos _)]
  have h8 := Real.add_one_le_exp (β * Xa.ph x)
  rw [hM, div_lt_iff₀ (by positivity)] at hbig
  nlinarith

theorem exists_maxT (hf : X.IsBddSec (Xa.Fp + T • Xa.L) f)
    (hrate : 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((T : ℝ) + nd X + 6 + 1 / 2))
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (T + nd X + 7))
    (hpos : ∃ x ∈ X.dom, 0 < quotT X Xa Fl T f x) :
    ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < quotT X Xa Fl T f x0 ∧
      ∀ x ∈ X.dom, quotT X Xa Fl T f x ≤ quotT X Xa Fl T f x0 := by
  obtain ⟨x1, hx1, hε⟩ := hpos
  have hρ : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧
      IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
        x = lact γ (rmul (cpt X (Fl.xs j) z') b)} ∧
      ∀ z ∈ Metric.ball (0 : V (nd X)) ρ, cpt X (Fl.xs j) z ∈ X.dom ∧
        quotT X Xa Fl T f (cpt X (Fl.xs j) z) < quotT X Xa Fl T f x1 := by
    intro j
    obtain ⟨ρ0, hρ0, hop⟩ := sat_open X (Fl.xs_mem j)
    obtain ⟨ρ1, hρ1, h1⟩ := Metric.eventually_nhds_iff_ball.mp (quotT_near X Xa Fl T f j (hO j) hε)
    exact ⟨min ρ0 ρ1, lt_min hρ0 hρ1, hop _ (min_le_left _ _),
      fun z hz => h1 z (Metric.ball_subset_ball (min_le_right _ _) hz)⟩
  choose ρ hρ0 hop hsm using hρ
  set U : Set (Frame X.Ψ r) := ⋃ j, {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
    ∃ z' ∈ Metric.ball (0 : V (nd X)) (ρ j), x = lact γ (rmul (cpt X (Fl.xs j) z') b)} with hUdef
  have hU : IsOpen U := isOpen_iUnion hop
  have hxs : ∀ j, Fl.xs j ∈ U := fun j => Set.mem_iUnion.mpr
    ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, 0, Metric.mem_ball_self (hρ0 j), by
      rw [ExtFPf.rmul_oneF, KU.lact_one, VanishPf.cpt_zero]⟩
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    obtain ⟨j, γ', hγ', b', hb', z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨j, γ * γ', X.Γ.mul_mem hγ hγ', rmul b' b, ExtFPf.mul_mem X hb' hb,
      z, hz, ?_⟩
    rw [← PoinPf.lact_rmul', KU.lact_lact, ExtFPf.rmul_assoc]
  have hUsm : ∀ x ∈ U, quotT X Xa Fl T f x < quotT X Xa Fl T f x1 := by
    intro x hx
    obtain ⟨j, γ', hγ', b', hb', z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    rw [quotT_inv X Xa Fl T f hf.1 hγ' (hsm j z hz).1 hb']
    exact (hsm j z hz).2
  obtain ⟨d, hd, hfar⟩ := sumSq_far X Xa Fl hU hxs hsat
  obtain ⟨δ, hδ, hsmall⟩ := quotT_far X Xa Fl T f hf hrate (A := Uᶜ) hd hfar hε
  obtain ⟨Kc, hKc, hKsub, hrep⟩ := reductionTheory_holds r X δ hδ
  have hSpos : ∀ x ∈ Kc \ U, 0 < sumSq X Xa Fl x := fun x hx =>
    lt_of_lt_of_le (by positivity) (hfar x (hKsub hx.1) hx.2)
  have hmove : ∀ x ∈ X.dom, quotT X Xa Fl T f x1 ≤ quotT X Xa Fl T f x →
      ∃ y ∈ Kc \ U, quotT X Xa Fl T f y = quotT X Xa Fl T f x := by
    intro x hx hle
    have hxU : x ∉ U := fun h => absurd (hUsm x h) (not_lt.mpr hle)
    have hl : δ ≤ X.la1 x := by
      by_contra h
      exact absurd (hsmall x hx hxU (not_le.mp h)) (not_lt.mpr hle)
    obtain ⟨γ, hγ, b, hb, hy⟩ := hrep x hx hl
    have he := quotT_inv X Xa Fl T f hf.1 hγ hx hb
    exact ⟨_, ⟨hy, fun h => absurd (he ▸ hUsm _ h) (not_lt.mpr hle)⟩, he⟩
  obtain ⟨y1, hy1, he1⟩ := hmove x1 hx1 le_rfl
  obtain ⟨x0, hx0, hmax⟩ := (hKc.diff hU).exists_isMaxOn ⟨y1, hy1⟩
    (quotT_contOn X Xa Fl T f hf.1 (fun x hx => hKsub hx.1) hSpos)
  have hge : quotT X Xa Fl T f x1 ≤ quotT X Xa Fl T f x0 := he1 ▸ hmax hy1
  refine ⟨x0, hKsub hx0.1, ?_, hε.trans_le hge, fun x hx => ?_⟩
  · by_contra h
    push Not at h
    have h0 := hSpos x0 hx0
    simp [sumSq, Data.pnorm, h] at h0
  · rcases le_or_gt (quotT X Xa Fl T f x1) (quotT X Xa Fl T f x) with hle | hlt
    · obtain ⟨y, hy, he⟩ := hmove x hx hle
      exact he ▸ hmax hy
    · exact hlt.le.trans hge

end

theorem mainT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (T : ℕ) (f : Frame X.Ψ r → ℂ), 0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * ((T : ℝ) + nd X + 6 + 1 / 2) → X.IsBddSec (Xa.Fp + T • Xa.L) f → (∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (T + nd X + 7)) → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((T : ℝ) + nd X + 6 + 1 / 2); (∃ x ∈ X.dom, 0 < Φ x) → ∃ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) ∧ 0 < Φ x0 ∧ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  intro E _ _ _ r X Xa Fl T f hrate hf hO Φ hpos
  have he : Φ = quotT X Xa Fl T f := by
    funext x
    simp only [Φ, quotT, thetaFac, sumSq, mul_assoc]
  rw [he] at hpos ⊢
  exact exists_maxT X Xa Fl T f hf hrate hO hpos

theorem no_pos_maxT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (T : ℕ) (f : Frame X.Ψ r → ℂ), X.IsSec (Xa.Fp + T • Xa.L) f → let Φ : Frame X.Ψ r → ℝ := fun x => X.pnorm (Xa.Fp + T • Xa.L) f x ^ 2 * X.pnorm ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 x ^ 2 * X.pnorm (2 • Xa.L - Xa.de) Xa.th1 x ^ 2 * (X.pnorm ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et x ^ 2) ^ ((1 : ℝ) / (Xa.i * (Xa.g0 / 2) : ℕ)) / (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ ((T : ℝ) + nd X + 6 + 1 / 2); ∀ x0 ∈ X.dom, (∃ k, Fl.s k x0 ≠ 0) → 0 < Φ x0 → ¬ ∀ x ∈ X.dom, Φ x ≤ Φ x0 := by
  intro E _ _ _ r X Xa Fl T f hf Φ x0 hx0 ⟨k0, hk0⟩ hpos hmax
  have hU : IsOpen (OmF X x0) := OntoB.isOpen_OmF X x0
  have h0U : (0 : V (nd X)) ∈ OmF X x0 := by show cpt X x0 0 ∈ X.dom; rw [IW.cpt_zero]; exact hx0
  set n1 : ℝ := ((Xa.i * (Xa.g0 / 2) : ℕ) : ℝ) with hn1
  have hn1p : 0 < n1 := by
    obtain ⟨g2, hg2⟩ := Xa.genus_even
    have h1 := Xa.i_pos
    have h2 := Xa.genus_pos
    have h3 : 1 ≤ Xa.g0 / 2 := by omega
    rw [hn1]
    have : 1 ≤ Xa.i * (Xa.g0 / 2) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have hz : ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P x0 = 0 → X.pnorm la P x0 ^ 2 = 0 := by
    intro la P h
    rw [OW.pnorm_eq, h]; simp
  have hf0 : f x0 ≠ 0 := fun h => by
    simp only [Φ, hz _ _ h, zero_mul, zero_div, lt_irrefl] at hpos
  have h20 : Xa.th2 x0 ≠ 0 := fun h => by
    simp only [Φ, hz _ _ h, zero_mul, mul_zero, zero_div, lt_irrefl] at hpos
  have h10 : Xa.th1 x0 ≠ 0 := fun h => by
    simp only [Φ, hz _ _ h, zero_mul, mul_zero, zero_div, lt_irrefl] at hpos
  have he0 : Xa.et x0 ≠ 0 := fun h => by
    have : (0 : ℝ) ^ ((1 : ℝ) / n1) = 0 := Real.zero_rpow (by positivity)
    simp only [Φ, hz _ _ h, ← hn1, this, mul_zero, zero_div, lt_irrefl] at hpos
  have hlog : ∀ x ∈ X.dom, f x ≠ 0 → Xa.th2 x ≠ 0 → Xa.th1 x ≠ 0 → Xa.et x ≠ 0 → Fl.s k0 x ≠ 0 →
      0 < Φ x ∧ Real.log (Φ x) = Real.log (Complex.normSq (f x)) + Real.log (Complex.normSq (Xa.th2 x)) +
      Real.log (Complex.normSq (Xa.th1 x)) + (1 / n1) * Real.log (Complex.normSq (Xa.et x)) +
      (-((T : ℝ) + nd X + 6 + 1 / 2)) * Real.log (∑ k, Complex.normSq (Fl.s k x)) +
      (1 / 2) * phla X Xa.L x := by
    intro x hx a1 a2 a3 a4 a5
    have hp : ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P x ≠ 0 → 0 < X.pnorm la P x ^ 2 := by
      intro la P h
      rw [OW.pnorm_sq X la P hx]
      exact mul_pos (Complex.normSq_pos.2 h) (Real.exp_pos _)
    have hsp := OW.sums_pos Fl a5
    have hS : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := by
      rw [OW.sum_pnorm_sq X _ _ hx]; exact mul_pos hsp (Real.exp_pos _)
    have p1 := hp (Xa.Fp + T • Xa.L) f a1
    have p2 := hp ((nd X + 4) • Xa.L - Xa.Fp) Xa.th2 a2
    have p3 := hp (2 • Xa.L - Xa.de) Xa.th1 a3
    have p4 := hp ((Xa.i * (Xa.g0 / 2)) • Xa.de) Xa.et a4
    have p5 := Real.rpow_pos_of_pos p4 (1 / n1)
    have p6 := Real.rpow_pos_of_pos hS ((T : ℝ) + nd X + 6 + 1 / 2)
    refine ⟨div_pos (mul_pos (mul_pos (mul_pos p1 p2) p3) p5) p6, ?_⟩
    simp only [Φ]
    rw [Real.log_div (mul_pos (mul_pos (mul_pos p1 p2) p3) p5).ne' p6.ne',
      Real.log_mul (mul_pos (mul_pos p1 p2) p3).ne' p5.ne', Real.log_mul (mul_pos p1 p2).ne' p3.ne',
      Real.log_mul p1.ne' p2.ne', Real.log_rpow p4, Real.log_rpow hS,
      BigC.log_pnorm_sq X hx a1, BigC.log_pnorm_sq X hx a2, BigC.log_pnorm_sq X hx a3,
      BigC.log_pnorm_sq X hx a4, OW.sum_pnorm_sq X _ _ hx, Real.log_mul hsp.ne' (Real.exp_pos _).ne',
      Real.log_exp, OW.phla_add_nsmul X hx, BigC.phla_sub X hx, BigC.phla_sub X hx,
      BigC.phla_nsmul X hx, BigC.phla_nsmul X hx, BigC.phla_nsmul X hx, ← hn1]
    push_cast
    field_simp
    ring
  have d1 := OntoB.hol_comp X x0 hf.1
  have d2 := OntoB.hol_comp X x0 Xa.secondTheta_vanishes.1.1.1.1
  have d3 := OntoB.hol_comp X x0 Xa.firstTheta_vanishes.1.1.1.1
  have d4 := OntoB.hol_comp X x0 Xa.et_sec.1
  have d5 := fun k => OntoB.hol_comp X x0 (OW.s_diffOn Fl k)
  have hc0 : cpt X x0 0 = x0 := IW.cpt_zero X x0
  have ev : ∀ {P : Frame X.Ψ r → ℂ}, DifferentiableOn ℂ (fun z => P (cpt X x0 z)) (OmF X x0) → P x0 ≠ 0 →
      ∀ᶠ z in 𝓝 (0 : V (nd X)), P (cpt X x0 z) ≠ 0 := fun hP h =>
    (hP.continuousOn.continuousAt (hU.mem_nhds h0U)).eventually_ne (by rw [hc0]; exact h)
  refine no_localMax hU h0U (a := fun z => f (cpt X x0 z)) (b := fun z => Xa.th2 (cpt X x0 z))
    (c := fun z => Xa.th1 (cpt X x0 z)) (d := fun z => Xa.et (cpt X x0 z)) d1 d2 d3 d4
    (by simpa only [hc0] using hf0) (by simpa only [hc0] using h20) (by simpa only [hc0] using h10)
    (by simpa only [hc0] using he0) (s := fun k z => Fl.s k (cpt X x0 z)) d5 (k0 := k0)
    (by simpa only [hc0] using hk0) (φ := fun z => phla X Xa.L (cpt X x0 z))
    ((IW.phla_cpt_cdAt X x0 h0U Xa.L).of_le HE.two_le_inf)
    (fun ξ hξ => Xa.posL x0 hx0 0 h0U ξ hξ) (1 / n1) (-((T : ℝ) + nd X + 6 + 1 / 2)) ?_
  filter_upwards [hU.mem_nhds h0U, ev d1 hf0, ev d2 h20, ev d3 h10, ev d4 he0, ev (d5 k0) hk0]
    with z hz a1 a2 a3 a4 a5
  obtain ⟨q1, q2⟩ := hlog _ hz a1 a2 a3 a4 a5
  obtain ⟨-, q3⟩ := hlog _ hx0 hf0 h20 h10 he0 hk0
  rw [hc0, ← q2, ← q3]
  exact Real.log_le_log q1 (hmax _ hz)

theorem rate_shift {X : Data E r} (Xa : ArchInM X) :
    0 < 4 / (Xa.g0 : ℝ) - 2 * Xa.c * (((Xa.T + (nd X + 4) : ℕ) : ℝ) + nd X + 6 + 1 / 2) := by
  have hg : (1 : ℝ) ≤ Xa.g0 := by exact_mod_cast Xa.genus_pos
  have hc := Xa.c_pos
  have hT : (2 * nd X : ℝ) + 11 ≤ Xa.T := by
    have h1 := Xa.T_ge
    have h2 := Xa.n_ge
    have : 2 * nd X + 11 ≤ Xa.T := by nlinarith
    exact_mod_cast this
  have hn : (0 : ℝ) ≤ nd X := Nat.cast_nonneg _
  have h1 : (Xa.T : ℝ) * Xa.c * Xa.g0 ≤ 1 := Xa.Tcg0
  set y : ℝ := Xa.c * Xa.g0 with hy
  have hy0 : 0 < y := by positivity
  have h2 : y * (2 * nd X + 21 / 2) < y * Xa.T := mul_lt_mul_of_pos_left (by linarith) hy0
  have h3 : 2 * y * ((Xa.T : ℝ) + 2 * nd X + 21 / 2) < 4 := by nlinarith
  have h4 : 4 / (Xa.g0 : ℝ) - 2 * Xa.c * (((Xa.T + (nd X + 4) : ℕ) : ℝ) + nd X + 6 + 1 / 2) =
      (4 - 2 * y * ((Xa.T : ℝ) + 2 * nd X + 21 / 2)) / Xa.g0 := by
    rw [hy]; push_cast; field_simp; ring
  rw [h4]
  exact div_pos (by linarith) (by linarith)

end GlobalTheory.UpperShift

namespace GlobalTheory.UpperShift

open GlobalTheory.UpperModel GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem upper_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + (Xa.T + (nd X + 4)) • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 3 * nd X + 10).choose (nd X) := by
  intro E _ _ _ r X Xa Fl m f hf hind
  by_contra hm
  obtain ⟨u, hu, hO⟩ := exists_comb Fl (Xa.T + (nd X + 4) + nd X + 6) m f (fun q => (hf q).1.1) (by
    rw [show Xa.T + (nd X + 4) + nd X + 6 + nd X = Xa.T + 3 * nd X + 10 by ring]; omega)
  have hg := isBddSec_sum X hf u
  have hg0 : ∃ x ∈ X.dom, ∑ q, u q * f q x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (hind u h)
  obtain ⟨k, hk⟩ := exists_s_ne Fl
  have d1 := hg.1.1
  have d2 := Xa.secondTheta_vanishes.1.1.1.1
  have d3 := Xa.firstTheta_vanishes.1.1.1.1
  have d4 := Xa.et_sec.1
  have d5 := (Fl.s_van k).1.1.1.1
  obtain ⟨x, hx, hne⟩ := exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5
    (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3
      (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
  obtain ⟨x0, hx0, hs0, hpos, hmax⟩ := mainT E r X Xa Fl (Xa.T + (nd X + 4)) _ (rate_shift Xa) hg hO ⟨x, hx, by
    have p1 := pnorm_pos X (Xa.Fp + (Xa.T + (nd X + 4)) • Xa.L) (P := fun x => ∑ q, u q * f q x) hx h1
    have p2 := pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2
    have p3 := pnorm_pos X (2 • Xa.L - Xa.de) hx h3
    have p4 := pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4
    have p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩
    positivity⟩
  exact no_pos_maxT E r X Xa Fl _ _ hg.1 x0 hx0 hs0 hpos hmax

end GlobalTheory.UpperShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIndependentBoundedSectionsShiftedWeightLeStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_independent_boundedSections_shiftedWeight_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + (Xa.T + (nd X + 4)) • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 3 * nd X + 10).choose (nd X) := by
  first | exact @GlobalTheory.UpperShift.upper_shift | exact GlobalTheory.UpperShift.upper_shift | (intros; apply GlobalTheory.UpperShift.upper_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBounds
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BinomRatio
open Finset

theorem fact_mul_choose_eq_prod (T a n : ℕ) :
    ((n.factorial : ℕ) : ℝ) * (((T + a + n).choose n : ℕ) : ℝ)
      = ∏ i ∈ range n, ((T : ℝ) + a + 1 + i) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (T + a) n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h2 : ((∏ i ∈ range n, (T + a + 1 + i) : ℕ) : ℝ) = ((n.factorial * (T + a + n).choose n : ℕ) : ℝ) := by
    rw [h]
  push_cast at h2
  rw [← h2]

theorem prod_upper (T a n : ℕ) :
    ∏ i ∈ range n, ((T : ℝ) + a + 1 + i)
      ≤ (1 + (a : ℝ) / (T + 1)) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hc : (1 + (a : ℝ) / (T + 1)) ^ n = ∏ _i ∈ range n, (1 + (a : ℝ) / (T + 1)) := by simp
  rw [hc, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _; positivity
  · intro i _
    have hT : (0 : ℝ) < T + 1 := by positivity
    have hi : (0 : ℝ) ≤ i := by positivity
    have ha : (0 : ℝ) ≤ a := by positivity
    have e : (1 + (a : ℝ) / (T + 1)) * ((T : ℝ) + 0 + 1 + i) = (T + 1 + i) + a + a * i / (T + 1) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (a : ℝ) * i / (T + 1) := by positivity
    linarith

theorem prod_lower (T c n : ℕ) (hc : (c : ℝ) ≤ T) (hT : 0 < T) :
    (1 - (c : ℝ) / T) ^ n * ∏ i ∈ range n, ((T : ℝ) + c + 1 + i)
      ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hcp : (1 - (c : ℝ) / T) ^ n = ∏ _i ∈ range n, (1 - (c : ℝ) / T) := by simp
  rw [hcp, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _
    have : (0 : ℝ) ≤ 1 - c / T := by rw [sub_nonneg, div_le_one hT']; exact hc
    positivity
  · intro i _
    have hi : (0 : ℝ) ≤ i := by positivity
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have e : (1 - (c : ℝ) / T) * ((T : ℝ) + c + 1 + i) = (T + 1 + i) - (c * c + c * (1 + i)) / T := by
      field_simp; ring
    rw [e]
    have : 0 ≤ ((c : ℝ) * c + c * (1 + i)) / T := by positivity
    linarith

end GlobalTheory.BinomRatio

namespace GlobalTheory.BinomRatio
open Finset

theorem first_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n := by
  have e1 : T + 3 * n + 10 = T + (2 * n + 10) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hA := fact_mul_choose_eq_prod T (2 * n + 10) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hU := prod_upper T (2 * n + 10) n
  set x : ℝ := ((2 * n + 10 : ℕ) : ℝ) / (T + 1) with hx
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hnx : (n : ℝ) * x ≤ 0.65 := by
    rw [hx, mul_div_assoc', div_le_iff₀ hT1]
    push_cast
    nlinarith
  have hpow : (1 + x) ^ n ≤ 2 := by
    calc (1 + x) ^ n ≤ (Real.exp x) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp x; linarith
      _ = Real.exp (n * x) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9; linarith
      _ = 2 := Real.exp_log (by norm_num)
  have hP : 0 ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
    apply prod_nonneg; intro i _; positivity
  have key : ((n.factorial : ℕ) : ℝ) * (((T + (2 * n + 10) + n).choose n : ℕ) : ℝ)
      ≤ ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hA]
    calc ∏ i ∈ range n, ((T : ℝ) + ((2 * n + 10 : ℕ) : ℝ) + 1 + i)
        ≤ (1 + x) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := hU
      _ ≤ 2 * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := mul_le_mul_of_nonneg_right hpow hP
      _ = ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
          push_cast at hB ⊢
          rw [← hB]; ring
  have := le_of_mul_le_mul_left key hf
  exact_mod_cast this

theorem second_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  have e1 : T + 2 * n + 6 = T + (n + 6) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hT0 : 0 < T := by nlinarith
  have hTR0 : (0 : ℝ) < T := by exact_mod_cast hT0
  have hc : (((n + 6 : ℕ)) : ℝ) ≤ T := by push_cast; nlinarith
  have hA := fact_mul_choose_eq_prod T (n + 6) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hL := prod_lower T (n + 6) n hc hT0
  have hbern : 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) ≤ (1 + -((((n + 6 : ℕ)) : ℝ)) / T) ^ n := by
    apply one_add_mul_le_pow
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hTR0]
    linarith
  have hC : (0 : ℝ) ≤ (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by positivity
  have step : (1 - (n : ℝ) * (n + 6) / T) * (((T + (n + 6) + n).choose n : ℕ) : ℝ)
      ≤ (1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hC
    have h1 : (1 : ℝ) - (n : ℝ) * (n + 6) / T = 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) := by
      push_cast; ring
    have h2 : (1 : ℝ) - (((n + 6 : ℕ)) : ℝ) / T = 1 + -((((n + 6 : ℕ)) : ℝ)) / T := by ring
    rw [h1, h2]; exact hbern
  have key : ((n.factorial : ℕ) : ℝ) * ((1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ))
      ≤ ((n.factorial : ℕ) : ℝ) * (((T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hB, mul_left_comm, hA]
    simpa only [Nat.cast_zero] using hL
  have := le_of_mul_le_mul_left key hf
  linarith

theorem two_binom_ratios : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T →
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) :=
  fun T n hn hT => ⟨first_ratio T n hn hT, second_ratio T n hn hT⟩

end GlobalTheory.BinomRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBoundsStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_binomial_ratio_bounds : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T → (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧ (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  first | exact @GlobalTheory.BinomRatio.two_binom_ratios | exact GlobalTheory.BinomRatio.two_binom_ratios | (intros; apply GlobalTheory.BinomRatio.two_binom_ratios <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareRanks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem li_iff {α : Type} {D : Set α} {m : ℕ} (f : Fin m → α → ℂ) :
    LinearIndependent ℂ (fun q (x : D) => f q x.1) ↔
      ∀ u : Fin m → ℂ, (∀ x ∈ D, ∑ q, u q * f q x = 0) → u = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h u hu
    funext q
    refine h u ?_ q
    funext x
    simp [Finset.sum_apply, hu x.1 x.2]
  · intro h u hu q
    have : u = 0 := h u fun x hx => by
      have := congrFun hu ⟨x, hx⟩
      simpa [Finset.sum_apply] using this
    simp [this]

def UpC (X : Data E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (la : Wt Ψ r) (N : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Frame Ψ r → ℂ), (∀ q, (fun y => f q (castFrame hΨ y)) ∈ X.SS (castWt hΨ la)) →
    LinearIndependent ℂ (fun q (x : GG Ψ G p0) => f q x.1) → m ≤ N

def LowC (X : Data E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (la : Wt Ψ r) (N : ℕ) : Prop :=
  ∃ g : Fin N → Frame Ψ r → ℂ, (∀ q, (fun y => g q (castFrame hΨ y)) ∈ X.SS (castWt hΨ la)) ∧
    LinearIndependent ℂ (fun q (x : GG Ψ G p0) => g q x.1)

theorem span_upper {C D : Type} [Finite C] (S : Set (C → D → ℂ)) (N : C → ℕ)
    (hup : ∀ c (m : ℕ) (g : Fin m → C → D → ℂ), (∀ q, g q ∈ S) → LinearIndependent ℂ (fun q => g q c) → m ≤ N c) :
    Module.Finite ℂ (Submodule.span ℂ S) ∧ finrank ℂ (Submodule.span ℂ S) ≤ ∑ᶠ c, N c := by
  classical
  have : Fintype C := Fintype.ofFinite C
  let Sc : C → Set (D → ℂ) := fun c => (fun g => g c) '' S
  have hc : ∀ c, Module.Finite ℂ (Submodule.span ℂ (Sc c)) ∧ finrank ℂ (Submodule.span ℂ (Sc c)) ≤ N c := by
    intro c
    obtain ⟨b, hbS, hbsp, hbli⟩ := exists_linearIndependent ℂ (Sc c)
    have hcard : ∀ t : Finset (D → ℂ), (↑t : Set (D → ℂ)) ⊆ b → t.card ≤ N c := by
      intro t ht
      have hmem : ∀ v ∈ t, ∃ g ∈ S, g c = v := fun v hv => hbS (ht hv)
      choose g hgS hgc using hmem
      let e := t.equivFin
      let gg : Fin t.card → C → D → ℂ := fun q => g (e.symm q).1 (e.symm q).2
      have hli : LinearIndependent ℂ (fun q => gg q c) := by
        have h1 : LinearIndependent ℂ (fun v : b => (v : D → ℂ)) := hbli
        have h2 : LinearIndependent ℂ (fun v : t => (v : D → ℂ)) :=
          h1.comp (fun v : t => (⟨v.1, ht v.2⟩ : b)) (fun v w h => Subtype.ext (by simpa using congrArg Subtype.val h))
        have h3 := h2.comp e.symm e.symm.injective
        convert h3 using 1
        funext q
        simp [gg, hgc]
      exact hup c _ gg (fun q => hgS _ _) hli
    have hfin : b.Finite := by
      by_contra hinf
      obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (N c + 1)
      have := hcard t ht
      omega
    have hfs := hfin.fintype
    have hsp : Submodule.span ℂ (Sc c) = Submodule.span ℂ b := hbsp.symm
    rw [hsp]
    refine ⟨FiniteDimensional.span_of_finite ℂ hfin, ?_⟩
    rw [finrank_span_set_eq_card hbli]
    have := hcard hfin.toFinset (by simp)
    simpa [Set.toFinset_card] using this
  have : ∀ c, Module.Finite ℂ (Submodule.span ℂ (Sc c)) := fun c => (hc c).1
  let φ : Submodule.span ℂ S →ₗ[ℂ] ((c : C) → Submodule.span ℂ (Sc c)) :=
    LinearMap.pi fun c => ((LinearMap.proj c).comp (Submodule.span ℂ S).subtype).codRestrict _ (by
      intro v
      have hv := v.2
      refine Submodule.span_induction (p := fun w _ => w c ∈ Submodule.span ℂ (Sc c)) ?_ ?_ ?_ ?_ hv
      · intro w hw
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · simp
      · intro x y _ _ hx hy
        simpa using Submodule.add_mem _ hx hy
      · intro a x _ hx
        simpa using Submodule.smul_mem _ a hx)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    funext c
    have h1 : ((φ v c : Submodule.span ℂ (Sc c)) : D → ℂ) = 0 := by rw [hv]; rfl
    exact h1
  refine ⟨Module.Finite.of_injective φ hinj, ?_⟩
  calc finrank ℂ (Submodule.span ℂ S) ≤ finrank ℂ ((c : C) → Submodule.span ℂ (Sc c)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = ∑ c, finrank ℂ (Submodule.span ℂ (Sc c)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ c, N c := Finset.sum_le_sum fun c _ => (hc c).2
    _ = ∑ᶠ c, N c := (finsum_eq_sum_of_fintype _).symm

theorem lower_of_comps {C D : Type} [Finite C] (W : Submodule ℂ (C → D → ℂ)) [Module.Finite ℂ W] (N : C → ℕ)
    (hlow : ∀ c, ∃ g : Fin (N c) → C → D → ℂ, (∀ q, g q ∈ W) ∧ (∀ q, ∀ c' ≠ c, g q c' = 0) ∧
      LinearIndependent ℂ (fun q => g q c)) :
    ∑ᶠ c, N c ≤ finrank ℂ W := by
  classical
  have : Fintype C := Fintype.ofFinite C
  choose g hgW hg0 hgli using hlow
  let G : (Σ c, Fin (N c)) → W := fun i => ⟨g i.1 i.2, hgW i.1 i.2⟩
  have hli : LinearIndependent ℂ G := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    obtain ⟨c, q⟩ := i
    have h1 := congrArg (fun v : W => (v : C → D → ℂ) c) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, G,
      Submodule.coe_zero, Pi.zero_apply] at h1
    rw [Fintype.sum_sigma] at h1
    rw [Finset.sum_eq_single c (fun c' _ hc' => by simp [hg0 _ _ c (Ne.symm hc')]) (by simp)] at h1
    exact Fintype.linearIndependent_iff.1 (hgli c) (fun q => a ⟨c, q⟩) h1 q
  have := hli.fintype_card_le_finrank
  rw [finsum_eq_sum_of_fintype]
  simpa [Fintype.card_sigma] using this

theorem indep_mul (X : Data E r) {la : Wt X.Ψ r} {w : Frame X.Ψ r → ℂ} (hw : DifferentiableOn ℂ w X.dom)
    (hw0 : ∃ x ∈ X.dom, w x ≠ 0) {m : ℕ} {f : Fin m → Frame X.Ψ r → ℂ} (hf : ∀ q, X.IsBddSec la (f q))
    (hi : ∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) :
    ∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * (f q * w) x = 0) → u = 0 := by
  intro u hu
  apply hi u
  obtain ⟨x0, hx0, hw0⟩ := hw0
  have hg := (GlobalTheory.UpperModel.isBddSec_sum X hf u).1.1
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hw hg ?_ hx0 hw0
  intro y hy
  rw [Finset.mul_sum, ← hu y hy]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.mul_apply]
  ring

theorem mul_mem (X : Data E r) {la la' mu : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la)
    (hQ : X.IsBddSec la' Q) (h : la + la' = mu) : P * Q ∈ X.SS mu := by
  have := (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds r X la la' 0).2.1 P hP Q hQ
  rw [h] at this
  exact this

theorem compX (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa) (hm : GlobalTheory.Shares.Margins X.toData Xa)
    (h0 : 0 < X.p0) (h1 : X.p0 < r) (hg1 : GapsGe X.p0 Xa.L 1) (hg2 : PairGe Xa.L (1.9 * Xa.T))
    (hg3 : GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0)
    (hg4 : PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1) (s : ℕ) (hs : Even s) (hsT : s ≤ Xa.T)
    (u : Frame X.Ψ r → ℂ) (hu : u ∈ X.SS (deMul X.Ψ r X.p0 s)) (hu0 : ∃ x ∈ X.dom, u x ≠ 0) :
    (∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
    (∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
    (∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L + 2 • deMul X.Ψ r X.p0 s)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 3 * nd X.toData + 10).choose (nd X.toData)) ∧
    ∃ g : Fin (Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData)) → Frame X.Ψ r → ℂ,
      (∀ q, g q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) ∧
      ∀ a : _ → ℂ, (∀ x ∈ X.dom, ∑ q, a q * g q x = 0) → a = 0 := by
  have hup : ∀ (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, f q ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
      (∀ a : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, a q * f q x = 0) → a = 0) →
      m ≤ Fl.δ * (Xa.T + 2 * nd X.toData + 6).choose (nd X.toData) := fun m f hf hi =>
    GlobalTheory.UpperModel.upper E r X.toData Xa Fl m f (fun q => (hf q).1) hi
  refine ⟨hup, ?_, ?_, GlobalTheory.T.lowerRank_cuspForms_detWeight_oneComponent E r X Xa Fl hm h0 h1 hg1 hg2 hg3 hg4 s hs hsT u hu hu0⟩
  · intro m f hf hi
    have hmem : ∀ q, f q * u ∈ X.SS (Xa.Fp + Xa.T • Xa.L) := fun q =>
      mul_mem X.toData (hf q) hu.1 (sub_add_cancel _ _)
    exact hup m _ hmem (indep_mul X.toData hu.1.1.1 hu0 (fun q => (hf q).1) hi)
  · intro m f hf hi
    obtain ⟨w, hw, hw0⟩ := GlobalTheory.T.exists_nonzero_boundedSection_shiftedWeight E r X Xa Fl hm h0 h1 hg1 hg2 hg3 hg4 s hs hsT u hu hu0
    have hmem : ∀ q, X.IsBddSec (Xa.Fp + (Xa.T + (nd X.toData + 4)) • Xa.L) (f q * w) := fun q =>
      (mul_mem X.toData (hf q) hw (by simp only [add_smul]; abel)).1
    exact GlobalTheory.T.card_independent_boundedSections_shiftedWeight_le E r X.toData Xa Fl m _ hmem (indep_mul X.toData hw.1.1 hw0 (fun q => (hf q).1) hi)

theorem compT (X : DataX E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (hG : X.Gm = G) (hp : X.p0 = p0) (L Fp : Wt Ψ r) (T s : ℕ)
    (hA : ArchOne X.toData (castWt hΨ L) (castWt hΨ Fp) T) (h0 : 0 < p0) (h1 : p0 < r)
    (hg1 : GapsGe p0 L 1) (hg2 : PairGe L (1.9 * T))
    (hg3 : GapsGe p0 (Fp - kLog Ψ r - (nd X.toData + 2) • L) 0)
    (hg4 : PairGe (Fp - kLog Ψ r - (nd X.toData + 2) • L) 1) (hs : Even s) (hsT : s ≤ T)
    (u : Frame Ψ r → ℂ) (hu : (fun y => u (castFrame hΨ y)) ∈ X.SS (castWt hΨ (deMul Ψ r p0 s)))
    (hu0 : ∃ y ∈ X.dom, u (castFrame hΨ y) ≠ 0) :
    ∃ δ : ℕ, (2 ≤ nd X.toData ∧ 11 * nd X.toData ^ 2 ≤ T) ∧ UpC X.toData hΨ G p0 (Fp + T • L) (δ * (T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
      UpC X.toData hΨ G p0 (Fp + T • L - deMul Ψ r p0 s) (δ * (T + 2 * nd X.toData + 6).choose (nd X.toData)) ∧
      UpC X.toData hΨ G p0 (Fp + T • L + 2 • deMul Ψ r p0 s)
        (δ * (T + 3 * nd X.toData + 10).choose (nd X.toData)) ∧
      LowC X.toData hΨ G p0 (Fp + T • L - deMul Ψ r p0 s) (δ * (T + nd X.toData).choose (nd X.toData)) := by
  subst hΨ hG hp
  obtain ⟨Xa, hL, hF, hT, hm, ⟨Fl⟩⟩ := hA
  change Xa.L = L at hL
  change Xa.Fp = Fp at hF
  subst hL hF hT
  obtain ⟨c1, c2, c3, g, hg, hgi⟩ := compX X Xa Fl hm h0 h1 hg1 hg2 hg3 hg4 s hs hsT u hu hu0
  exact ⟨Fl.δ, ⟨Xa.n_ge, Xa.T_ge⟩, fun m f hf hli => c1 m f hf ((li_iff f).1 hli), fun m f hf hli => c2 m f hf ((li_iff f).1 hli),
    fun m f hf hli => c3 m f hf ((li_iff f).1 hli), g, hg, (li_iff g).2 hgi⟩

theorem exists_pull_ne {U' C : Type} [Group U'] [Fintype U'] [DecidableEq U'] [MulAction U' C]
    (M : TwoLevels E r U' C) {F : C → Frame M.Ψ r → ℂ} {c : C} {x : Frame M.Ψ r} (h : M.detTr F c x ≠ 0) :
    ∃ g : U', M.pull g F c x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold TwoLevels.detTr
  have e : (Matrix.of fun g g' : U' => M.pull (g * g') F c x) = 0 := by
    ext g g'
    simp [hc]
  haveI : Nonempty U' := ⟨1⟩
  rw [e, Matrix.det_zero]

theorem tr_one_mem {U' C : Type} [Group U'] [MulAction U' C] (M : TwoLevels E r U' C) (c : C) :
    M.tr 1 c ∈ (M.comp c).Γ := by
  have h := M.tr_mul 1 1 c
  simp only [mul_one, one_smul] at h
  have e : M.tr 1 c * (M.tr 1 c * M.tr 1 c)⁻¹ = (M.tr 1 c)⁻¹ := by group
  rw [e] at h
  exact (Subgroup.inv_mem_iff _).1 h

theorem nd_comp {U' C : Type} [Group U'] [MulAction U' C] (M : TwoLevels E r U' C) (c : C) :
    nd (M.comp c).toData = M.dimY := by
  unfold nd TwoLevels.dimY
  rw [Fintype.card_prod, Fintype.card_coe, GlobalTheory.ChartCount.card_strictLower]
  rw [M.comp_Ψ c]

theorem nzT (X : Data E r) {Ψ : Finset (E →+* ℂ)} (hΨ : X.Ψ = Ψ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (hG : X.Gm = G) (hp : X.p0 = p0) (F : Frame Ψ r → ℂ) {la : Wt X.Ψ r}
    (hF : X.IsSec la (fun y => F (castFrame hΨ y))) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hχ : X.χ la γ = 1)
    (x : Frame Ψ r) (hx : x ∈ GG Ψ G p0) (h : F (lact γ x) ≠ 0) : ∃ y ∈ X.dom, F (castFrame hΨ y) ≠ 0 := by
  subst hΨ hG hp
  refine ⟨x, hx, fun h0 => h ?_⟩
  have := hF.2.2 γ hγ x hx
  rw [hχ, one_mul] at this
  exact this.trans h0

section Cusp

variable {U C : Type} [Group U] [MulAction U C]

theorem upper_cusp [Finite C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (N : C → ℕ)
    (h : ∀ c, UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 la (N c)) :
    Module.Finite ℂ (M.cusp la) ∧ finrank ℂ (M.cusp la) ≤ ∑ᶠ c, N c := by
  refine span_upper _ N fun c m g hg hli => ?_
  choose F hF hFg using hg
  refine h c m (fun q => F q c) (fun q => hF q c) ?_
  have e : (fun q => g q c) = fun q (x : GG M.Ψ M.Gm M.p0) => F q c x.1 := by
    funext q x
    rw [← hFg q]
    rfl
  rw [← e]
  exact hli

theorem lower_cusp [Finite C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) [Module.Finite ℂ (M.cusp la)] (N : C → ℕ)
    (h : ∀ c, LowC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 la (N c)) :
    ∑ᶠ c, N c ≤ finrank ℂ (M.cusp la) := by
  classical
  refine lower_of_comps _ N fun c => ?_
  obtain ⟨g, hg, hli⟩ := h c
  let F : Fin (N c) → C → Frame M.Ψ r → ℂ := fun q c' => if c' = c then g q else 0
  have hF : ∀ q, F q ∈ M.SS la := by
    intro q c'
    by_cases hc : c' = c
    · subst hc
      simpa [F] using hg q
    · simp only [F, if_neg hc]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds r (M.comp c').toData _ 0 0).1.1
  refine ⟨fun q => M.res (F q), fun q => Submodule.subset_span ⟨F q, hF q, rfl⟩, ?_, ?_⟩
  · intro q c' hc'
    funext x
    simp [TwoLevels.res, F, hc']
  · have e : (fun q => M.res (F q) c) = fun q (x : GG M.Ψ M.Gm M.p0) => g q x.1 := by
      funext q x
      simp [TwoLevels.res, F]
    show LinearIndependent ℂ (fun q => M.res (F q) c)
    rw [e]
    exact hli

end Cusp

theorem ranks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp (sub M ⊥) → 0 < M.p0 → M.p0 < r →
    ∀ (ka : Wt M.Ψ r) (T : ℕ), ArchOn M ka T → sOf M ≤ T →
      Ranks M ka (sOf M) ((M.dimY : ℝ) * (M.dimY + 6) / T) 2 := by
  intro E _ _ _ r U C _ _ _ _ M hLev h0 h1 ka T hArch hsT
  classical
  obtain ⟨L, Fp, rfl, hg1, hg2, hg3, hg4, hA⟩ := hArch
  haveI : Fintype (⊥ : Subgroup U) := Fintype.ofFinite _
  obtain ⟨u0, hu0, hnz⟩ :=
    GlobalTheory.T.exists_cuspForm_independent_translates E r (⊥ : Subgroup U) C (sub M ⊥) hLev (sOf M) (even_sOf M) (le_sOf M)
  have hc : ∀ c, ∃ δ : ℕ, (2 ≤ M.dimY ∧ 11 * M.dimY ^ 2 ≤ T) ∧
      UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L)
        (δ * (T + 2 * M.dimY + 6).choose M.dimY) ∧
      UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))
        (δ * (T + 2 * M.dimY + 6).choose M.dimY) ∧
      UpC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L + 2 • deMul M.Ψ r M.p0 (sOf M))
        (δ * (T + 3 * M.dimY + 10).choose M.dimY) ∧
      LowC (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))
        (δ * (T + M.dimY).choose M.dimY) := by
    intro c
    have hnd := nd_comp M c
    have hg3' := hg3
    have hg4' := hg4
    rw [← hnd] at hg3' hg4'
    obtain ⟨x, hx, hdx⟩ := hnz c
    obtain ⟨h, hh⟩ := exists_pull_ne (sub M ⊥) hdx
    have hh1 : (h : U) = 1 := Subgroup.mem_bot.1 h.2
    change u0 ((h : U) • c) (lact (M.tr (h : U) c) x) ≠ 0 at hh
    rw [hh1, one_smul] at hh
    have hγ := tr_one_mem M c
    obtain ⟨y, hy, hy0⟩ := nzT (M.comp c).toData (M.comp_Ψ c) M.Gm M.p0 (M.comp_Gm c) (M.comp_basePoint c) (u0 c)
      (hu0 c).1.1 hγ (M.χ_one c _ _ hγ) x hx hh
    obtain ⟨δ, hn, c1, c2, c3, c4⟩ := compT (M.comp c) (M.comp_Ψ c) M.Gm M.p0 (M.comp_Gm c) (M.comp_basePoint c) L Fp T
      (sOf M) (hA c) h0 h1 hg1 hg2 hg3' hg4' (even_sOf M) hsT (u0 c) (hu0 c) ⟨y, hy, hy0⟩
    rw [hnd] at hn c1 c2 c3 c4
    exact ⟨δ, hn, c1, c2, c3, c4⟩
  choose δ hn c1 c2 c3 c4 using hc
  obtain ⟨f0, r0⟩ := upper_cusp M _ _ c1
  obtain ⟨fm, -⟩ := upper_cusp M _ _ c2
  obtain ⟨f2, r2⟩ := upper_cusp M _ _ c3
  have l0 := lower_cusp M _ _ c4
  haveI : Fintype C := Fintype.ofFinite C
  rw [finsum_eq_sum_of_fintype] at r0 r2 l0
  set n := M.dimY with hn_def
  have hb : ∀ c, (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧
      (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) :=
    fun c => GlobalTheory.T.two_binomial_ratio_bounds T n (hn c).1 (hn c).2
  refine ⟨f0, f2, ?_, ?_, fm⟩
  · by_cases hε : 1 - (n : ℝ) * (n + 6) / T ≤ 0
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hε (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    · push_neg at hε
      have r0' : (finrank ℂ (M.cusp (Fp + T • L)) : ℝ) ≤ ∑ c, (δ c : ℝ) * ((T + 2 * n + 6).choose n : ℕ) := by
        exact_mod_cast r0
      have l0' : ∑ c, (δ c : ℝ) * ((T + n).choose n : ℕ) ≤
          (finrank ℂ (M.cusp (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))) : ℝ) := by
        exact_mod_cast l0
      calc (1 - (n : ℝ) * (n + 6) / T) * finrank ℂ (M.cusp (Fp + T • L))
          ≤ (1 - (n : ℝ) * (n + 6) / T) * ∑ c, (δ c : ℝ) * ((T + 2 * n + 6).choose n : ℕ) :=
            mul_le_mul_of_nonneg_left r0' hε.le
        _ = ∑ c, (δ c : ℝ) * ((1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            ring
        _ ≤ ∑ c, (δ c : ℝ) * ((T + n).choose n : ℕ) :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hb c).2 (Nat.cast_nonneg _)
        _ ≤ _ := l0'
  · have key : finrank ℂ (M.cusp (Fp + T • L + 2 • deMul M.Ψ r M.p0 (sOf M))) ≤
        2 * finrank ℂ (M.cusp (Fp + T • L - deMul M.Ψ r M.p0 (sOf M))) := by
      calc _ ≤ ∑ c, δ c * (T + 3 * n + 10).choose n := r2
        _ ≤ ∑ c, δ c * (2 * (T + n).choose n) :=
            Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hb c).1
        _ = 2 * ∑ c, δ c * (T + n).choose n := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            ring
        _ ≤ _ := Nat.mul_le_mul_left _ l0
    exact_mod_cast key

end GlobalTheory.ShareRanks

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeightsStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoLevelFlagDomain_cuspForm_ranks_shifted_weights : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp (sub M ⊥) → 0 < M.p0 → M.p0 < r → ∀ (ka : Wt M.Ψ r) (T : ℕ), ArchOn M ka T → sOf M ≤ T → Ranks M ka (sOf M) ((M.dimY : ℝ) * (M.dimY + 6) / T) 2 := by
  first | exact @GlobalTheory.ShareRanks.ranks | exact GlobalTheory.ShareRanks.ranks | (intros; apply GlobalTheory.ShareRanks.ranks <;> assumption)
end
