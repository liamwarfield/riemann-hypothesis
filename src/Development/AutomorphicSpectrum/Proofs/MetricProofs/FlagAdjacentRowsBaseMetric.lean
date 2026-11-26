module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedMeasure

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem locSec_norm_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr x x' ψ ψ' kb kb' σ σ' i₀ i₀' V V' u u' _ _ hs hs' w hw
  obtain ⟨⟨F, H, hc⟩, -, -, hVs, hVU, -, hu, hd, hn⟩ := hs
  obtain ⟨-, -, -, -, hVU', -, hu', hd', hn'⟩ := hs'
  by_cases h0 : ψ w i₀ = 0
  · have h0' : ψ' w i₀' = 0 := (hd' w hw.2).2 ((hd w hw.1).1 h0)
    simp [h0, h0']
  have h0' : ψ' w i₀' ≠ 0 := fun h => h0 ((hd w hw.1).2 ((hd' w hw.2).1 h))
  obtain ⟨-, hF, -, -, -, hp⟩ := hc
  obtain ⟨hH, hG, z₀, z₁, hz₀, hz₁, hex⟩ := hp w (hVs hw.1)
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    obtain ⟨c, hc0, hzc⟩ := hz₀
    have e₀ : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k =>
        (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk (fstPt k₀ (RW.lift w w)) q := by
      rw [hzc]; rfl
    rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
      (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk (fstPt k₀ (RW.lift w w)))]
    exact hG
  have hD : IsPtData M τ a k₀ ca cb RW w z₀ z₁ F (H τ (ψ w)) (ψ w i₀) :=
    ⟨hF, hG', hz₀, hz₁, (hH τ).1, (hH τ).2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  have e₁ := hn w hw.1 h0 z₀ z₁ F _ _ hD
  have e₂ := hn' w hw.2 h0' z₀ z₁ F _ _ hD
  have hA : 0 < (potA M τ a k₀).h (RW.lift x w) := (potA M τ a k₀).pos _ (RW.mem x w (hVU hw.1)).1
  have hA' : 0 < (potA M τ a k₀).h (RW.lift x' w) := (potA M τ a k₀).pos _ (RW.mem x' w (hVU' hw.2)).1
  have hN : 0 < ‖u w * ψ w i₀‖ := norm_pos_iff.2 (mul_ne_zero (hu w hw.1) h0)
  have hN' : 0 < ‖u' w * ψ' w i₀'‖ := norm_pos_iff.2 (mul_ne_zero (hu' w hw.2) h0')
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hN hA)) (Set.mem_Ioi.2 (div_pos hN' hA')) ?_
  rw [Real.log_div hN.ne' hA.ne', Real.log_div hN'.ne' hA'.ne', e₁, e₂]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_transition_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.locSec_norm_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartLocalCoordinatesAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsNormFnLogNormSecDiagSec
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isNormFn_logNormSec_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ (b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsNormFn M τ a k₀ ca cb RW fun x => logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) x + c := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hab hk hca hcb hW c
    x z₀ z₁ F h t h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hd : IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hno := GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hd
  obtain ⟨-, -, hx, -, -, -, hu, hiff, hnorm⟩ := hL x
  have hψ : ψ x x (i₀ x) ≠ 0 := fun h0 => hno ((hiff x hx).1 h0)
  have hn := hnorm x hx hψ z₀ z₁ F h t hd
  have hne : ‖u x x * ψ x x (i₀ x)‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero (hu x hx) hψ)
  show Real.log (‖u x x * ψ x x (i₀ x)‖ *
    Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x x)) + c))) + c = _
  rw [Real.log_mul hne (Real.exp_ne_zero _), Real.log_exp, ← hn]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_local_coordinates_alt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ (b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsNormFn M τ a k₀ ca cb RW fun x => logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) x + c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isNormFn_logNormSec_diagSec <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphicAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsSectionDiagSec
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isSection_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsSection RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  refine ⟨fun x => ?_, fun x x' w hw => ?_⟩
  · obtain ⟨⟨F, H, hC⟩, -, -, hsrc, -, hu, -⟩ := hL x
    intro l z hz
    have hz' : z ∈ (RW.A.chart l).target ∩ (RW.A.chart l).symm ⁻¹' (ψ x).source :=
      ⟨hz.1, hsrc hz.2⟩
    have h1 : AnalyticAt ℂ (u x ∘ (RW.A.chart l).symm) z := hu l z hz
    have h2 : AnalyticAt ℂ ((ψ x) ∘ (RW.A.chart l).symm) z := (hC.1 l).1 z hz'
    have h3 : AnalyticAt ℂ (fun w => ((ψ x) ∘ (RW.A.chart l).symm) w (i₀ x)) z :=
      analyticAt_pi_iff.1 h2 (i₀ x)
    exact h1.mul h3
  · have hx : 0 < (potA M τ a k₀).h (RW.lift x w) :=
      (potA M τ a k₀).pos _ (RW.mem x w ((hL x).2.2.2.2.1 hw.1)).1
    have hx' : 0 < (potA M τ a k₀).h (RW.lift x' w) :=
      (potA M τ a k₀).pos _ (RW.mem x' w ((hL x').2.2.2.2.1 hw.2)).1
    have hg := locSec_norm_eq K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x x' (ψ x) (ψ x') (kb x) (kb x') (σ x) (σ x')
      (i₀ x) (i₀ x') (V x) (V x') (u x) (u x') hblk hW (hL x) (hL x') w hw
    have key : ∀ (s h : ℝ), 0 < h → s * Real.exp (-(Real.log h + c)) = s / h * Real.exp (-c) := by
      intro s h hh
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log h), Real.exp_log hh, div_eq_mul_inv, mul_assoc]
    show ‖u x w * ψ x w (i₀ x)‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x w)) + c)) =
      ‖u x' w * ψ x' w (i₀ x')‖ * Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x' w)) + c))
    rw [key _ _ hx, key _ _ hx', hg]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_holomorphic_alt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsSection RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isSection_diagSec | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isSection_diagSec | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isSection_diagSec <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartContinuousProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwisted
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwisted
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

theorem chart_swap_keep :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ (∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i) ∧ ∀ y ∈ ψ'.source, ∀ i, (∀ l, σ l ≠ i) → ψ' y i = ψ y i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]
  · intro y _ i hi
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) i = ψ y i
    exact Function.extend_apply' _ _ _ (fun ⟨l, hl⟩ => hi l hl)

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwistedStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_chart_product_projection_twisted : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ (∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i) ∧ ∀ y ∈ ψ'.source, ∀ i, (∀ l, σ l ≠ i) → ψ' y i = ψ y i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep | exact GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap_keep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartContinuousProjection
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd

theorem compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (h : IsCompatChart A ψ) (V : Set X) (hV : IsOpen V) :
    IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  refine ⟨?_, ?_⟩
  · refine (h j).1.mono ?_
    rintro z ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    have : (A.chart j).symm z ∈ ψ.source ∩ V := by
      simpa [OpenPartialHomeomorph.restrOpen_source] using hs
    exact this.1
  · have hsymm : ((ψ.restrOpen V hV).symm : (Fin e → ℂ) → X) = ψ.symm := rfl
    rw [hsymm]
    refine (h j).2.mono ?_
    rintro z ⟨hz, hs⟩
    refine ⟨?_, hs⟩
    have h1 : ψ.symm z ∈ ψ.source ∩ V := by
      have := (ψ.restrOpen V hV).map_target hz
      rwa [OpenPartialHomeomorph.restrOpen_source] at this
    have h2 : ψ (ψ.symm z) = z := (ψ.restrOpen V hV).right_inv hz
    rw [← h2]
    exact ψ.map_source h1.1

theorem holoOn_comp {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (B : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A B pr) (S : Set Z) (g : Z → ℂ) (hg : B.HoloOn S g) :
    A.HoloOn (pr ⁻¹' S) (fun y => g (pr y)) := by
  rintro j z ⟨hzt, hzS⟩
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart j).symm z))
  have h1 : AnalyticAt ℂ (B.chart k ∘ pr ∘ (A.chart j).symm) z := hp.2 j k z ⟨hzt, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ pr ∘ (A.chart j).symm) z) := by
    refine hg k _ ⟨(B.chart k).map_source hk, ?_⟩
    have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm z))) = pr ((A.chart j).symm z) :=
      (B.chart k).left_inv hk
    simpa [this] using hzS
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (pr ∘ (A.chart j).symm) z :=
    hp.1.continuousAt.comp ((A.chart j).continuousAt_symm hzt)
  filter_upwards [hc.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hk)] with w hw
  have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm w))) = pr ((A.chart j).symm w) :=
    (B.chart k).left_inv hw
  simp [this]

theorem snoc_inj {r n e : ℕ} (σb : Fin r → Option (Fin n)) (s : Fin n ↪ Fin e) (i₀ : Fin e)
    (hne : ∀ i, s i ≠ i₀) (hσ : ∀ k k' i, σb k = some i → σb k' = some i → k = k') (k k' : Fin (r + 1)) (i : Fin e)
    (h : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k = some i)
    (h' : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k' = some i) :
    k = k' := by
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast l =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h'
      exact absurd (hb.trans h.symm) (hne b)
  | cast l =>
    induction k' using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h
      exact absurd (hb.trans h'.symm) (hne b)
    | cast l' =>
      simp only [Fin.snoc_castSucc] at h h'
      obtain ⟨b, hb, hbi⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b', hb', hbi'⟩ := Option.map_eq_some_iff.1 h'
      have : b = b' := s.injective (hbi.trans hbi'.symm)
      subst this
      rw [hσ l l' b hb hb']

theorem mul_rearrange (A B a b c : ℂ) (h : A = B) : a * A * (b * c) = a * b * (B * c) := by
  subst h
  ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → BM.Rb.X) (hc : Continuous pr) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin BM.Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M BM.Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), HoloMap RW.A BM.Rb.A pr → ∀ c : ℝ, IsSNC RW.A (BM.L.pullback pr hc + secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (fun x y => BM.s (pr x) (pr y) * diagSec ψ i₀ u x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) (diagSet k₀ RW)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hp c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, hVU, huh, hu0, hdiag, -⟩ := hL x
  obtain ⟨hcomp, -, hne, hbase, -, -⟩ := hW
  obtain ⟨ψb, hψbc, hxb, hψbU, σb, hσi, hσW, ub, hubh, hub0, hs⟩ := BM.snc (pr x)
  obtain ⟨ψ', hψ'c, hsrc, hk1, hk2⟩ :=
    GlobalTheory.T.compatible_chart_product_projection_twisted e n RW.X BM.Rb.X RW.A BM.Rb.A pr (ψ x) (kb x) (σ x) ψb hcomp hψbc hbase
  have hsrc'' : (ψ'.restrOpen (V x) hVo).source = ψ'.source ∩ V x := ψ'.restrOpen_source (V x) hVo
  have hcoe : ∀ y, (ψ'.restrOpen (V x) hVo) y = ψ' y := fun y => rfl
  have hmem : ∀ y ∈ (ψ'.restrOpen (V x) hVo).source, y ∈ ψ'.source ∧ y ∈ V x ∧ pr y ∈ ψb.source := by
    intro y hy
    rw [hsrc''] at hy
    refine ⟨hy.1, hy.2, ?_⟩
    have := hy.1
    rw [hsrc] at this
    exact this.2
  refine ⟨ψ'.restrOpen (V x) hVo, compat_restr _ _ hψ'c _ hVo, ?_, ?_,
    Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map (σ x)) (some (i₀ x)),
    snoc_inj σb (σ x) (i₀ x) hne hσi, ?_, fun y => ub (pr y) * u x y, ?_, ?_, ?_⟩
  · rw [hsrc'', hsrc]
    exact ⟨⟨hVs hxV, hxb⟩, hxV⟩
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact ⟨hψbU hyb, hyV⟩
  · intro k
    induction k using Fin.lastCases with
    | last =>
      ext y
      simp only [Fin.snoc_last, Set.mem_inter_iff, Set.mem_setOf_eq, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨hd, hy⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨hy, ?_⟩
        rw [hcoe, hk2 y hy' _ hne]
        exact (hdiag y hyV).2 hd
      · rintro ⟨hy, h0⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨(hdiag y hyV).1 ?_, hy⟩
        rw [hcoe, hk2 y hy' _ hne] at h0
        exact h0
    | cast k =>
      ext y
      simp only [Fin.snoc_castSucc, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      have hWk := Set.ext_iff.1 (hσW k) (pr y)
      constructor
      · rintro ⟨hw, hy⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨-, i, hi, h0⟩ := hWk.1 ⟨hw, hyb⟩
        refine ⟨hy, σ x i, by rw [hi]; rfl, ?_⟩
        rw [hcoe, hk1 y hy']
        exact h0
      · rintro ⟨hy, i', hi', h0⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hi'
        rw [hcoe, hk1 y hy'] at h0
        exact ⟨(hWk.2 ⟨hyb, i, hi, h0⟩).1, hy⟩
  · intro l z hz
    have h1 := holoOn_comp RW.A BM.Rb.A pr hp ψb.source ub hubh l z ⟨hz.1, (hmem _ hz.2).2.2⟩
    have h2 := huh l z ⟨hz.1, (hmem _ hz.2).2.1⟩
    exact h1.mul h2
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact mul_ne_zero (hub0 _ hyb) (hu0 _ hyV)
  · intro y hy
    obtain ⟨hy', hyV, hyb⟩ := hmem y hy
    have hi₀ : ψ' y (i₀ x) = ψ x y (i₀ x) := hk2 y hy' _ hne
    beta_reduce
    rw [Fin.prod_univ_castSucc, hs (pr y) hyb]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, pow_one, hcoe, diagSec, hi₀]
    refine mul_rearrange _ _ _ _ _ (Finset.prod_congr rfl fun k _ => ?_)
    cases h : σb k <;> simp [hk1 y hy']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartContinuousProjectionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_continuous_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → BM.Rb.X) (hc : Continuous pr) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin BM.Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M BM.Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), HoloMap RW.A BM.Rb.A pr → ∀ c : ℝ, IsSNC RW.A (BM.L.pullback pr hc + secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (fun x y => BM.s (pr x) (pr y) * diagSec ψ i₀ u x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) (diagSet k₀ RW)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartLocalCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartLocalCoordinates
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isOpen_blocksNonzero {κ : Type} [Fintype κ] (ρ : κ → Type) :
    IsOpen {z : (Σ k, ρ k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem logNormSec_secPot_le : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∃ c : ℝ, ∀ w, logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) w ≤ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hb hW
  have hAs : ContinuousOn (potA M τ a k₀).h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    ContDiffOn.continuousOn (GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm (ι := fun o : Option _ => ι (o.getD k₀)) (aDeg M τ a k₀))
  have hg : Continuous fun w => ‖diagSec ψ i₀ u w w‖ / (potA M τ a k₀).h (RW.lift w w) := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨-, hVo, hxV, hVs, -, hu, -⟩ := hL x
    have hlift : ContinuousAt (RW.lift x) x := continuousAt_pi.2 fun p =>
      ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.continuousAt_of_holoOn RW.A (RW.holo x p) (RW.mem_U x)
    have hmem := (RW.mem x x (RW.mem_U x)).1
    have hh : ContinuousAt (fun w => (potA M τ a k₀).h (RW.lift x w)) x :=
      ContinuousAt.comp (g := (potA M τ a k₀).h)
        (hAs.continuousAt ((isOpen_blocksNonzero _).mem_nhds hmem)) hlift
    have hψ : ContinuousAt (fun w => ψ x w (i₀ x)) x :=
      (continuous_apply (i₀ x)).continuousAt.comp ((ψ x).continuousAt (hVs hxV))
    have hloc : ContinuousAt (fun w => ‖u x w * ψ x w (i₀ x)‖ / (potA M τ a k₀).h (RW.lift x w)) x :=
      (((ReciprocityTheory.AnForm.P.LeviFormBoundaryTopology.continuousAt_of_holoOn RW.A hu hxV).mul hψ).norm).div hh
        ((potA M τ a k₀).pos _ hmem).ne'
    refine hloc.congr ?_
    filter_upwards [hVo.mem_nhds hxV] with w hw
    exact GlobalTheory.T.twisted_chart_transition_analytic K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr x w (ψ x) (ψ w) (kb x) (kb w) (σ x) (σ w)
      (i₀ x) (i₀ w) (V x) (V w) (u x) (u w) hb hW (hL x) (hL w) w ⟨hw, (hL w).2.2.1⟩
  obtain ⟨Cb, hCb⟩ := (isCompact_range hg).bddAbove
  refine ⟨Real.log (max Cb 1), fun w => ?_⟩
  have hgw : ‖diagSec ψ i₀ u w w‖ / (potA M τ a k₀).h (RW.lift w w) ≤ max Cb 1 :=
    (hCb ⟨w, rfl⟩).trans (le_max_left _ _)
  have hpos : 0 < (potA M τ a k₀).h (RW.lift w w) := (potA M τ a k₀).pos _ (RW.mem w w (RW.mem_U w)).1
  have hm : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hexp : Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift w w)) + Real.log (max Cb 1))) =
      ((potA M τ a k₀).h (RW.lift w w))⁻¹ * (max Cb 1)⁻¹ := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hpos, Real.exp_log hm]
  show Real.log (‖diagSec ψ i₀ u w w‖ *
    Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift w w)) + Real.log (max Cb 1)))) ≤ 0
  rw [hexp]
  refine Real.log_nonpos (by positivity) ?_
  have : ‖diagSec ψ i₀ u w w‖ * (((potA M τ a k₀).h (RW.lift w w))⁻¹ * (max Cb 1)⁻¹) =
      (‖diagSec ψ i₀ u w w‖ / (potA M τ a k₀).h (RW.lift w w)) / max Cb 1 := by
    rw [div_div, div_eq_mul_inv, mul_inv]
  rw [this]
  exact (div_le_one hm).2 hgw

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartLocalCoordinatesStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_local_coordinates : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∃ c : ℝ, ∀ w, logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) w ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.logNormSec_secPot_le | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.logNormSec_secPot_le | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.logNormSec_secPot_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

private theorem isPotential_secPot_of_isSmoothHerm {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)]
    {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ρ)} {e : ℕ} (R : ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes P J e)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ρ) (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A)
    (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (hVU : ∀ x, V x ⊆ R.U x)
    (c : ℝ) : ReciprocityTheory.AnForm.M.IsPotential R.A (secPot R A V hV hm c) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have hol : ∀ (x : R.X) (p : (k : κ) × ρ k) (j : Fin R.A.n) (t : Fin e → ℂ),
      t ∈ (R.A.chart j).target → (R.A.chart j).symm t ∈ R.U x →
      AnalyticAt ℂ (fun s => R.lift x ((R.A.chart j).symm s) p) t :=
    fun x p j t ht hu => R.holo x p j t ⟨ht, hu⟩
  have memNZ : ∀ (z0 y0 : R.X), y0 ∈ R.U z0 → ∀ k, ∃ i, R.lift z0 y0 ⟨k, i⟩ ≠ 0 := by
    intro z0 y0 h
    have h' := R.mem z0 y0 h
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.mcPts, Set.mem_ofPred_eq] at h'
    exact h'.1
  unfold ReciprocityTheory.AnForm.M.IsPotential ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn
    ReciprocityTheory.AnForm.M.FinHolAtlas.HoloOn
  dsimp only [secPot]
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t))
        ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) := by
      rw [contDiffOn_pi]
      intro p
      have h1 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t) p)
          ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) :=
        fun t ht => (hol x p j t ht.1 (hVU x ht.2)).contDiffAt.contDiffWithinAt
      exact h1.restrict_scalars ℝ
    have hmem : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        (∀ k, ∃ i, R.lift x ((R.A.chart j).symm t) ⟨k, i⟩ ≠ 0) :=
      fun t ht => memNZ x _ (hVU x ht.2)
    have hh := hA'.comp hlift (fun t ht => hmem t ht)
    have hne : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        A.h (R.lift x ((R.A.chart j).symm t)) ≠ 0 :=
      fun t ht => (A.pos _ (hmem t ht)).ne'
    exact (hh.log hne).add contDiffOn_const
  · obtain ⟨hyx, hyx'⟩ := hy
    have hyU : y ∈ R.U x := hVU x hyx
    have hyU' : y ∈ R.U x' := hVU x' hyx'
    choose i hi using memNZ x' y hyU'
    obtain ⟨r, hr⟩ : ∃ r : κ → R.X → ℂ,
        ∀ k z, r k z = R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ :=
      ⟨fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩, fun _ _ => rfl⟩
    have hry : ∀ k, r k y ≠ 0 := by
      intro k
      obtain ⟨cy, hcy, hly⟩ := R.compat x x' y ⟨hyU, hyU'⟩
      have h1 := congrFun hly ⟨k, i k⟩
      rw [hr, h1]
      exact div_ne_zero (mul_ne_zero (hcy k) (hi k)) (hi k)
    obtain ⟨j, hj⟩ := R.A.cover y
    have hD : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x')) :=
      (R.A.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x).inter (R.isOpen_U x'))
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Fin e → ℂ), O = {t | t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane} := ⟨_, rfl⟩
    have memO : ∀ t, t ∈ O ↔ (t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane) := by
      intro t; rw [hOdef]; rfl
    have hO : IsOpen O := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      obtain ⟨htT, htU, htne, htsl⟩ := (memO t).1 ht
      have hDn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x') ∈ 𝓝 t :=
        hD.mem_nhds ⟨htT, htU⟩
      have hca : ∀ (z0 : R.X) (p : (k : κ) × ρ k), (R.A.chart j).symm t ∈ R.U z0 →
          ContinuousAt (fun s => R.lift z0 ((R.A.chart j).symm s) p) t :=
        fun z0 p hz => (hol z0 p j t htT hz).continuousAt
      have e1 : ∀ᶠ s in 𝓝 t, ∀ k, R.lift x' ((R.A.chart j).symm s) ⟨k, i k⟩ ≠ 0 := by
        rw [Filter.eventually_all]
        intro k
        exact (hca x' _ htU.2).eventually_ne (htne k)
      have e2 : ∀ᶠ s in 𝓝 t, ∀ k, r k ((R.A.chart j).symm s) / r k y ∈ Complex.slitPlane := by
        rw [Filter.eventually_all]
        intro k
        have hc0 : ContinuousAt (fun s => r k ((R.A.chart j).symm s)) t := by
          simp only [hr]
          exact (hca x _ htU.1).div (hca x' _ htU.2) (htne k)
        have hc : ContinuousAt (fun s => r k ((R.A.chart j).symm s) / r k y) t :=
          hc0.div_const _
        exact hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (htsl k))
      filter_upwards [hDn, e1, e2] with s hs1 hs2 hs3
      exact (memO s).2 ⟨hs1.1, hs1.2, hs2, hs3⟩
    have hWopen : IsOpen ((R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O) :=
      (R.A.chart j).isOpen_inter_preimage hO
    have hsy : (R.A.chart j).symm ((R.A.chart j) y) = y := (R.A.chart j).left_inv hj
    have hyW : y ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O := by
      refine ⟨hj, (memO _).2 ?_⟩
      rw [hsy]
      refine ⟨(R.A.chart j).map_source hj, ⟨hyU, hyU'⟩, hi, fun k => ?_⟩
      rw [div_self (hry k)]
      exact Complex.one_mem_slitPlane
    have condW : ∀ z ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, z ∈ R.U x ∧ z ∈ R.U x' ∧
        (∀ k, R.lift x' z ⟨k, i k⟩ ≠ 0) ∧ ∀ k, r k z / r k y ∈ Complex.slitPlane := by
      intro z hz
      have h2 := (memO ((R.A.chart j) z)).1 hz.2
      rw [(R.A.chart j).left_inv hz.1] at h2
      exact ⟨h2.2.1.1, h2.2.1.2, h2.2.2.1, h2.2.2.2⟩
    refine ⟨(R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, hWopen, hyW,
      fun z => (∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ), ?_, ?_⟩
    · intro j' t ht
      obtain ⟨hUx, hUx', hne, hsl⟩ := condW _ ht.2
      have hra : ∀ k, AnalyticAt ℂ (fun s => r k ((R.A.chart j').symm s)) t := by
        intro k
        simp only [hr]
        exact (hol x _ j' t ht.1 hUx).div (hol x' _ j' t ht.1 hUx') (hne k)
      show AnalyticAt ℂ (fun s => (∑ k, ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)) t
      refine AnalyticAt.add ?_ analyticAt_const
      have hs : ∀ k ∈ (Finset.univ : Finset κ), AnalyticAt ℂ (fun s => ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) t :=
        fun k _ => analyticAt_const.mul (((hra k).div analyticAt_const (hry k)).clog (hsl k))
      have h3 := Finset.analyticAt_sum Finset.univ hs
      rw [Finset.sum_fn] at h3
      exact h3
    · intro z hz
      obtain ⟨hUx, hUx', hne, -⟩ := condW z hz.1.1
      obtain ⟨cz, hcz, hlz⟩ := R.compat x x' z ⟨hUx, hUx'⟩
      have hrz : ∀ k, r k z = cz k := by
        intro k
        rw [hr]
        have h1 := congrFun hlz ⟨k, i k⟩
        rw [h1]
        exact mul_div_cancel_right₀ _ (hne k)
      have hhz : A.h (R.lift x z) = (∏ k, ‖cz k‖ ^ A.a k) * A.h (R.lift x' z) := by
        rw [hlz]; exact A.smul cz _ hcz
      have hhpos : 0 < A.h (R.lift x' z) := A.pos _ (memNZ x' z hUx')
      have hczn : ∀ k, ‖cz k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hcz k)
      have hryn : ∀ k, ‖r k y‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hry k)
      have lhs : (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
          ∑ k, (A.a k : ℝ) * Real.log ‖cz k‖ := by
        rw [hhz, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hczn k))
          hhpos.ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hczn k))]
        simp only [Real.log_zpow]
        ring
      show (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
        ((∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
          ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)).re
      rw [lhs]
      simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re,
        Complex.log_re, norm_div, hrz]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.log_div (hczn k) (hryn k)]
      ring

theorem isPotential_secPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (potA M τ a k₀) := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA
    exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _
  exact isPotential_secPot_of_isSmoothHerm RW (potA M τ a k₀) hS V _ _ (fun x => (hL x).2.2.2.2.1) c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphicStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secPot_isPotential : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.isPotential_secPot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartCoordinatesRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartCoordinatesRegular
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, -, hu, hu0, hd, -⟩ := hL x
  have hsrc : ((ψ x).restrOpen (V x) hVo).source = V x := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.mpr hVs
  refine ⟨(ψ x).restrOpen (V x) hVo, pa_compat_restr RW.A (ψ x) hW.1 (V x) hVo, by rw [hsrc]; exact hxV, ?_,
    fun _ => some (i₀ x), ?_, ?_, u x, ?_, ?_, ?_⟩
  · rw [hsrc]; exact subset_rfl
  · intro k k' _ _ _
    exact Subsingleton.elim k k'
  · intro k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    rw [hsrc]
    ext w
    constructor
    · rintro ⟨hw, hwV⟩
      exact ⟨hwV, i₀ x, rfl, (hd w hwV).2 hw⟩
    · rintro ⟨hwV, i, hi, hw⟩
      obtain rfl : i₀ x = i := Option.some.inj hi
      exact ⟨(hd w hwV).1 hw, hwV⟩
  · rw [hsrc]; exact hu
  · rw [hsrc]; exact hu0
  · rw [hsrc]
    intro w _
    simp [diagSec]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartCoordinatesRegularStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chart_coordinates_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetric
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X) (hc : Continuous pr), IsWAtlas M BM.Rb τ a k₀ ca cb RW pr → ∃ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (Dg : Set RW.X) (cst : ℝ), IsPotential RW.A L' ∧ IsSection RW.A L' v ∧ IsSNC RW.A L' v ![1] ![Dg] ∧ IsSNC RW.A (BM.L.pullback pr hc + L') (fun x y => BM.s (pr x) (pr y) * v x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) Dg) ∧ (∀ w, logNormSec L' v w ≤ 0) ∧ IsNormFn M τ a k₀ ca cb RW fun x => logNormSec L' v x + cst := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM τ a b k₀ ca cb hb hj hblk hca hcb _ RW pr hc hW
  choose ψ kb σ i₀ V u hL using
    GlobalTheory.T.flag_adjacent_twisted_measure K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a b k₀ ca cb hb hj hblk hca hcb RW pr hW
  obtain ⟨c, hc0⟩ := GlobalTheory.T.twisted_chart_local_coordinates K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.secPot RW (GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA M τ a k₀) V
      (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c,
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec ψ i₀ u, GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSet k₀ RW, c, ?_, ?_, ?_, ?_, hc0, ?_⟩
  · exact GlobalTheory.T.secPot_isPotential K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact GlobalTheory.T.twisted_chart_holomorphic_alt K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL hblk hW c
  · exact GlobalTheory.T.twisted_chart_coordinates_regular K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  · exact GlobalTheory.T.twisted_chart_continuous_projection K ι Φ y Ψ N j M n (d + 2) BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hW.1 c
  · exact GlobalTheory.T.twisted_chart_local_coordinates_alt K ι Φ y Ψ N j M n (d + 2) BM.Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hj hblk hca hcb hW c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsBaseMetricStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_base_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X) (hc : Continuous pr), IsWAtlas M BM.Rb τ a k₀ ca cb RW pr → ∃ (L' : LocPot RW.X) (v : RW.X → RW.X → ℂ) (Dg : Set RW.X) (cst : ℝ), IsPotential RW.A L' ∧ IsSection RW.A L' v ∧ IsSNC RW.A L' v ![1] ![Dg] ∧ IsSNC RW.A (BM.L.pullback pr hc + L') (fun x y => BM.s (pr x) (pr y) * v x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) Dg) ∧ (∀ w, logNormSec L' v w ≤ 0) ∧ IsNormFn M τ a k₀ ca cb RW fun x => logNormSec L' v x + cst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.main <;> assumption)
end
