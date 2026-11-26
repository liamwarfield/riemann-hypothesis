module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

def LemmaETailMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) → ∀ C₁ : ℝ, 0 ≤ C₁ →
    ∃ CE : ℝ, ∀ u : Fin D → X → ℝ, (∀ i, IsLemmaEPot A Om L s C₁ (u i)) →
      TailMassBound A (secOpen s) (rSec L s) (fun i => potForm Om.pot (u i)) CE

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StTailShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def TailShift.Statement : Prop :=
  ∀ (D : ℕ) (B CE : ℝ), ∃ CE' : ℝ, ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas D X) (Yo : Set X) (r r' : X → ℝ) (T : Fin D → LocPot X),
    IsOpen Yo → ContinuousOn r Yo → ContinuousOn r' Yo →
    (∀ x ∈ Yo, Real.exp 1 ≤ r x) → (∀ x ∈ Yo, Real.exp 1 ≤ r' x) →
    (∀ x ∈ Yo, |r x - r' x| ≤ B) →
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A T j y) →
    TailLogBound A Yo r' T CE → TailLogBound A Yo r T CE'

section Inhabitants

open ReciprocityTheory.AnForm (fsDens fsDens_pos)
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart projectiveLine_fubiniStudy_mass_one)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts errE errorWithLinear ell)

noncomputable section

section C2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_finset_biUnion {α β ι κ : Type*} [UniformSpace β] {F : κ → α → β}
    {f : α → β} {p : Filter κ} (T : Finset ι) (S : ι → Set α)
    (h : ∀ i ∈ T, TendstoUniformlyOn F f p (S i)) : TendstoUniformlyOn F f p (⋃ i ∈ T, S i) := by
  intro u hu
  filter_upwards [(eventually_all_finset T).2 fun i hi => h i hi u hu] with n hn x hx
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hx
  exact hn i hi x hx

theorem TendstoC2On.congr_open {F G : ℝ → E → ℝ} {f : E → ℝ} {L U : Set E} (hU : IsOpen U)
    (hLU : L ⊆ U) (hFG : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ U, F t y = G t y) (h : TendstoC2On G f L) :
    TendstoC2On F f L := by
  have e0 : ∀ t, (∀ y ∈ U, F t y = G t y) → ∀ y ∈ U, F t =ᶠ[𝓝 y] G t :=
    fun t ht y hy => Filter.eventually_of_mem (hU.mem_nhds hy) ht
  refine ⟨h.1.congr ?_, h.2.1.congr ?_, h.2.2.congr ?_⟩
  · filter_upwards [hFG] with t ht y hy
    exact (ht y (hLU hy)).symm
  · filter_upwards [hFG] with t ht y hy
    exact (e0 t ht y (hLU hy)).fderiv_eq.symm
  · filter_upwards [hFG] with t ht y hy
    have h' : fderiv ℝ (F t) =ᶠ[𝓝 y] fderiv ℝ (G t) :=
      Filter.eventually_of_mem (hU.mem_nhds (hLU hy)) fun z hz => (e0 t ht z hz).fderiv_eq
    exact h'.fderiv_eq.symm

end C2

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.NormIteratedFDerivCompLeOfIsOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

namespace ArgumentConvergenceLemmas

open Filter Topology Metric Set MeasureTheory
open scoped ContDiff
open ReciprocityTheory.AnForm.A (Mollifier molli shrink)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (errE errorWithLinear ell)

noncomputable section

theorem molli_contDiffAt {D : ℕ} (ρ : Mollifier D) {P : Set (Fin D → ℂ)} (hP : IsOpen P)
    {u : (Fin D → ℂ) → ℝ} (hu : ContinuousOn u P) {ε : ℝ} (hε : 0 < ε) {z : Fin D → ℂ}
    (hz : z ∈ shrink P ε) : ContDiffAt ℝ ∞ (molli ρ ε u) z := by
  obtain ⟨δ, hδ, hδP⟩ := ReciprocityTheory.AnForm.A.exists_thick hP hε.le hz
  have hi : Integrable ((closedBall z (ε + δ)).indicator u) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      ((hu.mono hδP).integrableOn_compact (isCompact_closedBall z (ε + δ)))
  have hg := (ReciprocityTheory.AnForm.A.scaled_hasCompactSupport ρ hε).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (ReciprocityTheory.AnForm.A.scaled_contDiff ρ ε)
    hi.locallyIntegrable
  refine hg.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds z hδ] with y hy
  rw [mem_ball] at hy
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ hε (C := closedBall z (ε + δ))
    (closedBall_subset_closedBall' (by linarith)), convolution_def]
  rfl

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_fderiv_eq (g : E → F) (y : E) :
    ‖fderiv ℝ (fderiv ℝ g) y‖ = ‖iteratedFDeriv ℝ 2 g y‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem norm_iteratedFDeriv_sub_eq {a b : E → ℝ} {V : Set E} (hV : IsOpen V)
    (ha : ContDiffOn ℝ 2 a V) (hb : ContDiffOn ℝ 2 b V) {z : E} (hz : z ∈ V) :
    ‖iteratedFDeriv ℝ 0 (fun y => a y - b y) z‖ = ‖a z - b z‖ ∧
      ‖iteratedFDeriv ℝ 1 (fun y => a y - b y) z‖ = ‖fderiv ℝ a z - fderiv ℝ b z‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => a y - b y) z‖ =
        ‖fderiv ℝ (fderiv ℝ a) z - fderiv ℝ (fderiv ℝ b) z‖ := by
  have da : DifferentiableAt ℝ a z :=
    (ha.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  have db : DifferentiableAt ℝ b z :=
    (hb.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, fderiv_fun_sub da db]
  · rw [← norm_fderiv_fderiv_eq, fderiv2_sub_of_contDiffOn hV ha hb hz]

theorem norm_iteratedFDeriv_comp_le_of_isOpen {g : F → G} {f : E → F} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t) (hg : ContDiffOn ℝ 2 g t) (hf : ContDiffOn ℝ 2 f s)
    (hst : MapsTo f s t) {x : E} (hx : x ∈ s) {n : ℕ} (hn : n ≤ 2) {C d : ℝ}
    (hC : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ d ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial * C * d ^ n := by
  have hn' : (n : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hn
  rw [← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le (hg.of_le hn') (hf.of_le hn') le_rfl ht.uniqueDiffOn
    hs.uniqueDiffOn hst hx (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx)]
    exact hC i (hi.trans hn)
  · rw [iteratedFDerivWithin_of_isOpen i hs hx]
    exact hD i hi1 (hi.trans hn)

theorem exists_bound_iteratedFDeriv {f : E → F} {s K : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ B : ℝ, ∀ i : ℕ, i ≤ 2 → ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
  have h : ∀ i : ℕ, i ≤ 2 → ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun i hi =>
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hf hs (by exact_mod_cast hi)).mono hKs)
  obtain ⟨B0, h0⟩ := h 0 (by norm_num)
  obtain ⟨B1, h1⟩ := h 1 (by norm_num)
  obtain ⟨B2, h2⟩ := h 2 le_rfl
  refine ⟨max B0 (max B1 B2), fun i hi y hy => ?_⟩
  interval_cases i
  · exact (h0 y hy).trans (le_max_left _ _)
  · exact (h1 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y hy).trans ((le_max_right _ _).trans (le_max_right _ _))

end Calculus

theorem tendstoUniformlyOn_of_norm_le {Y α : Type*} [SeminormedAddCommGroup α] {F : ℝ → Y → α}
    {f : Y → α} {K : Set Y} {β : ℝ → ℝ} (hβ : Tendsto β (𝓝[>] 0) (𝓝 0))
    (h : ∀ᶠ t in 𝓝[>] 0, ∀ y ∈ K, ‖F t y - f y‖ ≤ β t) :
    TendstoUniformlyOn F f (𝓝[>] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [h, hβ.eventually (gt_mem_nhds he)] with t ht hβt y hy
  rw [dist_comm, dist_eq_norm]
  exact (ht y hy).trans_lt hβt

end

end ArgumentConvergenceLemmas

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassZero.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ t, S.J 0 ε t ≤ η

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassError
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassError.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1), ∀ δ, 0 < δ → ∃ τ, 0 < τ ∧ ∀ t₀ t, 0 < t → t ≤ t₀ → t₀ ≤ τ →
      S.ell₀ ≤ ell t₀ → S.errW a ha t₀ t ≤ δ ∧ S.errDiv a ha t₀ t ≤ δ

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassStep.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1) (ε t : ℝ), 0 < ε → 0 < t → S.ell₀ ≤ ell t →
      S.J (a + 1) ε t ≤ S.J a ε t + S.plTerm a ha ε t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassReplace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def GreenMassReplace.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∃ Cκ, 0 ≤ Cκ ∧ ∀ (a : ℕ) (ha : a < D + 1) (t₀ : ℝ), 0 < t₀ → S.ell₀ ≤ ell t₀ →
      ∃ K, 0 ≤ K ∧ ∀ ε t, 0 < ε → ε ≤ 1 → 0 < t → t ≤ t₀ →
        S.plTerm a ha ε t ≤ K * S.J a ε t + Cκ * S.errW a ha t₀ t + 2 * S.errDiv a ha t₀ t

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def RegSection.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ (L : LocPot X) (s : X → X → ℂ), IsPotential A L ∧ IsSection A L s ∧
      (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) ∧ secOpen s = R.Yo ∧ Dense R.Yo ∧
      ContinuousOn R.r R.Yo ∧ ContinuousOn (rSec L s) R.Yo ∧
      ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec L s y| ≤ B

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
