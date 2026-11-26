module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartMollifiedBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology MeasureTheory Set
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt polyMax shrink)

noncomputable section

theorem trunc_ge_of_bdd {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (K B : ℝ) (j : Fin R.N) {V : Set (Fin D → ℂ)} (hVo : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) (hb : ∀ y ∈ V, R.trunc K j y ≤ B) {y : Fin D → ℂ} (hy : y ∈ V) :
    -K ≤ R.trunc K j y := by
  unfold RegChartData.trunc limsupExt
  split_ifs with hA
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)
    have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[(R.chart j).target \ coordDiv (R.S j)] y)
        (fun y => max (R.u j y) (-K)) := by
      refine isBoundedUnder_of_eventually_le (a := B) ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hy), self_mem_nhdsWithin]
        with y' hy'V hy'
      have h := hb y' hy'V
      simp only [RegChartData.trunc, limsupExt, if_neg hy'.2] at h
      exact h
    refine le_limsup_of_le hbdd (fun b hb' => ?_)
    obtain ⟨y', hy'⟩ := hb'.exists
    exact (le_max_right _ _).trans hy'
  · exact le_max_right (R.u j y) (-K)

theorem le_molli_of_ge {D : ℕ} (ρ : Mollifier D) {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}
    (hU : IsOpen U) (hφ : IsPsh U φ) {t c : ℝ} (ht : 0 < t) {z : Fin D → ℂ}
    (hz : closedBall z t ⊆ U) (hc : ∀ y ∈ closedBall z t, c ≤ φ y) : c ≤ molli ρ t φ z := by
  obtain ⟨-, hi⟩ := ReciprocityTheory.AnForm.A.phiC hU hφ (isCompact_closedBall z t) hz
  rw [ReciprocityTheory.AnForm.A.molli_eq_C ρ ht (subset_refl _)]
  calc c = ∫ y, ρ.scaled t y * c := by
        rw [integral_mul_const, ReciprocityTheory.AnForm.A.integral_scaled ρ ht, one_mul]
    _ ≤ _ := by
      refine integral_mono ((ReciprocityTheory.AnForm.A.integrable_scaled ρ ht).mul_const _)
        (ReciprocityTheory.AnForm.A.integrable_kC ρ ht hi z) fun y => ?_
      by_cases hy : ρ.scaled t y = 0
      · simp [hy]
      refine mul_le_mul_of_nonneg_left ?_ (ReciprocityTheory.AnForm.A.scaled_nonneg ρ ht y)
      have hmem := ReciprocityTheory.AnForm.A.mem_ball_sub ρ ht hy z
      rw [indicator_of_mem hmem]
      exact hc _ hmem

theorem ChartMollifiedBounds.proof (h : TruncPsh.Statement) : ChartMollifiedBounds.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B, hδ, hV⟩ := h X D A R
  choose V hVo hVt hVball hVpsh using hV

  have hcpt : ∀ j, IsCompact (R.chart j '' closure (R.mid j)) := fun j =>
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have himg : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro j _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  choose r hr hrt using fun j => (hcpt j).exists_cthickening_subset_open (R.chart j).open_target (himg j)

  obtain ⟨ε, hε, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ j, ε ≤ r j := by
    rcases isEmpty_or_nonempty (Fin R.N) with hN | hN
    · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, -, hj₀⟩ := Finset.univ.exists_min_image r Finset.univ_nonempty
      exact ⟨r j₀, hr j₀, fun j => hj₀ j (Finset.mem_univ j)⟩

  choose Cq hCq using fun j => (hcpt j).exists_bound_of_continuousOn
    (((R.q_smooth j).continuousOn).mono (himg j))
  refine ⟨max B 0 + ∑ j, |Cq j|, min δ ε, lt_min hδ hε, fun t ht ht₀ => ⟨?_, ?_⟩⟩
  · intro j x hx
    exact (closedBall_subset_cthickening (mem_image_of_mem _ hx) t).trans
      ((cthickening_mono ((ht₀.trans_le (min_le_right _ _)).le.trans (hεr j)) _).trans (hrt j))
  intro K hK j x hx
  have hxs : x ∈ (R.chart j).source := R.closure_mid j (subset_closure hx)
  obtain ⟨hpsh, hbd⟩ := hVpsh j K
  have htδ : t ≤ δ := (ht₀.trans_le (min_le_left _ _)).le
  have hball : closedBall (R.chart j x) t ⊆ V j :=
    (closedBall_subset_closedBall htδ).trans (hVball j x hx)
  have hq : |R.q j (R.chart j x)| ≤ ∑ j, |Cq j| := by
    have h1 := hCq j (R.chart j x) (mem_image_of_mem _ (subset_closure hx))
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Cq j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))

  have hlow : -K ≤ molli ρ t (R.trunc K j) (R.chart j x) :=
    le_molli_of_ge ρ (hVo j) hpsh ht hball fun y hy =>
      trunc_ge_of_bdd R K _ j (hVo j) (hVt j) hbd (hball hy)
  have hup : molli ρ t (R.trunc K j) (R.chart j x) ≤ max B 0 := by
    have h1 := ReciprocityTheory.AnForm.A.molli_le_polyMax ρ (hVo j) hpsh ht (z := R.chart j x) hball
    refine h1.trans (ReciprocityTheory.AnForm.A.polyMax_le' ht.le fun y hy => ?_)
    exact (hbd y (hball hy)).trans (max_le_max le_rfl (by linarith))
  have hphReg : R.phReg ρ K t j x = molli ρ t (R.trunc K j) (R.chart j x) - R.q j (R.chart j x) := rfl
  refine ⟨?_, ?_, fun hY => ?_⟩
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  · rw [hphReg]; linarith [neg_abs_le (R.q j (R.chart j x)), le_abs_self (R.q j (R.chart j x)), le_max_right B 0]
  ·
    have hA : R.chart j x ∉ coordDiv (R.S j) := (R.mem_Yo j x hxs).1 hY
    have htr : R.trunc K j (R.chart j x) = max (R.u j (R.chart j x)) (-K) := by
      simp only [RegChartData.trunc, limsupExt, if_neg hA]
    have hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x := by
      simp only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hxs]
    have hle := ReciprocityTheory.AnForm.A.le_molli ρ (hVo j) hpsh ht (z := R.chart j x) hball
    rw [hphReg]
    linarith [le_max_left (R.u j (R.chart j x)) (-K)]

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.ToPotentialChartsChartFun
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

theorem closure_image_subset {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : closure s ⊆ e.source) :
    IsCompact (e '' closure s) ∧ closure (e.target ∩ e.symm ⁻¹' s) ⊆ e '' closure s := by
  have hK : IsCompact (e '' closure s) :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  refine ⟨hK, closure_minimal ?_ hK.isClosed⟩
  rintro y ⟨hy, hys⟩
  exact ⟨e.symm y, subset_closure hys, e.right_inv hy⟩

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace RegCharts

def ofPotentialCharts [CompactSpace X] (P : PotentialCharts A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) : RegCharts A where
  n := P.N
  ψ := P.chart
  compat := P.compat
  W j := (P.chart j).target
  W' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
  W'' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.inner j
  isOpen_kappaOpenNeighbourhood j := (P.chart j).open_target
  isOpen_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_mid j)
  isOpen_alt_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_inner j)
  W_subset _ := subset_rfl
  isCompact_closure_middle j :=
    (closure_image_subset (P.chart j) (P.closure_mid j)).1.of_isClosed_subset isClosed_closure
      (closure_image_subset (P.chart j) (P.closure_mid j)).2
  closure_W'_subset j := (closure_image_subset (P.chart j) (P.closure_mid j)).2.trans
    (image_subset_iff.2 fun _ hx => (P.chart j).map_source (P.closure_mid j hx))
  closure_W''_subset j := by
    have hs := (P.closure_inner j).trans (P.mid_subset_source j)
    refine (closure_image_subset (P.chart j) hs).2.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hs hx)]
    exact P.closure_inner j hx
  cover x := by
    obtain ⟨j, hj⟩ := P.cover x
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hj)
    refine ⟨j, hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rw [(P.chart j).left_inv hs]
    exact hj
  θ := P.th
  θ_pot := P.th_pot
  om := om
  om_pot := om_pot
  om_pos := om_pos
  q := P.q
  q_smooth := P.q_smooth
  q_θ j y hy _ := by
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := P.q_th j y y ⟨P.th.mem_U y, hy⟩
    refine ⟨V, hV, hyV, fun x => -G x, fun k => (hG k).neg, fun x hx _ => ?_⟩
    have := hq x hx
    simp only [Complex.neg_re]
    linarith

variable [CompactSpace X] (P : PotentialCharts A) (om : LocPot X) (om_pot : IsPotential A om)
  (om_pos : IsPosPot A om)

end RegCharts

namespace RegCharts

variable (R : RegCharts A)

variable [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1)

end RegCharts

section RoundTrip

variable [CompactSpace X] [T2Space X]

end RoundTrip

namespace PotentialCharts

variable (P : PotentialCharts A)


end PotentialCharts

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
end
