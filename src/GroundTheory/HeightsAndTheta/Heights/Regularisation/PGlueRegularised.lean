module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)

noncomputable section

namespace RegChartData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)


open Classical in
theorem glue_eventually (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      R.regularised ρ K t ε η y =
        regMax ε (fun j : {j // x₀ ∈ R.mid j} => R.phReg ρ K t j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      (x₀ ∉ R.mid j → y ∉ L j ∧ y ∉ closure (R.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ R.mid j
    · filter_upwards [(R.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (R.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (R.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (R.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [RegChartData.regularised, PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ R.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ R.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := R.cover y
  have hk0 : x₀ ∈ R.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ R.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, R.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

theorem arg_contDiffAt (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin R.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ R.mid j) :
    ContDiffAt ℝ ∞ (fun y => R.phReg ρ K t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by
  have hxj : x ∈ (R.chart j).source := R.mid_subset_source j hj
  have hT : ContDiffAt ℝ ∞ (R.chart j ∘ ψ.symm) (ψ x) :=
    ((analyticAt_transition hψ (R.compat j) hx hxj).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hTx : (R.chart j ∘ ψ.symm) (ψ x) = R.chart j x := by simp [ψ.left_inv hx]
  have hS := (R.smoothed_local ρ K ht j (hball j x (subset_closure hj))).1
  have hq : ContDiffAt ℝ ∞ (R.q j) (R.chart j x) :=
    (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds ((R.chart j).map_source hxj))
  rw [← hTx] at hS hq
  have hη := contDiffAt_comp_symm_of_smoothOn hψ (R.isOpen_mid j) (hcut.smooth j) hj hx
  exact ((hS.comp (ψ x) hT).sub (hq.comp (ψ x) hT)).add (contDiffAt_const.mul hη)

end RegChartData


open Classical in
theorem GlueRegularised.proof : GlueRegularised.Statement := by
  intro X _ _ _ D A R ρ η Cη K t ε hcut ht hε hball hcmp
  refine ⟨fun i y hy => ?_, fun k x hx w => ?_⟩
  ·
    have hyt : y ∈ (A.chart i).target := hy.1
    have hx₀ : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hyt
    have hψ : IsCompatChart A (A.chart i) := fun l => ⟨A.holo l i, A.holo i l⟩
    have hyx : A.chart i ((A.chart i).symm y) = y := (A.chart i).right_inv hyt
    have hloc := R.glue_eventually ρ η hcut hε.le hcmp ((A.chart i).symm y)
    have hG : ContDiffAt ℝ ∞ (fun y' => regMax ε (fun j : {j // (A.chart i).symm y ∈ R.mid j} =>
        R.phReg ρ K t j ((A.chart i).symm y') + 4 * ε * η j ((A.chart i).symm y')) + ε / 2) y := by
      have hr := ((ReciprocityTheory.AnForm.A.regMax_thm {j // (A.chart i).symm y ∈ R.mid j}).1 ε hε).1
      refine (hr.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).add contDiffAt_const
      have := R.arg_contDiffAt ρ η (K := K) (ε := ε) hcut ht hball hψ hx₀ j.2
      rwa [hyx] at this
    refine (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (((A.chart i).continuousAt_symm hyt).tendsto.eventually hloc).mono fun y' hy' => hy'.2
  ·
    have hψ := R.compat k
    have hxk : x ∈ (R.chart k).source := R.mid_subset_source k hx
    have hzt : R.chart k x ∈ (R.chart k).target := (R.chart k).map_source hxk
    have hqk : ContDiffAt ℝ ∞ (R.q k) (R.chart k x) :=
      (R.q_smooth k).contDiffAt ((R.chart k).open_target.mem_nhds hzt)
    set b : {j // x ∈ R.mid j} → (Fin D → ℂ) → ℝ := fun j y =>
      R.phReg ρ K t j ((R.chart k).symm y) + 4 * ε * η j ((R.chart k).symm y) + R.q k y with hb_def
    have hb : ∀ j, ContDiffAt ℝ ∞ (b j) (R.chart k x) := fun j =>
      (R.arg_contDiffAt ρ η (K := K) (ε := ε) hcut ht hball hψ hxk j.2).add hqk
    have hadd := ((ReciprocityTheory.AnForm.A.regMax_thm {j // x ∈ R.mid j}).1 ε hε).2.2.2.2.2.2.1
    have hgerm : R.chartFun (R.regularised ρ K t ε η) k =ᶠ[𝓝 (R.chart k x)]
        fun y => regMax ε (fun j => b j y) + ε / 2 := by
      have hloc := R.glue_eventually ρ η hcut hε.le hcmp x
      have ht' : Tendsto (R.chart k).symm (𝓝 (R.chart k x)) (𝓝 x) := by
        have := ((R.chart k).continuousAt_symm hzt).tendsto
        rwa [(R.chart k).left_inv hxk] at this
      filter_upwards [ht'.eventually hloc] with y hy
      simp only [PotentialCharts.chartFun]
      rw [hy.2, hb_def, hadd]
      ring
    have hconst : levi (fun y => regMax ε (fun j => b j y) + ε / 2) (R.chart k x) w =
        levi (fun y => regMax ε (fun j => b j y)) (R.chart k x) w := by
      unfold levi
      have : fderiv ℝ (fun y => regMax ε (fun j => b j y) + ε / 2) =
          fderiv ℝ (fun y => regMax ε (fun j => b j y)) := funext fun _ => fderiv_add_const _
      rw [this]
    rw [levi_congr hgerm w, hconst]
    have hzV : R.chart k x ∈ interior {y | ∀ j, ContDiffAt ℝ 2 (b j) y} :=
      mem_interior_iff_mem_nhds.2 (Filter.eventually_all.2 fun j =>
        ((hb j).of_le (WithTop.coe_le_coe.mpr le_top)).eventually (by simp))
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm D {j // x ∈ R.mid j} ε _ b isOpen_interior hε
      (fun j y hy => (interior_subset hy j).contDiffWithinAt) _ hzV w _ fun ⟨j, hj⟩ => ?_
    have hxj : x ∈ (R.chart j).source := R.mid_subset_source j hj
    set T := R.chart j ∘ (R.chart k).symm with hT
    have hTa : AnalyticAt ℂ T (R.chart k x) := analyticAt_transition hψ (R.compat j) hxk hxj
    have hTR : ContDiffAt ℝ ∞ T (R.chart k x) := (hTa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have hTz : T (R.chart k x) = R.chart j x := by simp [hT, (R.chart k).left_inv hxk]
    obtain ⟨hS, hSl⟩ := R.smoothed_local ρ K ht j (hball j x (subset_closure hj))
    have hq : ContDiffAt ℝ ∞ (R.q j) (R.chart j x) :=
      (R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds ((R.chart j).map_source hxj))
    rw [← hTz] at hS hSl hq
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hS2 : ContDiffAt ℝ 2 (R.smoothed ρ K t j ∘ T) (R.chart k x) := (hS.comp _ hTR).of_le h2
    have hQ2 : ContDiffAt ℝ 2 (fun y => R.q k y - R.q j (T y)) (R.chart k x) :=
      (hqk.sub (hq.comp _ hTR)).of_le h2
    have hE2 : ContDiffAt ℝ 2 (η j ∘ (R.chart k).symm) (R.chart k x) :=
      (contDiffAt_comp_symm_of_smoothOn hψ (R.isOpen_mid j) (hcut.smooth j) hj hxk).of_le h2
    have hF2 : ContDiffAt ℝ 2 (fun y => (R.smoothed ρ K t j ∘ T) y + 1 * (R.q k y - R.q j (T y)))
        (R.chart k x) := hS2.add (contDiffAt_const.mul hQ2)
    have hbe : b ⟨j, hj⟩ = fun y => ((R.smoothed ρ K t j ∘ T) y + 1 * (R.q k y - R.q j (T y))) +
        4 * ε * (η j ∘ (R.chart k).symm) y := by
      funext y
      simp only [hb_def, RegChartData.phReg, hT, Function.comp_apply]
      ring
    have e1 := levi_add_smul (4 * ε) hF2 hE2 w
    have e2 := levi_add_smul 1 hS2 hQ2 w
    have e3 := levi_comp (φ := R.smoothed ρ K t j) w hTa (hS.of_le h2)

    have e4 : levi (fun y => R.q k y - R.q j (T y)) (R.chart k x) w = 0 := by
      obtain ⟨W, hWo, hxW, G, hG, hGeq⟩ := R.q_th k x x ⟨R.th.mem_U x, hxk⟩
      obtain ⟨W', hWo', hxW', G', hG', hGeq'⟩ := R.q_th j x x ⟨R.th.mem_U x, hxj⟩
      have hO : IsOpen (W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source) :=
        (((hWo.inter hWo').inter (R.th.isOpen_U x)).inter (R.chart k).open_source).inter
          (R.chart j).open_source
      have hxO : x ∈ W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source :=
        ⟨⟨⟨⟨hxW, hxW'⟩, R.th.mem_U x⟩, hxk⟩, hxj⟩
      have hev1 : ∀ᶠ y in 𝓝 (R.chart k x),
          (R.chart k).symm y ∈ W ∩ W' ∩ R.th.U x ∩ (R.chart k).source ∩ (R.chart j).source :=
        ((R.chart k).continuousAt_symm hzt).preimage_mem_nhds
          (by rw [(R.chart k).left_inv hxk]; exact hO.mem_nhds hxO)
      have hev := hev1.and ((R.chart k).open_target.mem_nhds hzt)
      have hGa := analyticAt_comp_symm_of_holoOn hψ hG hxW hxk
      have hGa' := analyticAt_comp_symm_of_holoOn hψ hG' hxW' hxk
      have hgerm : (fun y => R.q k y - R.q j (T y)) =ᶠ[𝓝 (R.chart k x)]
          fun y => (((G ∘ (R.chart k).symm) - (G' ∘ (R.chart k).symm)) y).re := by
        filter_upwards [hev] with y hy
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hyt⟩ := hy
        have ek := hGeq _ ⟨⟨h1, h3⟩, h4⟩
        have ej := hGeq' _ ⟨⟨h2, h3⟩, h5⟩
        rw [(R.chart k).right_inv hyt] at ek
        simp only [hT, Function.comp_apply, Pi.sub_apply, Complex.sub_re]
        linarith
      rw [levi_congr hgerm w]
      exact levi_re_analytic (hGa.sub hGa') w
    have hl := hcut.levi_ge j k x ⟨hj, hx⟩ w
    have h4 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 4 * ε)
    have h0 := hSl (fderiv ℂ T (R.chart k x) w)
    rw [hbe, e1, e2, e3, e4]
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli regMax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)

noncomputable section

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)


open Classical in
theorem glue_eventually_of_close (a : Fin P.N → X → ℝ) (η : Fin P.N → X → ℝ) {Cη ε : ℝ}
    (hcut : P.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ P.mid j ∩ P.mid k, |a j x - a k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      P.glue (fun j x => a j x + 4 * ε * η j x) ε y =
        regMax ε (fun j : {j // x₀ ∈ P.mid j} => a j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      (x₀ ∉ P.mid j → y ∉ L j ∧ y ∉ closure (P.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ P.mid j
    · filter_upwards [(P.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (P.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (P.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (P.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ P.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ P.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := P.cover y
  have hk0 : x₀ ∈ P.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ P.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, P.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

end PotentialCharts

namespace BoundedPshData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

theorem smoothed_local (ρ : Mollifier D) {t : ℝ} (ht : 0 < t) (j : Fin B.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (B.chart j).target) :
    ContDiffAt ℝ ∞ (B.smoothed ρ t j) z ∧ ∀ w, 0 ≤ levi (B.smoothed ρ t j) z w := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall z t).exists_cthickening_subset_open (B.chart j).open_target hz
  rw [cthickening_closedBall hδ.le ht.le] at hδsub
  have hU'sub : ball z (δ + t) ⊆ (B.chart j).target := ball_subset_closedBall.trans hδsub
  have hpsh : IsPsh (ball z (δ + t)) (B.u j) := isPsh_mono (B.u_psh j) hU'sub
  obtain ⟨hopen, hsm, hpm, -⟩ :=
    (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ (B.u j) isOpen_ball hpsh).1 t ht
  have hz' : z ∈ shrink (ball z (δ + t)) t := closedBall_subset_ball (lt_add_of_pos_left t hδ)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ hopen
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm
  exact ⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩

theorem arg_contDiffAt (ρ : Mollifier D) (η : Fin B.N → X → ℝ) {Cη t ε : ℝ}
    (hcut : B.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin B.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ B.mid j) :
    ContDiffAt ℝ ∞ (fun y => B.phReg ρ t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by
  have hxj : x ∈ (B.chart j).source := B.mid_subset_source j hj
  have hT : ContDiffAt ℝ ∞ (B.chart j ∘ ψ.symm) (ψ x) :=
    ((analyticAt_transition hψ (B.compat j) hx hxj).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hTx : (B.chart j ∘ ψ.symm) (ψ x) = B.chart j x := by simp [ψ.left_inv hx]
  have hS := (B.smoothed_local ρ ht j (hball j x (subset_closure hj))).1
  have hq : ContDiffAt ℝ ∞ (B.q j) (B.chart j x) :=
    (B.q_smooth j).contDiffAt ((B.chart j).open_target.mem_nhds ((B.chart j).map_source hxj))
  rw [← hTx] at hS hq
  have hη := contDiffAt_comp_symm_of_smoothOn hψ (B.isOpen_mid j) (hcut.smooth j) hj hx
  exact ((hS.comp (ψ x) hT).sub (hq.comp (ψ x) hT)).add (contDiffAt_const.mul hη)

end BoundedPshData


open Classical in
theorem BoundedGlue.proof : BoundedGlue.Statement := by
  intro X _ _ _ D A B ρ η Cη t ε hcut ht hε hball hcmp
  have hloc := B.glue_eventually_of_close (fun j x => B.phReg ρ t j x) η hcut hε.le hcmp
  refine ⟨fun i y hy => ?_, fun k x hx w => ?_⟩
  ·
    have hyt : y ∈ (A.chart i).target := hy.1
    have hx₀ : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hyt
    have hψ : IsCompatChart A (A.chart i) := fun l => ⟨A.holo l i, A.holo i l⟩
    have hyx : A.chart i ((A.chart i).symm y) = y := (A.chart i).right_inv hyt
    have hG : ContDiffAt ℝ ∞ (fun y' => regMax ε (fun j : {j // (A.chart i).symm y ∈ B.mid j} =>
        B.phReg ρ t j ((A.chart i).symm y') + 4 * ε * η j ((A.chart i).symm y')) + ε / 2) y := by
      have hr := ((ReciprocityTheory.AnForm.A.regMax_thm {j // (A.chart i).symm y ∈ B.mid j}).1 ε hε).1
      refine (hr.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).add contDiffAt_const
      have := B.arg_contDiffAt ρ η (ε := ε) hcut ht hball hψ hx₀ j.2
      rwa [hyx] at this
    refine (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (((A.chart i).continuousAt_symm hyt).tendsto.eventually (hloc ((A.chart i).symm y))).mono
      fun y' hy' => hy'.2
  ·
    have hψ := B.compat k
    have hxk : x ∈ (B.chart k).source := B.mid_subset_source k hx
    have hzt : B.chart k x ∈ (B.chart k).target := (B.chart k).map_source hxk
    have hqk : ContDiffAt ℝ ∞ (B.q k) (B.chart k x) :=
      (B.q_smooth k).contDiffAt ((B.chart k).open_target.mem_nhds hzt)
    set b : {j // x ∈ B.mid j} → (Fin D → ℂ) → ℝ := fun j y =>
      B.phReg ρ t j ((B.chart k).symm y) + 4 * ε * η j ((B.chart k).symm y) + B.q k y with hb_def
    have hb : ∀ j, ContDiffAt ℝ ∞ (b j) (B.chart k x) := fun j =>
      (B.arg_contDiffAt ρ η (ε := ε) hcut ht hball hψ hxk j.2).add hqk
    have hadd := ((ReciprocityTheory.AnForm.A.regMax_thm {j // x ∈ B.mid j}).1 ε hε).2.2.2.2.2.2.1
    have hgerm : B.chartFun (B.regularised ρ t ε η) k =ᶠ[𝓝 (B.chart k x)]
        fun y => regMax ε (fun j => b j y) + ε / 2 := by
      have ht' : Tendsto (B.chart k).symm (𝓝 (B.chart k x)) (𝓝 x) := by
        have := ((B.chart k).continuousAt_symm hzt).tendsto
        rwa [(B.chart k).left_inv hxk] at this
      filter_upwards [ht'.eventually (hloc x)] with y hy
      simp only [PotentialCharts.chartFun, BoundedPshData.regularised]
      rw [hy.2, hb_def, hadd]
      ring
    have hconst : levi (fun y => regMax ε (fun j => b j y) + ε / 2) (B.chart k x) w =
        levi (fun y => regMax ε (fun j => b j y)) (B.chart k x) w := by
      unfold levi
      have : fderiv ℝ (fun y => regMax ε (fun j => b j y) + ε / 2) =
          fderiv ℝ (fun y => regMax ε (fun j => b j y)) := funext fun _ => fderiv_add_const _
      rw [this]
    rw [levi_congr hgerm w, hconst]
    have hzV : B.chart k x ∈ interior {y | ∀ j, ContDiffAt ℝ 2 (b j) y} :=
      mem_interior_iff_mem_nhds.2 (Filter.eventually_all.2 fun j =>
        ((hb j).of_le (WithTop.coe_le_coe.mpr le_top)).eventually (by simp))
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm D {j // x ∈ B.mid j} ε _ b isOpen_interior hε
      (fun j y hy => (interior_subset hy j).contDiffWithinAt) _ hzV w _ fun ⟨j, hj⟩ => ?_
    have hxj : x ∈ (B.chart j).source := B.mid_subset_source j hj
    set T := B.chart j ∘ (B.chart k).symm with hT
    have hTa : AnalyticAt ℂ T (B.chart k x) := analyticAt_transition hψ (B.compat j) hxk hxj
    have hTR : ContDiffAt ℝ ∞ T (B.chart k x) := (hTa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have hTz : T (B.chart k x) = B.chart j x := by simp [hT, (B.chart k).left_inv hxk]
    obtain ⟨hS, hSl⟩ := B.smoothed_local ρ ht j (hball j x (subset_closure hj))
    have hq : ContDiffAt ℝ ∞ (B.q j) (B.chart j x) :=
      (B.q_smooth j).contDiffAt ((B.chart j).open_target.mem_nhds ((B.chart j).map_source hxj))
    rw [← hTz] at hS hSl hq
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hS2 : ContDiffAt ℝ 2 (B.smoothed ρ t j ∘ T) (B.chart k x) := (hS.comp _ hTR).of_le h2
    have hQ2 : ContDiffAt ℝ 2 (fun y => B.q k y - B.q j (T y)) (B.chart k x) :=
      (hqk.sub (hq.comp _ hTR)).of_le h2
    have hE2 : ContDiffAt ℝ 2 (η j ∘ (B.chart k).symm) (B.chart k x) :=
      (contDiffAt_comp_symm_of_smoothOn hψ (B.isOpen_mid j) (hcut.smooth j) hj hxk).of_le h2
    have hF2 : ContDiffAt ℝ 2 (fun y => (B.smoothed ρ t j ∘ T) y + 1 * (B.q k y - B.q j (T y)))
        (B.chart k x) := hS2.add (contDiffAt_const.mul hQ2)
    have hbe : b ⟨j, hj⟩ = fun y => ((B.smoothed ρ t j ∘ T) y + 1 * (B.q k y - B.q j (T y))) +
        4 * ε * (η j ∘ (B.chart k).symm) y := by
      funext y
      simp only [hb_def, BoundedPshData.phReg, hT, Function.comp_apply]
      ring
    have e1 := levi_add_smul (4 * ε) hF2 hE2 w
    have e2 := levi_add_smul 1 hS2 hQ2 w
    have e3 := levi_comp (φ := B.smoothed ρ t j) w hTa (hS.of_le h2)

    have e4 : levi (fun y => B.q k y - B.q j (T y)) (B.chart k x) w = 0 := by
      obtain ⟨W, hWo, hxW, G, hG, hGeq⟩ := B.q_th k x x ⟨B.th.mem_U x, hxk⟩
      obtain ⟨W', hWo', hxW', G', hG', hGeq'⟩ := B.q_th j x x ⟨B.th.mem_U x, hxj⟩
      have hO : IsOpen (W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source) :=
        (((hWo.inter hWo').inter (B.th.isOpen_U x)).inter (B.chart k).open_source).inter
          (B.chart j).open_source
      have hxO : x ∈ W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source :=
        ⟨⟨⟨⟨hxW, hxW'⟩, B.th.mem_U x⟩, hxk⟩, hxj⟩
      have hev1 : ∀ᶠ y in 𝓝 (B.chart k x),
          (B.chart k).symm y ∈ W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source :=
        ((B.chart k).continuousAt_symm hzt).preimage_mem_nhds
          (by rw [(B.chart k).left_inv hxk]; exact hO.mem_nhds hxO)
      have hev := hev1.and ((B.chart k).open_target.mem_nhds hzt)
      have hGa := analyticAt_comp_symm_of_holoOn hψ hG hxW hxk
      have hGa' := analyticAt_comp_symm_of_holoOn hψ hG' hxW' hxk
      have hgerm : (fun y => B.q k y - B.q j (T y)) =ᶠ[𝓝 (B.chart k x)]
          fun y => (((G ∘ (B.chart k).symm) - (G' ∘ (B.chart k).symm)) y).re := by
        filter_upwards [hev] with y hy
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hyt⟩ := hy
        have ek := hGeq _ ⟨⟨h1, h3⟩, h4⟩
        have ej := hGeq' _ ⟨⟨h2, h3⟩, h5⟩
        rw [(B.chart k).right_inv hyt] at ek
        simp only [hT, Function.comp_apply, Pi.sub_apply, Complex.sub_re]
        linarith
      rw [levi_congr hgerm w]
      exact levi_re_analytic (hGa.sub hGa') w
    have hl := hcut.levi_ge j k x ⟨hj, hx⟩ w
    have h4 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 4 * ε)
    have h0 := hSl (fderiv ℂ T (B.chart k x) w)
    rw [hbe, e1, e2, e3, e4]
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

namespace RegChartData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)

theorem one_le_log_growth (j : Fin R.N) {y : Fin D → ℂ} (hyt : y ∈ (R.chart j).target) :
    1 ≤ Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := by
  have hy1 : ‖y‖ < 1 := by simpa using R.target_subset j hyt
  have hs : 0 ≤ ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
  have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
  rwa [Real.log_exp] at this

theorem trunc_psh_le (j : Fin R.N) {V : Set (Fin D → ℂ)} (hV : IsOpen V)
    (hVt : V ⊆ (R.chart j).target) {B : ℝ} (hB : ∀ y ∈ V \ coordDiv (R.S j), R.u j y ≤ B)
    (K : ℝ) : IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K) := by
  have hcont : ContinuousOn (R.u j) (V \ coordDiv (R.S j)) :=
    (R.continuousOn_u j).mono (sdiff_subset_sdiff_left hVt)
  have hpsh : IsPsh (V \ coordDiv (R.S j)) (R.u j) :=
    isPsh_mono (R.u_psh j) (sdiff_subset_sdiff_left hVt)
  have hbound : ∀ y ∈ V \ coordDiv (R.S j), R.u j y ≤
      |B| * Real.log (Real.exp 1 + ∑ i ∈ R.S j, Real.log ‖y i‖⁻¹) := fun y hy =>
    (hB y hy).trans ((le_abs_self B).trans
      (le_mul_of_one_le_right (abs_nonneg _) (R.one_le_log_growth j (hVt hy.1))))
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm D (R.S j) V (R.u j) |B| hV
    (hVt.trans (R.target_subset j)) hcont hpsh hbound).2 K

  have heq : EqOn (limsupExt V (coordDiv (R.S j)) (fun y => max (R.u j y) (-K)))
      (R.trunc K j) V := by
    intro y hy
    simp only [RegChartData.trunc, limsupExt]
    split_ifs with hA
    · congr 1
      rw [nhdsWithin_restrict ((R.chart j).target \ coordDiv (R.S j)) hy hV]
      congr 1
      ext v
      constructor
      · rintro ⟨hv1, hv2⟩; exact ⟨⟨hVt hv1, hv2⟩, hv1⟩
      · rintro ⟨⟨-, hv2⟩, hv1⟩; exact ⟨hv1, hv2⟩
    · rfl
  refine ⟨isPsh_congr heq hext, fun y hy => ?_⟩
  by_cases hA : y ∈ coordDiv (R.S j)
  · simp only [RegChartData.trunc, limsupExt, if_pos hA]
    have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := R.S j) (R.chart j).open_target (hVt hy)
    refine limsup_le_of_le (isCoboundedUnder_le_of_le _ fun v => le_max_right (R.u j v) (-K)) ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hy), self_mem_nhdsWithin]
      with v hv hvt
    exact max_le_max (hB v ⟨hv, hvt.2⟩) le_rfl
  · simp only [RegChartData.trunc, limsupExt, if_neg hA]
    exact max_le_max (hB y ⟨hy, hA⟩) le_rfl

end RegChartData

theorem TruncPsh.proof : TruncPsh.Statement := by
  intro X _ _ _ D A R
  have hKc : ∀ j, IsCompact (R.chart j '' closure (R.mid j)) := fun j =>
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have hKt : ∀ j, R.chart j '' closure (R.mid j) ⊆ (R.chart j).target := fun j =>
    image_subset_iff.2 fun x hx => (R.chart j).map_source (R.closure_mid j hx)
  have hε : ∀ j, ∃ ε, 0 < ε ∧
      cthickening ε (R.chart j '' closure (R.mid j)) ⊆ (R.chart j).target := fun j =>
    (hKc j).exists_cthickening_subset_open (R.chart j).open_target (hKt j)
  choose ε hεpos hεsub using hε
  have hM : ∀ j, ∃ M, ∀ y ∈ cthickening (ε j) (R.chart j '' closure (R.mid j)), R.q j y ≤ M := by
    intro j
    obtain ⟨M, hM⟩ := (hKc j).cthickening.bddAbove_image
      ((R.q_smooth j).continuousOn.mono (hεsub j))
    exact ⟨M, fun y hy => hM ⟨y, hy, rfl⟩⟩
  choose M hM using hM
  obtain ⟨δ, hδε, hδ⟩ := ((Filter.eventually_all.2 fun j =>
    (eventually_lt_nhds (hεpos j)).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0)).exists
  have hVt : ∀ j, thickening (ε j) (R.chart j '' closure (R.mid j)) ⊆ (R.chart j).target :=
    fun j => (thickening_subset_cthickening _ _).trans (hεsub j)
  refine ⟨δ, ∑ k, |M k| + |R.Cph|, hδ, fun j => ⟨_, isOpen_thickening, hVt j,
    fun x hx y hy => ?_, fun K => R.trunc_psh_le j isOpen_thickening (hVt j) ?_ K⟩⟩
  · exact mem_thickening_iff.2 ⟨_, ⟨x, subset_closure hx, rfl⟩,
      (mem_closedBall.1 hy).trans_lt (hδε j)⟩
  · intro y hy
    have h1 : R.q j y ≤ M j := hM j y (thickening_subset_cthickening _ _ hy.1)
    have h2 : R.ph ((R.chart j).symm y) ≤ R.Cph := R.ph_le _ (R.symm_mem_Yo j (hVt j hy.1) hy.2)
    have h3 : |M j| ≤ ∑ k, |M k| :=
      Finset.single_le_sum (f := fun k => |M k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have : R.u j y = R.q j y + R.ph ((R.chart j).symm y) := rfl
    rw [this]
    linarith [le_abs_self (M j), le_abs_self R.Cph]

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)

noncomputable section

namespace TruncTransfer

theorem exists_lipschitz_near {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hf : ∀ y ∈ W, ContDiffAt ℝ 1 f y) :
    ∃ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, closedBall z ε ⊆ W ∧
      ∀ y ∈ closedBall z ε, ‖f y - f z‖ ≤ C * ‖y - z‖ := by
  obtain ⟨ε, hε, hεW⟩ := hK.exists_cthickening_subset_open hW hKW
  have hc : IsCompact (cthickening ε K) := hK.cthickening
  have hcont : ContinuousOn (fderiv ℝ f) (cthickening ε K) := fun y hy =>
    ((hf y (hεW hy)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨ε, hε, max C 0, le_max_right _ _, fun z hz =>
    ⟨(closedBall_subset_cthickening hz ε).trans hεW, fun y hy => ?_⟩⟩
  have hsub := closedBall_subset_cthickening hz ε
  exact (convex_closedBall z ε).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hf w (hεW (hsub hw))).differentiableAt one_ne_zero)
    (fun w hw => (hC w (hsub hw)).trans (le_max_left _ _)) (mem_closedBall_self hε.le) hy

theorem limsupExt_max_le {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) (S : Finset (Fin D))
    (v : (Fin D → ℂ) → ℝ) (K c r : ℝ) {y : Fin D → ℂ} (hy : y ∈ U) (hr : 0 < r)
    (h : ∀ y' ∈ ball y r, y' ∈ U → y' ∉ coordDiv S → max (v y') (-K) ≤ c) :
    limsupExt U (coordDiv S) (fun y' => max (v y') (-K)) y ≤ c := by
  unfold limsupExt
  split_ifs with hyS
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S) hU hy
    refine limsup_le_of_le (isCoboundedUnder_le_of_le _ fun _ => le_max_right _ (-K)) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds y hr)] with y' hy' hb
    exact h y' hb hy'.1 hy'.2
  · exact h y (mem_ball_self hr) hy hyS

variable {D : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : FinHolAtlas D X}
  (R : RegChartData A)

theorem isCompact_chart_image (j : Fin R.N) {s : Set X} (hs : s ⊆ closure (R.mid j))
    (hsc : IsClosed s) : IsCompact (R.chart j '' s) :=
  hsc.isCompact.image_of_continuousOn ((R.chart j).continuousOn.mono (hs.trans (R.closure_mid j)))

theorem trunc_bdd (k : Fin R.N) : ∃ c > 0, ∃ M : ℝ, ∀ K : ℝ, ∀ x ∈ R.mid k, ∀ s ≤ c,
    ∀ y ∈ closedBall (R.chart k x) s, R.trunc K k y ≤ max M (-K) := by
  have hKk := isCompact_chart_image R k subset_rfl isClosed_closure
  obtain ⟨ε, hε, hεT⟩ := hKk.exists_cthickening_subset_open (R.chart k).open_target
    (image_subset_iff.2 fun x hx => (R.chart k).map_source (R.closure_mid k hx))
  have hc : IsCompact (cthickening ε (R.chart k '' closure (R.mid k))) := hKk.cthickening
  obtain ⟨Mq, hMq⟩ := hc.exists_bound_of_continuousOn ((R.q_smooth k).continuousOn.mono hεT)
  refine ⟨ε / 2, half_pos hε, Mq + R.Cph, fun K x hx s hs y hy => ?_⟩
  have hxK : R.chart k x ∈ R.chart k '' closure (R.mid k) := mem_image_of_mem _ (subset_closure hx)
  have hball := closedBall_subset_cthickening hxK ε
  have hyε : dist y (R.chart k x) ≤ ε / 2 := (mem_closedBall.1 hy).trans hs
  have hyT : y ∈ (R.chart k).target := hεT (hball (mem_closedBall.2 (by linarith)))
  refine limsupExt_max_le (R.chart k).open_target _ _ K _ _ hyT (half_pos hε)
    fun y' hy' hy'T hy'S => ?_
  have hy'c : y' ∈ cthickening ε (R.chart k '' closure (R.mid k)) :=
    hball (mem_closedBall.2 (by linarith [dist_triangle y' y (R.chart k x), mem_ball.1 hy']))
  have hq : R.q k y' ≤ Mq := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMq y' hy'c)
  have hph := R.ph_le _ (R.symm_mem_Yo k hy'T hy'S)
  refine max_le_max ?_ le_rfl
  show R.q k y' + R.ph ((R.chart k).symm y') ≤ Mq + R.Cph
  linarith

theorem pair (j k : Fin R.N) : ∃ δ₀ > 0, ∃ c₀ > 0, ∃ L₀ B₀ : ℝ, ∀ δ L B : ℝ, δ ≤ δ₀ → L * δ ≤ c₀ →
    2 * L₀ ≤ L → 1 ≤ L → B₀ ≤ B →
    ∀ K : ℝ, ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
      R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by
  set W := (R.chart j).target ∩ (R.chart j).symm ⁻¹' (R.chart k).source with hW
  have hWo : IsOpen W := (R.chart j).isOpen_inter_preimage_symm (R.chart k).open_source
  obtain ⟨τ, hτ⟩ : ∃ f : (Fin D → ℂ) → (Fin D → ℂ), f = R.chart k ∘ (R.chart j).symm := ⟨_, rfl⟩
  have hτy : ∀ y, τ y = R.chart k ((R.chart j).symm y) := fun y => by rw [hτ]; rfl
  obtain ⟨Δ, hΔ⟩ : ∃ f : (Fin D → ℂ) → ℝ, f = fun y => R.q j y - R.q k (τ y) := ⟨_, rfl⟩
  have hΔy : ∀ y, Δ y = R.q j y - R.q k (τ y) := fun y => by rw [hΔ]
  have hKc : IsCompact (R.chart j '' (closure (R.mid j) ∩ closure (R.mid k))) :=
    isCompact_chart_image R j inter_subset_left (isClosed_closure.inter isClosed_closure)
  have hKW : R.chart j '' (closure (R.mid j) ∩ closure (R.mid k)) ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    have hxj := R.closure_mid j hx.1
    refine ⟨(R.chart j).map_source hxj, ?_⟩
    show (R.chart j).symm (R.chart j x) ∈ (R.chart k).source
    rw [(R.chart j).left_inv hxj]
    exact R.closure_mid k hx.2
  have hτan : ∀ y ∈ W, AnalyticAt ℂ τ y := by
    intro y hy
    have h := analyticAt_transition (R.compat j) (R.compat k) ((R.chart j).map_target hy.1) hy.2
    rw [(R.chart j).right_inv hy.1] at h
    rwa [hτ]
  have hτc : ∀ y ∈ W, ContDiffAt ℝ 1 τ y := fun y hy =>
    (hτan y hy).restrictScalars.contDiffAt
  have hτT : ∀ y ∈ W, τ y ∈ (R.chart k).target := fun y hy => by
    rw [hτy]; exact (R.chart k).map_source hy.2
  have hΔc : ∀ y ∈ W, ContDiffAt ℝ 1 Δ y := by
    intro y hy
    have hqj : ContDiffAt ℝ 1 (R.q j) y :=
      ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hy.1)).of_le (by simp)
    have hqk : ContDiffAt ℝ 1 (R.q k) (τ y) :=
      ((R.q_smooth k).contDiffAt ((R.chart k).open_target.mem_nhds (hτT y hy))).of_le (by simp)
    rw [hΔ]
    exact hqj.sub (hqk.comp y (hτc y hy))
  obtain ⟨ε₁, hε₁, C₁, hC₁, hτL⟩ := exists_lipschitz_near hWo hKc hKW hτc
  obtain ⟨ε₂, hε₂, C₂, hC₂, hΔL⟩ := exists_lipschitz_near hWo hKc hKW hΔc
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn
    (fun y hy => (hΔc y (hKW hy)).continuousAt.continuousWithinAt)
  obtain ⟨c₀, hc₀, Mk, hMk⟩ := trunc_bdd R k
  refine ⟨min ε₁ ε₂ / 2, half_pos (lt_min hε₁ hε₂), c₀, hc₀, max C₁ C₂, B₀, ?_⟩
  intro δ L B hδ hLδ hL₀ hL1 hB K x hx t ht htδ y hy
  have hxj := R.mid_subset_source j hx.1
  have hxk := R.mid_subset_source k hx.2
  have hzK : R.chart j x ∈ R.chart j '' (closure (R.mid j) ∩ closure (R.mid k)) :=
    mem_image_of_mem _ ⟨subset_closure hx.1, subset_closure hx.2⟩
  have hτz : τ (R.chart j x) = R.chart k x := by rw [hτy, (R.chart j).left_inv hxj]
  have hΔz : Δ (R.chart j x) = R.q j (R.chart j x) - R.q k (R.chart k x) := by rw [hΔy, hτz]
  have hΔB : |Δ (R.chart j x)| ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ _ hzK
  have hLt : L * t ≤ c₀ := (mul_le_mul_of_nonneg_left htδ.le (by linarith)).trans hLδ
  have hbdd : BddAbove (R.trunc K k '' closedBall (R.chart k x) (L * t)) :=
    ⟨max Mk (-K), by rintro _ ⟨w, hw, rfl⟩; exact hMk K x hx.2 (L * t) hLt w hw⟩
  have h2t : 2 * t ≤ min ε₁ ε₂ := by linarith
  have hCL : max C₁ C₂ * (2 * t) ≤ L * t := by
    have := mul_le_mul_of_nonneg_right hL₀ ht.le
    linarith
  have hC0 : 0 ≤ max C₁ C₂ := hC₁.trans (le_max_left _ _)
  obtain ⟨hWz, hτd⟩ := hτL _ hzK
  have key : ∀ y' ∈ closedBall (R.chart j x) (2 * t), y' ∉ coordDiv (R.S j) →
      max (R.u j y') (-K) ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by
    intro y' hy' hy'S
    have hy'1 : y' ∈ closedBall (R.chart j x) ε₁ :=
      closedBall_subset_closedBall (h2t.trans (min_le_left _ _)) hy'
    have hy'2 : y' ∈ closedBall (R.chart j x) ε₂ :=
      closedBall_subset_closedBall (h2t.trans (min_le_right _ _)) hy'
    have hy'W : y' ∈ W := hWz hy'1
    have hnorm : ‖y' - R.chart j x‖ ≤ 2 * t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy'
    have hx'k : (R.chart j).symm y' ∈ (R.chart k).source := hy'W.2
    have hx'Yo : (R.chart j).symm y' ∈ R.Yo := R.symm_mem_Yo j hy'W.1 hy'S
    have hτS : τ y' ∉ coordDiv (R.S k) := by
      rw [hτy]; exact (R.mem_Yo k _ hx'k).1 hx'Yo
    have hu : R.u j y' = R.u k (τ y') + Δ y' := by
      simp only [RegChartData.u, PotentialCharts.chartFun]
      rw [hΔy, hτy, (R.chart k).left_inv hx'k]
      ring
    have htr : R.trunc K k (τ y') = max (R.u k (τ y')) (-K) := by
      rw [RegChartData.trunc, limsupExt, if_neg hτS]
    have hmem : τ y' ∈ closedBall (R.chart k x) (L * t) := by
      rw [mem_closedBall, dist_eq_norm, ← hτz]
      calc ‖τ y' - τ (R.chart j x)‖ ≤ C₁ * ‖y' - R.chart j x‖ := hτd y' hy'1
        _ ≤ max C₁ C₂ * (2 * t) :=
          mul_le_mul (le_max_left _ _) hnorm (norm_nonneg _) hC0
        _ ≤ L * t := hCL
    have hP : R.u k (τ y') ≤ polyMax (R.trunc K k) (R.chart k x) (L * t) :=
      calc R.u k (τ y') ≤ max (R.u k (τ y')) (-K) := le_max_left _ _
        _ = R.trunc K k (τ y') := htr.symm
        _ ≤ polyMax (R.trunc K k) (R.chart k x) (L * t) := le_csSup hbdd (mem_image_of_mem _ hmem)
    have hΔle : Δ y' ≤ Δ (R.chart j x) + L * t := by
      have h1 := (hΔL _ hzK).2 y' hy'2
      rw [Real.norm_eq_abs] at h1
      have h2 : C₂ * ‖y' - R.chart j x‖ ≤ max C₁ C₂ * (2 * t) :=
        mul_le_mul (le_max_right _ _) hnorm (norm_nonneg _) hC0
      linarith [le_abs_self (Δ y' - Δ (R.chart j x))]
    have hm1 := le_max_left (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B)
    have hm2 := le_max_right (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B)
    have hΔa := abs_le.1 hΔB
    have hLt0 : 0 ≤ L * t := mul_nonneg (by linarith) ht.le
    rw [hu]
    refine max_le ?_ ?_ <;> linarith
  have hyW : y ∈ W := hWz (closedBall_subset_closedBall
    (by linarith [min_le_left ε₁ ε₂] : t ≤ ε₁) hy)
  exact limsupExt_max_le (R.chart j).open_target _ _ K _ _ hyW.1 ht fun y' hy' _ hy'S =>
    key y' (mem_closedBall.2 (by
      linarith [dist_triangle y' y (R.chart j x), mem_ball.1 hy', mem_closedBall.1 hy])) hy'S

end TruncTransfer

theorem TruncTransfer.proof : TruncTransfer.Statement := by
  intro X _ _ _ D A R
  choose δ₀ hδ₀ c₀ hc₀ L₀ B₀ hP using fun j k => TruncTransfer.pair R j k
  obtain ⟨L', hL'⟩ := (Set.finite_range (fun p : Fin R.N × Fin R.N => L₀ p.1 p.2)).bddAbove
  obtain ⟨B, hB⟩ := (Set.finite_range (fun p : Fin R.N × Fin R.N => B₀ p.1 p.2)).bddAbove
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = max 1 (2 * L') := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := (Set.finite_range
    (fun p : Fin R.N × Fin R.N => max (δ₀ p.1 p.2)⁻¹ (L / c₀ p.1 p.2))).bddAbove
  have hm1 : 0 < max m 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max m 1)⁻¹, L, B, inv_pos.2 hm1, hL ▸ le_max_left _ _,
    fun K j k x hx t ht htδ y hy => ?_⟩
  have hmj : max (δ₀ j k)⁻¹ (L / c₀ j k) ≤ max m 1 :=
    (hm (Set.mem_range_self (j, k)) : _).trans (le_max_left _ _)
  refine hP j k (max m 1)⁻¹ L B ?_ ?_ ?_ (hL ▸ le_max_left _ _)
    (hB (Set.mem_range_self (j, k))) K x hx t ht htδ y hy
  · exact inv_le_of_inv_le₀ (hδ₀ j k) ((le_max_left _ _).trans hmj)
  · have h1 : L / c₀ j k ≤ max m 1 := (le_max_right _ _).trans hmj
    rw [div_le_iff₀ (hc₀ j k)] at h1
    rw [← div_eq_mul_inv, div_le_iff₀ hm1]
    linarith [mul_comm (max m 1) (c₀ j k)]
  · have h2 : L₀ j k ≤ L' := hL' (Set.mem_range_self (j, k))
    rw [hL]
    exact le_trans (by linarith) (le_max_right _ _)

end

end GroundTheory.Heights₂.Heights.Regular
end
