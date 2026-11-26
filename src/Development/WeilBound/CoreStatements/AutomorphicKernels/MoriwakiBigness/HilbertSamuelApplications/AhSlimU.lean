module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.AhSlim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueC2Explicit
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

open GroundTheory.Heights₂.Heights.AnalyticLimit (TendstoC2On)

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendstoUniformlyOn_add_small {V α : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {N : Set α} {g₀ : ℝ → α → V} {g : α → V} {l : Filter ℝ} {s : ℝ → ℝ} {q : α → V} {C : ℝ}
    (hq : ∀ z ∈ N, ‖q z‖ ≤ C) (hs : Tendsto s l (𝓝 0)) (h : TendstoUniformlyOn g₀ g l N) :
    TendstoUniformlyOn (fun t z => g₀ t z + s t • q z) g l N := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  have hs' : ∀ᶠ t in l, |s t| < ε / 2 / (|C| + 1) := by
    have := hs.eventually (Metric.ball_mem_nhds (0 : ℝ) (div_pos (half_pos hε) hC))
    filter_upwards [this] with t ht
    simpa [Real.dist_eq] using ht
  filter_upwards [h (ε / 2) (half_pos hε), hs'] with t h1 h2 z hz
  have h3 := h1 z hz
  have h4 : ‖s t • q z‖ < ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hqz : ‖q z‖ ≤ |C| + 1 := (hq z hz).trans ((le_abs_self C).trans (by linarith))
    calc |s t| * ‖q z‖ ≤ |s t| * (|C| + 1) := by gcongr
      _ < ε / 2 / (|C| + 1) * (|C| + 1) := by gcongr
      _ = ε / 2 := by field_simp
  calc dist (g z) (g₀ t z + s t • q z) ≤ dist (g z) (g₀ t z) + dist (g₀ t z) (g₀ t z + s t • q z) :=
        dist_triangle _ _ _
    _ = dist (g z) (g₀ t z) + ‖s t • q z‖ := by simp [dist_eq_norm]
    _ < ε := by linarith

theorem tendstoC2On_congr {U N : Set E} (hU : IsOpen U) (hN : N ⊆ U) {G G' : ℝ → E → ℝ} {p : E → ℝ}
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, G' t z = G t z) (hc : TendstoC2On G' p N) :
    TendstoC2On G p N := by
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N, G' t =ᶠ[𝓝 z] G t := by
    filter_upwards [h] with t ht z hz
    filter_upwards [hU.mem_nhds (hN hz)] with y hy using ht y hy
  refine ⟨hc.1.congr ?_, hc.2.1.congr ?_, hc.2.2.congr ?_⟩
  · filter_upwards [hev] with t ht z hz using (ht z hz).eq_of_nhds
  · filter_upwards [hev] with t ht z hz using (ht z hz).fderiv_eq
  · filter_upwards [hev] with t ht z hz using (ht z hz).fderiv.fderiv_eq

theorem tendstoC2On_add_small {U N : Set E} (hU : IsOpen U) (hN : N ⊆ U) (hNc : IsCompact N)
    {a : ℝ → E → ℝ} {p Q : E → ℝ} {δ : ℝ → ℝ} (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (hQ : ContDiffOn ℝ 2 Q U) (ha : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (a t) U)
    (h : TendstoC2On a p N) :
    TendstoC2On (fun t z => a t z + δ t * Q z) p N ∧
      ∃ C : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N,
        ‖fderiv ℝ (fun z => a t z + δ t * Q z) z - fderiv ℝ (a t) z‖ ≤ C * |δ t| := by
  have hD1 : ContinuousOn (fderiv ℝ Q) U := hQ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ Q)) U :=
    (hQ.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M0, hM0⟩ := hNc.exists_bound_of_continuousOn (hQ.continuousOn.mono hN)
  obtain ⟨M1, hM1⟩ := hNc.exists_bound_of_continuousOn (hD1.mono hN)
  obtain ⟨M2, hM2⟩ := hNc.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ Q)) (by exact hD2.mono hN)
  have hdiffQ : ∀ z ∈ U, DifferentiableAt ℝ Q z := fun z hz =>
    (hQ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hdiff2Q : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ Q) z := fun z hz =>
    ((hQ.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : ∀ t, ContDiffOn ℝ 2 (a t) U → ∀ z ∈ U,
      fderiv ℝ (fun z => a t z + δ t * Q z) z = fderiv ℝ (a t) z + δ t • fderiv ℝ Q z := by
    intro t ht z hz
    have hd : DifferentiableAt ℝ (a t) z :=
      (ht.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    have := (hd.hasFDerivAt.add ((hdiffQ z hz).hasFDerivAt.const_mul (δ t))).fderiv
    exact this
  have h2 : ∀ t, ContDiffOn ℝ 2 (a t) U → ∀ z ∈ U,
      fderiv ℝ (fderiv ℝ (fun z => a t z + δ t * Q z)) z =
        fderiv ℝ (fderiv ℝ (a t)) z + δ t • fderiv ℝ (fderiv ℝ Q) z := by
    intro t ht z hz
    have hev : fderiv ℝ (fun z => a t z + δ t * Q z) =ᶠ[𝓝 z]
        fun z => fderiv ℝ (a t) z + δ t • fderiv ℝ Q z := by
      filter_upwards [hU.mem_nhds hz] with y hy using h1 t ht y hy
    rw [hev.fderiv_eq]
    have hd : DifferentiableAt ℝ (fderiv ℝ (a t)) z :=
      ((ht.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    exact (hd.hasFDerivAt.add ((hdiff2Q z hz).hasFDerivAt.const_smul (δ t))).fderiv
  refine ⟨⟨?_, ?_, ?_⟩, |M1|, ?_⟩
  · have := tendstoUniformlyOn_add_small (q := Q) hM0 hδ h.1
    simpa [smul_eq_mul] using this
  · have := tendstoUniformlyOn_add_small (q := fderiv ℝ Q) hM1 hδ h.2.1
    refine this.congr ?_
    filter_upwards [ha] with t ht z hz
    exact (h1 t ht z (hN hz)).symm
  · have := tendstoUniformlyOn_add_small (q := fderiv ℝ (fderiv ℝ Q)) hM2 hδ h.2.2
    refine this.congr ?_
    filter_upwards [ha] with t ht z hz
    exact (h2 t ht z (hN hz)).symm
  · filter_upwards [ha] with t ht z hz
    rw [h1 t ht z (hN hz), add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hM1 z hz).trans (le_abs_self _)) (abs_nonneg _)

end General

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem chart_C2_convergence (A B : FinHolAtlas e X) (hAB : A.Compatible B) (jA : Fin A.n) (j : Fin B.n)
    (s : X → X → ℂ) (ph : X → ℝ) (hbd : IsClosed (bdry s)) (hph : A.SmoothOn (bdry s)ᶜ ph)
    {W' : Set X} (hW' : IsOpen W') (hWb : W' ⊆ chartBall B j (5 / 4)) (hWc : W' ⊆ (bdry s)ᶜ)
    (f : ℝ → X → ℝ) (hfs : ∀ᶠ t in 𝓝[>] (0 : ℝ), A.SmoothOn (chartBall B j (5 / 4)) (f t))
    (hconv : ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t => f t ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (f t ∘ (B.chart j).symm))
        (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t ∘ (B.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        ‖fderiv ℝ (f t ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t)
    {N : Set (Fin e → ℂ)} (hNc : IsCompact N)
    (hN : N ⊆ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W') :
    TendstoC2On (fun t => f t ∘ (A.chart jA).symm) (ph ∘ (A.chart jA).symm) N ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ N,
        ‖fderiv ℝ (f t ∘ (A.chart jA).symm) z - fderiv ℝ (ph ∘ (A.chart jA).symm) z‖ ≤ M * t := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  set W := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W' with hWdef
  have hWo : IsOpen W := (A.chart jA).isOpen_inter_preimage_symm hW'
  set U := ball (0 : Fin e → ℂ) (5 / 4) ∩
    ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ) with hUdef
  have hUo : IsOpen U :=
    isOpen_ball.inter ((B.chart j).isOpen_inter_preimage_symm hbd.isOpen_compl)
  set τ := B.chart j ∘ (A.chart jA).symm with hτdef
  have hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y := by
    intro y hy
    have ha : AnalyticAt ℂ τ y := hAB.1 jA j y ⟨hy.1, (hWb hy.2).1⟩
    have hR : AnalyticAt ℝ τ y := ha.restrictScalars
    exact hR.contDiffAt
  have hleft : ∀ y ∈ W, (B.chart j).symm (τ y) = (A.chart jA).symm y := fun y hy =>
    (B.chart j).left_inv (hWb hy.2).1
  have hWU : Set.MapsTo τ W U := by
    intro y hy
    refine ⟨(hWb hy.2).2, (B.chart j).map_source (hWb hy.2).1, ?_⟩
    show (B.chart j).symm (τ y) ∈ (bdry s)ᶜ
    rw [hleft y hy]
    exact hWc hy.2
  have hΦ : ∀ z ∈ U, ContDiffAt ℝ 2 (ph ∘ (B.chart j).symm) z := by
    intro z hz
    exact (((smoothOn_of_compatible hAB hbd.isOpen_compl hph) j).contDiffAt
      (((B.chart j).isOpen_inter_preimage_symm hbd.isOpen_compl).mem_nhds hz.2)).of_le h2
  have hG : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ U, ContDiffAt ℝ 2 (f t ∘ (B.chart j).symm) z := by
    filter_upwards [hfs] with t ht z hz
    have hz' : z ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' chartBall B j (5 / 4) := by
      refine ⟨hz.2.1, (B.chart j).map_target hz.2.1, ?_⟩
      show B.chart j ((B.chart j).symm z) ∈ ball (0 : Fin e → ℂ) (5 / 4)
      rw [(B.chart j).right_inv hz.2.1]
      exact hz.1
    exact (((smoothOn_of_compatible hAB (chartBall_isOpen B j _) ht) j).contDiffAt
      (((B.chart j).isOpen_inter_preimage_symm (chartBall_isOpen B j _)).mem_nhds hz')).of_le h2
  have hF : ∀ t, ∀ y ∈ W, (f t ∘ (A.chart jA).symm) y = (f t ∘ (B.chart j).symm) (τ y) := by
    intro t y hy
    simp only [Function.comp_apply]
    rw [hleft y hy]
  have hΨ : ∀ y ∈ W, (ph ∘ (A.chart jA).symm) y = (ph ∘ (B.chart j).symm) (τ y) := by
    intro y hy
    simp only [Function.comp_apply]
    rw [hleft y hy]
  have hτN : IsCompact (τ '' N) :=
    hNc.image_of_continuousOn fun y hy => (hτ y (hN hy)).continuousAt.continuousWithinAt
  have hτU : τ '' N ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩
    have := hWU (hN hy)
    exact ⟨this.1, this.2.2⟩
  obtain ⟨c0, c1, c2, M, hM⟩ := hconv _ hτU hτN
  refine ⟨GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.local_c2_convergence_pullback hWo hτ hWU hG hΦ hF hΨ hNc hN
    c0 c1 c2, ?_⟩
  have hτc : ContDiffOn ℝ 2 τ W := fun y hy => (hτ y hy).contDiffWithinAt
  have hD1 : ContinuousOn (fderiv ℝ τ) W := hτc.continuousOn_fderiv_of_isOpen hWo (by norm_num)
  obtain ⟨M1, hM1⟩ := hNc.exists_bound_of_continuousOn (hD1.mono hN)
  refine ⟨M * M1, ?_⟩
  filter_upwards [hM, hG] with t ht hGt z hz
  have e1 := (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.fderiv_fderiv_comp_eq hWo hτ hWU hGt
    (hF t) (hN hz)).1
  have e2 := (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.fderiv_fderiv_comp_eq hWo hτ hWU hΦ
    hΨ (hN hz)).1
  rw [e1, e2, ← ContinuousLinearMap.sub_comp]
  have h3 := ht (τ z) (Set.mem_image_of_mem τ hz)
  have h4 := hM1 z hz
  calc _ ≤ _ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (M * t) * M1 := mul_le_mul h3 h4 (norm_nonneg _) ((norm_nonneg _).trans h3)
    _ = M * M1 * t := by ring

end Chart

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

noncomputable section

section Glue

variable {e : ℕ} {X : Type} [TopologicalSpace X]

lemma glue_local_unif [T2Space X] (B : FinHolAtlas e X)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧
      (∀ j, y₀ ∈ chartBall B j (5 / 4) → W ⊆ chartBall B j (5 / 4)) ∧
      ∀ (f η : Fin B.n → X → ℝ) (δ Mb : ℝ), 0 ≤ δ → δ ≤ 1 →
        (∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) → (∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1) →
        (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
        (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
        ∀ j, y₀ ∉ chartBall B j (5 / 4) → ∀ y ∈ W,
          glueArg B f η δ Mb j y + δ ≤ glueArg B f η δ Mb k₀ y := by
  classical
  set Kc : Fin B.n → Set X := fun j => (B.chart j).symm '' closedBall (0 : Fin e → ℂ) (9 / 8)
  have hKsub : ∀ j, closedBall (0 : Fin e → ℂ) (9 / 8) ⊆ (B.chart j).target :=
    fun j => (closedBall_subset_closedBall (by norm_num)).trans (h2 j)
  have hKcl : ∀ j, IsClosed (Kc j) := fun j =>
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((B.chart j).continuousOn_symm.mono (hKsub j))).isClosed
  have hKin : ∀ j, Kc j ⊆ chartBall B j (5 / 4) := by
    rintro j _ ⟨z, hz, rfl⟩
    refine ⟨(B.chart j).map_target (hKsub j hz), ?_⟩
    rw [Set.mem_preimage, (B.chart j).right_inv (hKsub j hz)]
    exact closedBall_subset_ball (by norm_num) hz
  have hnotK : ∀ j, ∀ y, y ∉ Kc j → y ∉ chartBall B j (9 / 8) := by
    intro j y hy hb
    exact hy ⟨B.chart j y, ball_subset_closedBall hb.2, (B.chart j).left_inv hb.1⟩
  let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
  refine ⟨chartBall B k₀ 1 ∩ (⋂ j ∈ I, chartBall B j (5 / 4)) ∩ ⋂ j ∈ Iᶜ, (Kc j)ᶜ, ?_, ?_, ?_, ?_, ?_⟩
  · refine ((chartBall_isOpen B k₀ 1).inter ?_).inter ?_
    · exact isOpen_biInter_finset fun j _ => chartBall_isOpen B j _
    · exact isOpen_biInter_finset fun j _ => (hKcl j).isOpen_compl
  · refine ⟨⟨hk₀, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter]; intro j hj; simpa [I] using hj
    · simp only [Set.mem_iInter]
      intro j hj hK
      have : y₀ ∈ chartBall B j (5 / 4) := hKin j hK
      simp [I, this] at hj
  · exact fun y hy => hy.1.1
  · intro j hj y hy
    have := hy.1.2
    simp only [Set.mem_iInter] at this
    exact this j (by simpa [I] using hj)
  · intro f η δ Mb hδ0 hδ1 hη0 hη1 hMb hov j hj y hy
    have hyK : y ∉ Kc j := by
      have := hy.2
      simp only [Set.mem_iInter] at this
      exact this j (by simpa [I] using hj)
    have hy0 : y ∈ chartBall B k₀ 1 := hy.1.1
    have hy5 : y ∈ chartBall B k₀ (5 / 4) := chartBall_mono B k₀ (by norm_num) hy0
    have hk : glueArg B f η δ Mb k₀ y = f k₀ y := by
      simp [glueArg, hy5, hη0 k₀ y hy0]
    rw [hk]
    unfold glueArg
    split_ifs with hj5
    · rw [hη1 j y (hnotK j y hyK)]
      have := hov j k₀ y ⟨hj5, hy5⟩
      have := (abs_le.1 this).2
      linarith [hδ0]
    · have := (abs_le.1 (hMb k₀ y hy5)).1
      linarith

lemma glue_loc_rep [T2Space X] (B : FinHolAtlas e X) [Nonempty (Fin B.n)]
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (y₀ : X) (k₀ : Fin B.n) (hk₀ : y₀ ∈ chartBall B k₀ 1) :
    ∃ (W : Set X) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧ W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧
      (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ (f η : Fin B.n → X → ℝ) (δ Mb : ℝ), 0 < δ → δ ≤ 1 →
        (∀ j, ∀ y ∈ chartBall B j 1, η j y = 0) → (∀ j, ∀ y ∉ chartBall B j (9 / 8), η j y = -1) →
        (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
        (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
        ∀ y ∈ W, ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) =
          ReciprocityTheory.AnForm.A.regMax δ (fun j =>
            if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
  classical
  obtain ⟨W, hWo, hyW, hWk, hWin, hWout⟩ := glue_local_unif B h2 y₀ k₀ hk₀
  let I : Finset (Fin B.n) := Finset.univ.filter fun j => y₀ ∈ chartBall B j (5 / 4)
  have hk₀I : k₀ ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    exact chartBall_mono B k₀ (by norm_num) hk₀
  refine ⟨W, I, hWo, hyW, hWk, hk₀I, fun j hj => hWin j (by simpa [I] using hj), ?_⟩
  intro f η δ Mb hδ hδ1 hη0 hη1 hMb hov y hy
  have hy5 : ∀ j ∈ I, y ∈ chartBall B j (5 / 4) := fun j hj => hWin j (by simpa [I] using hj) hy
  rw [regMax_dominated (Fin B.n) δ _ k₀ I hδ hk₀I (fun j hj =>
    hWout f η δ Mb hδ.le hδ1 hη0 hη1 hMb hov j (by simpa [I] using hj) y hy)]
  congr 1
  funext j
  have hk5 := hy5 k₀ hk₀I
  by_cases hj : j ∈ I
  · simp [hj, glueArg, hy5 j hj]
  · simp [hj, glueArg, hk5]

theorem reg_glue_explicit [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) [Nonempty (Fin B.n)]
    (Θ th : LocPot X) (hAB : A.Compatible B) (hcov : ∀ x, ∃ j, x ∈ chartBall B j 1)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hΘ : IsPotential A Θ) (hΘpos : IsPosPot A Θ) (hth : IsPotential A th)
    (η : Fin B.n → X → ℝ)
    (hη : ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (δ Mb : ℝ) (f : Fin B.n → X → ℝ), 0 < δ → δ ≤ 1 →
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f j)) →
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f j y| ≤ Mb) →
      (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f j))) →
      (∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f j y - f k y| ≤ δ) →
      A.Smooth (fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y)) ∧
      (∀ c₀ : ℝ, IsPsh A (th + LocPot.ofFun
        (fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) + c₀) +
          Θ.rsmul (2 * K * δ))) ∧
      ∀ j, ∀ y ∈ chartBall B j (5 / 4),
        |ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) - f j y| ≤ K * δ := by
  classical
  have hηs : ∀ j, A.Smooth (η j) := fun j => (hη j).1

  have hC : ∀ j, ∃ C : ℝ, IsPsh A (LocPot.ofFun (η j) + Θ.rsmul C) := fun j =>
    pshShift A Θ hΘ hΘpos (η j) (hηs j)
  choose Cj hCj using hC
  set K' : ℝ := ∑ j, |Cj j| with hK'
  have hK'ge : ∀ j, Cj j ≤ K' := fun j =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j))
  have hK'0 : 0 ≤ K' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨4 * K' + 2, by linarith, ?_⟩
  intro δ Mb f hδ hδ1 hfs hMb hfp hov
  set F : X → ℝ := fun y => ReciprocityTheory.AnForm.A.regMax δ (fun j => glueArg B f η δ Mb j y) with hF

  have hRM := (ReciprocityTheory.AnForm.A.regMax_thm (Fin B.n)).1 δ hδ

  have hΘlevi : ∀ x jA, ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' Θ.U x, ∀ w : Fin e → ℂ,
      0 ≤ levi (Θ.φ x ∘ (A.chart jA).symm) y w := by
    intro x jA y hy w
    by_cases hw : w = 0
    · subst hw; simp [levi_zero]
    · exact (hΘpos x jA y hy w hw).le

  have hloc : ∀ y₀ : X, ∃ (W : Set X) (k₀ : Fin B.n) (I : Finset (Fin B.n)), IsOpen W ∧ y₀ ∈ W ∧
      W ⊆ chartBall B k₀ 1 ∧ k₀ ∈ I ∧ (∀ j ∈ I, W ⊆ chartBall B j (5 / 4)) ∧
      ∀ y ∈ W, F y = ReciprocityTheory.AnForm.A.regMax δ (fun j =>
        if j ∈ I then f j y + 4 * δ * η j y else f k₀ y + 4 * δ * η k₀ y - δ) := by
    intro y₀
    obtain ⟨k₀, hk₀⟩ := hcov y₀
    obtain ⟨W, I, hWo, hyW, hWk, hk₀I, hWI, hrep⟩ := glue_loc_rep B h2 y₀ k₀ hk₀
    exact ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, fun y hy => hrep f η δ Mb hδ hδ1
      (fun j => (hη j).2.2.1) (fun j => (hη j).2.2.2) hMb hov y hy⟩

  have hbd : ∀ j, ∀ y ∈ chartBall B j (5 / 4), |F y - f j y| ≤ (4 * K' + 2) * δ := by
    intro j y hy
    have hup : ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) ≤ f j y + δ := by
      apply ReciprocityTheory.AnForm.A.tmax_le
      intro j'
      unfold glueArg
      split_ifs with h'
      · have h1 := (abs_le.1 (hov j' j y ⟨h', hy⟩)).2
        have h2' : 4 * δ * η j' y ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) ((hη j').2.1 y).2
        linarith
      · have := (abs_le.1 (hMb j y hy)).1
        linarith
    obtain ⟨k, hk⟩ := hcov y
    have hk5 : y ∈ chartBall B k (5 / 4) := chartBall_mono B k (by norm_num) hk
    have hlow : f j y - δ ≤ ReciprocityTheory.AnForm.A.tmax (fun j' => glueArg B f η δ Mb j' y) := by
      refine le_trans ?_ (ReciprocityTheory.AnForm.A.le_tmax _ k)
      have : glueArg B f η δ Mb k y = f k y := by
        simp [glueArg, hk5, (hη k).2.2.1 y hk]
      rw [this]
      have := (abs_le.1 (hov j k y ⟨hy, hk5⟩)).2
      linarith
    have h1 := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).1
    have h2' := (hRM.2.2.2.1 (fun j' => glueArg B f η δ Mb j' y)).2
    have hF' : F y = ReciprocityTheory.AnForm.A.regMax δ (fun j' => glueArg B f η δ Mb j' y) := rfl
    rw [abs_le]
    constructor <;> nlinarith

  have hsm : ∀ (jA : Fin A.n) (g : X → ℝ) (U : Set X), IsOpen U → A.SmoothOn U g →
      ∀ y ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' U,
        ContDiffAt ℝ ∞ (g ∘ (A.chart jA).symm) y := fun jA g U hU hg y hy =>
    (hg jA).contDiffAt (((A.chart jA).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hsmη : ∀ (jA : Fin A.n) (j : Fin B.n), ∀ y ∈ (A.chart jA).target,
      ContDiffAt ℝ ∞ (η j ∘ (A.chart jA).symm) y := fun jA j y hy =>
    hsm jA (η j) Set.univ isOpen_univ (hηs j) y ⟨hy, trivial⟩
  refine ⟨?_, ?_, hbd⟩
  ·
    intro jA y' hy'
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    have hV : (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W ∈ nhds y' :=

      ((A.chart jA).isOpen_inter_preimage_symm hWo).mem_nhds ⟨hyt, hyW⟩
    let G : (Fin e → ℂ) → (Fin B.n → ℝ) := fun z j =>
      if j ∈ I then f j ((A.chart jA).symm z) + 4 * δ * η j ((A.chart jA).symm z)
      else f k₀ ((A.chart jA).symm z) + 4 * δ * η k₀ ((A.chart jA).symm z) - δ
    have hG : ContDiffAt ℝ ∞ G y' := by
      refine contDiffAt_pi.2 fun j => ?_
      by_cases hj : j ∈ I
      · simp only [G, hj, if_true]
        exact (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) y' ⟨hyt, hWI j hj hyW⟩).add
          (contDiffAt_const.mul (hsmη jA j y' hyt))
      · simp only [G, hj, if_false]
        exact ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
          ⟨hyt, hWI k₀ hk₀I hyW⟩).add (contDiffAt_const.mul (hsmη jA k₀ y' hyt))).sub
          contDiffAt_const
    have hcomp : ContDiffAt ℝ ∞ (ReciprocityTheory.AnForm.A.regMax δ ∘ G) y' := hRM.1.contDiffAt.comp y' hG
    refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hV] with z hz
    exact hWeq _ hz.2
  ·
    intro c₀ x jA y' hy' w
    have hyt : y' ∈ (A.chart jA).target := hy'.1
    have hyth : (A.chart jA).symm y' ∈ th.U x := hy'.2.1.1
    have hyΘ : (A.chart jA).symm y' ∈ Θ.U x := hy'.2.2
    obtain ⟨W, k₀, I, hWo, hyW, hWk, hk₀I, hWI, hWeq⟩ := hloc ((A.chart jA).symm y')
    set c : ℝ := 2 * (4 * K' + 2) * δ with hc
    set V := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (W ∩ th.U x ∩ Θ.U x) with hVdef
    have hVo : IsOpen V :=
      (A.chart jA).isOpen_inter_preimage_symm ((hWo.inter (th.isOpen_U x)).inter (Θ.isOpen_U x))
    have hyV : y' ∈ V := ⟨hyt, ⟨hyW, hyth⟩, hyΘ⟩
    let P : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      th.φ x ((A.chart jA).symm z) + (if j ∈ I then f j ((A.chart jA).symm z)
        else f k₀ ((A.chart jA).symm z) - δ)
    let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
      if j ∈ I then η j ((A.chart jA).symm z) else η k₀ ((A.chart jA).symm z)
    let R : (Fin e → ℂ) → ℝ := fun z => Θ.φ x ((A.chart jA).symm z)
    let u : Fin B.n → (Fin e → ℂ) → ℝ := fun j z => ((P j z + 4 * δ * Q j z) + c * R z) + c₀

    have hPs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (P j) z := by
      intro j z hz
      have hzt : z ∈ (A.chart jA).target := hz.1
      have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) z :=
        contDiffAt_of_isPotential A th hth x jA ⟨hzt, hz.2.1.2⟩
      by_cases hj : j ∈ I
      · simp only [P, hj, if_true]
        exact h1.add (hsm jA (f j) _ (chartBall_isOpen B j _) (hfs j) z ⟨hzt, hWI j hj hz.2.1.1⟩)
      · simp only [P, hj, if_false]
        exact h1.add ((hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) z
          ⟨hzt, hWI k₀ hk₀I hz.2.1.1⟩).sub contDiffAt_const)
    have hQs : ∀ j, ∀ z ∈ V, ContDiffAt ℝ ∞ (Q j) z := by
      intro j z hz
      by_cases hj : j ∈ I
      · simp only [Q, hj, if_true]; exact hsmη jA j z hz.1
      · simp only [Q, hj, if_false]; exact hsmη jA k₀ z hz.1
    have hRs : ∀ z ∈ V, ContDiffAt ℝ ∞ R z := fun z hz =>
      contDiffAt_of_isPotential A Θ hΘ x jA ⟨hz.1, hz.2.2⟩
    have hus : ∀ j, ContDiffOn ℝ 2 (u j) V := by
      intro j z hz
      exact (((((hPs j z hz).add (contDiffAt_const.mul (hQs j z hz))).add
        (contDiffAt_const.mul (hRs z hz))).add contDiffAt_const).of_le (by norm_cast)).contDiffWithinAt

    have heq : ((th + LocPot.ofFun (fun y => F y + c₀) + Θ.rsmul c).φ x ∘ (A.chart jA).symm) =ᶠ[nhds y']
        (fun z => ReciprocityTheory.AnForm.A.regMax δ (fun j => u j z)) := by
      filter_upwards [hVo.mem_nhds hyV] with z hz
      have hF' := hWeq _ hz.2.1.1
      show th.φ x ((A.chart jA).symm z) + (F ((A.chart jA).symm z) + c₀) +
          c * Θ.φ x ((A.chart jA).symm z) = _
      rw [hF']
      set C0 : ℝ := th.φ x ((A.chart jA).symm z) + c * Θ.φ x ((A.chart jA).symm z) + c₀ with hC0
      have htr := hRM.2.2.2.2.2.2.1 (fun j => if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) C0
      have hu : (fun j => u j z) = (fun j => (if j ∈ I then f j ((A.chart jA).symm z) +
          4 * δ * η j ((A.chart jA).symm z) else f k₀ ((A.chart jA).symm z) +
          4 * δ * η k₀ ((A.chart jA).symm z) - δ) + C0) := by
        funext j
        by_cases hj : j ∈ I
        · simp only [u, P, Q, R, hj, if_true, hC0]; ring
        · simp only [u, P, Q, R, hj, if_false, hC0]; ring
      rw [hu, htr, hC0]
      ring
    rw [levi_congr heq w]
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm e (Fin B.n) δ V u hVo hδ hus y' hyV w 0 ?_
    intro j

    have hP2 := (hPs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hQ2 := (hQs j y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hR2 := (hRs y' hyV).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_cast)
    have hl1 : levi (u j) y' w = levi (P j) y' w + 4 * δ * levi (Q j) y' w + c * levi R y' w := by
      have e1 : levi (fun z => P j z + 4 * δ * Q j z) y' w =
          levi (P j) y' w + 4 * δ * levi (Q j) y' w := levi_add_smul (4 * δ) hP2 hQ2 w
      have e2 : levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w =
          levi (fun z => P j z + 4 * δ * Q j z) y' w + c * levi R y' w :=
        levi_add_smul c (hP2.add (contDiffAt_const.mul hQ2)) hR2 w
      have e3 : levi (fun z => ((P j z + 4 * δ * Q j z) + c * R z) +
            c₀ * (fun _ : Fin e → ℂ => (1 : ℝ)) z) y' w =
          levi (fun z => (P j z + 4 * δ * Q j z) + c * R z) y' w +
            c₀ * levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w :=
        levi_add_smul c₀ ((hP2.add (contDiffAt_const.mul hQ2)).add (contDiffAt_const.mul hR2))
          contDiffAt_const w
      have h00 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
      have hue : u j = fun z => ((P j z + 4 * δ * Q j z) + c * R z) +
          c₀ * (fun _ : Fin e → ℂ => (1 : ℝ)) z := by
        funext z; simp [u]
      rw [hue, e3, e2, e1, h00]; ring
    have hRl : 0 ≤ levi R y' w := hΘlevi x jA y' ⟨hyt, hyΘ⟩ w

    have hPl : 0 ≤ levi (P j) y' w := by
      by_cases hj : j ∈ I
      · have := hfp j x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI j hj hyW⟩ w
        have hPe : P j = (th + LocPot.ofFun (f j)).φ x ∘ (A.chart jA).symm := by
          funext z; simp only [P, hj, if_true]; rfl
        rw [hPe]; exact this
      · have := hfp k₀ x jA y' ⟨hyt, ⟨hyth, trivial⟩, hWI k₀ hk₀I hyW⟩ w
        have hg2 : ContDiffAt ℝ 2 ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) y' := by
          have h1 : ContDiffAt ℝ ∞ (th.φ x ∘ (A.chart jA).symm) y' :=
            contDiffAt_of_isPotential A th hth x jA ⟨hyt, hyth⟩
          exact (h1.add (hsm jA (f k₀) _ (chartBall_isOpen B k₀ _) (hfs k₀) y'
            ⟨hyt, hWI k₀ hk₀I hyW⟩)).of_le (by norm_cast)
        have hPe : P j = fun z => ((th + LocPot.ofFun (f k₀)).φ x ∘ (A.chart jA).symm) z +
            (-δ) * (fun _ => (1 : ℝ)) z := by
          funext z; simp only [P, hj, if_false]; show _ = th.φ x _ + f k₀ _ + _; ring
        rw [hPe, levi_add_smul (-δ) hg2 contDiffAt_const w]
        have h0 : levi (fun _ : Fin e → ℂ => (1 : ℝ)) y' w = 0 := by simp [levi]
        rw [h0]; linarith

    have hQl : 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
      have key : ∀ j', Q j = η j' ∘ (A.chart jA).symm → 0 ≤ levi (Q j) y' w + K' * levi R y' w := by
        intro j' hQe
        have h0 := hCj j' x jA y' ⟨hyt, ⟨trivial, hyΘ⟩⟩ w
        have hQR : (LocPot.ofFun (η j') + Θ.rsmul (Cj j')).φ x ∘ (A.chart jA).symm =
            fun z => (η j' ∘ (A.chart jA).symm) z + Cj j' * R z := rfl
        rw [hQR, levi_add_smul (Cj j') (hsmη jA j' y' hyt |>.of_le (by norm_cast)) hR2 w] at h0
        rw [hQe]
        nlinarith [hK'ge j']
      by_cases hj : j ∈ I
      · exact key j (by funext z; simp [Q, hj])
      · exact key k₀ (by funext z; simp [Q, hj])
    rw [hl1]
    have : 0 ≤ 4 * δ * (levi (Q j) y' w + K' * levi R y' w) := by positivity
    have h2δ : 0 ≤ (4 * K' + 4) * δ * levi R y' w :=
      mul_nonneg (mul_nonneg (by linarith) hδ.le) hRl
    have hcv : c = 2 * (4 * K' + 2) * δ := hc
    rw [hcv]
    nlinarith

end Glue

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

open GroundTheory.Heights₂.Heights.AnalyticLimit (TendstoC2On)

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem glue_C2_local [T2Space X] (A B : FinHolAtlas e X) [Nonempty (Fin B.n)] (s : X → X → ℂ)
    (ph : X → ℝ) (hAB : A.Compatible B) (hcov : ∀ x, ∃ j, x ∈ chartBall B j 1)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hbd : IsClosed (bdry s)) (hph : A.SmoothOn (bdry s)ᶜ ph) (η : Fin B.n → X → ℝ)
    (hη : ∀ j, A.Smooth (η j) ∧ (∀ y, -1 ≤ η j y ∧ η j y ≤ 0) ∧
      (∀ y ∈ chartBall B j 1, η j y = 0) ∧ ∀ y ∉ chartBall B j (9 / 8), η j y = -1)
    (K₀ t₀ : ℝ) (δ Mb : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ) (ht₀ : 0 < t₀)
    (hδ : Tendsto δ (𝓝[>] 0) (𝓝 0))
    (H : ∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧
      (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧
      (∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb t) ∧
      ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t)
    (hc : ∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm))
        (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧
      ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K',
        ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t)
    (jA : Fin A.n) (z₀ : Fin e → ℂ)
    (hz₀ : z₀ ∈ (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (bdry s)ᶜ) :
    ∃ N ∈ 𝓝 z₀, TendstoC2On (fun t => (fun y => ReciprocityTheory.AnForm.A.regMax (δ t)
        (fun j => glueArg B (f t) η (δ t) (Mb t) j y) + K₀ * δ t) ∘ (A.chart jA).symm)
      (ph ∘ (A.chart jA).symm) N := by
  classical
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ t₀ := by
    filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht using ht
  have h2' : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  obtain ⟨k₀, hk₀⟩ := hcov ((A.chart jA).symm z₀)
  obtain ⟨W, I, hWo, hyW, hWk, hk₀I, hWI, hrep⟩ := glue_loc_rep B h2 _ k₀ hk₀
  set W' := W ∩ (bdry s)ᶜ with hW'def
  have hW'o : IsOpen W' := hWo.inter hbd.isOpen_compl
  set U := (A.chart jA).target ∩ (A.chart jA).symm ⁻¹' W' with hUdef
  have hUo : IsOpen U := (A.chart jA).isOpen_inter_preimage_symm hW'o
  have hzU : z₀ ∈ U := ⟨hz₀.1, hyW, hz₀.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hUo.mem_nhds hzU)
  set N := closedBall z₀ (r / 2) with hNdef
  have hNU : N ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hNc : IsCompact N := isCompact_closedBall _ _
  refine ⟨N, closedBall_mem_nhds z₀ (half_pos hr), ?_⟩
  set p := ph ∘ (A.chart jA).symm with hp
  have hpC : ContDiffOn ℝ 2 p U :=
    ((hph jA).of_le h2').mono fun z hz => ⟨hz.1, hz.2.2⟩
  let b : Fin B.n → Fin B.n := fun j => if j ∈ I then j else k₀
  have hb : ∀ j, b j ∈ I := by
    intro j
    by_cases hj : j ∈ I
    · simpa [b, hj] using hj
    · simpa [b, hj] using hk₀I
  have hWb : ∀ j, W' ⊆ chartBall B (b j) (5 / 4) := fun j y hy => hWI _ (hb j) hy.1
  let Q : Fin B.n → (Fin e → ℂ) → ℝ := fun j z =>
    4 * η (b j) ((A.chart jA).symm z) - (if j ∈ I then 0 else 1)
  have hQ : ∀ j, ContDiffOn ℝ 2 (Q j) U := by
    intro j
    have h1 : ContDiffOn ℝ 2 (η (b j) ∘ (A.chart jA).symm) U :=
      (((hη (b j)).1 jA).of_le h2').mono fun z hz => ⟨hz.1, trivial⟩
    exact (contDiffOn_const.mul h1).sub contDiffOn_const
  have hsm : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ContDiffOn ℝ 2 (f t (b j) ∘ (A.chart jA).symm) U :=
    fun t h0 h1 j => (((H t h0 h1).2.2.1 (b j) jA).of_le h2').mono
      fun z hz => ⟨hz.1, hWb j hz.2⟩
  have hsmE : ∀ j, ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2 (f t (b j) ∘ (A.chart jA).symm) U :=
    fun j => ev.mono fun t ht => hsm t ht.1 ht.2 j
  have hA := fun j => chart_C2_convergence A B hAB jA (b j) s ph hbd hph hW'o (hWb j)
    Set.inter_subset_right (fun t => f t (b j))
    (ev.mono fun t ht => (H t ht.1 ht.2).2.2.1 (b j)) (hc (b j)) hNc hNU
  have hAdd := fun j => tendstoC2On_add_small hUo hNU hNc hδ (hQ j) (hsmE j) (hA j).1
  choose M hM using fun j => (hA j).2
  choose C hC using fun j => (hAdd j).2
  let u : ℝ → Fin B.n → (Fin e → ℂ) → ℝ := fun t j z =>
    (f t (b j) ∘ (A.chart jA).symm) z + δ t * Q j z
  let M' : ℝ := ∑ j, (|C j| + |M j|)
  have hM'0 : ∀ j, |C j| + |M j| ≤ M' := fun j =>
    Finset.single_le_sum (f := fun j => |C j| + |M j|) (fun _ _ => by positivity) (Finset.mem_univ j)
  have hgrad : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ N,
      ‖fderiv ℝ (u t j) x - fderiv ℝ p x‖ ≤ M' * δ t := by
    filter_upwards [ev, eventually_all.2 hM, eventually_all.2 hC] with t ht h1 h3 j x hx
    have hle := (H t ht.1 ht.2).1
    have hpos : 0 < δ t := ht.1.trans_le hle
    have a1 := h3 j x hx
    have a2 := h1 j x hx
    have a3 : C j * |δ t| ≤ |C j| * δ t := by
      rw [abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have a4 : M j * t ≤ |M j| * δ t :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) ht.1.le).trans
        (mul_le_mul_of_nonneg_left hle (abs_nonneg _))
    have a5 : (|C j| + |M j|) * δ t ≤ M' * δ t := mul_le_mul_of_nonneg_right (hM'0 j) hpos.le
    calc ‖fderiv ℝ (u t j) x - fderiv ℝ p x‖
        = ‖(fderiv ℝ (u t j) x - fderiv ℝ (f t (b j) ∘ (A.chart jA).symm) x) +
            (fderiv ℝ (f t (b j) ∘ (A.chart jA).symm) x - fderiv ℝ p x)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ C j * |δ t| + M j * t := add_le_add a1 a2
      _ ≤ M' * δ t := by nlinarith
  have hratio : Tendsto (fun t => (M' * δ t) ^ 2 / δ t) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t => M' ^ 2 * δ t) (𝓝[>] 0) (𝓝 0) := by
      simpa using hδ.const_mul (M' ^ 2)
    refine h0.congr' ?_
    filter_upwards [ev] with t ht
    have hpos : 0 < δ t := ht.1.trans_le (H t ht.1 ht.2).1
    field_simp
  have hucd : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ContDiffOn ℝ 2 (u t j) U :=
    fun t h0 h1 j => (hsm t h0 h1 j).add (contDiffOn_const.mul (hQ j))
  have hreg := GroundTheory.Heights₂.Heights.AnalyticLimit.RegularizedMaxConvergenceC2.proof (Fin B.n) U N p u δ
    (fun t => M' * δ t) hUo hNU hpC
    (ev.mono fun t ht => ⟨ht.1.trans_le (H t ht.1 ht.2).1, hucd t ht.1 ht.2⟩) hδ
    (fun j => (hAdd j).1) hgrad hratio
  have hevA : ∀ᶠ t in 𝓝[>] (0 : ℝ), ContDiffOn ℝ 2
      (fun x => ReciprocityTheory.AnForm.A.regMax (δ t) (fun j => u t j x) + δ t / 2) U := by
    filter_upwards [ev] with t ht
    have hpos : 0 < δ t := ht.1.trans_le (H t ht.1 ht.2).1
    exact (((ReciprocityTheory.AnForm.A.regMax_contDiff (ι := Fin B.n) hpos).of_le
      ReciprocityTheory.AnForm.A.two_le_inf).comp_contDiffOn (contDiffOn_pi.2 (hucd t ht.1 ht.2))).add
      contDiffOn_const
  have hfin := (tendstoC2On_add_small hUo hNU hNc hδ (Q := fun _ => K₀ - 1 / 2) contDiffOn_const
    hevA hreg).1
  refine tendstoC2On_congr hUo hNU ?_ hfin
  filter_upwards [ev] with t ht z hz
  obtain ⟨hle, hle1, -, hMb, hov⟩ := H t ht.1 ht.2
  have hpos : 0 < δ t := ht.1.trans_le hle
  have hr1 := hrep (f t) η (δ t) (Mb t) hpos hle1 (fun j => (hη j).2.2.1)
    (fun j => (hη j).2.2.2) hMb hov ((A.chart jA).symm z) hz.2.1
  have hu : (fun j => u t j z) = fun j => if j ∈ I then
      f t j ((A.chart jA).symm z) + 4 * δ t * η j ((A.chart jA).symm z)
      else f t k₀ ((A.chart jA).symm z) + 4 * δ t * η k₀ ((A.chart jA).symm z) - δ t := by
    funext j
    by_cases hj : j ∈ I
    · simp only [u, Q, b, hj, if_true, Function.comp_apply]; ring
    · simp only [u, Q, b, hj, if_false, Function.comp_apply]; ring
  simp only [Function.comp_apply]
  rw [hu, hr1]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GlobalTheory.CompanionTheory.Ar.Giv.GlueC2

theorem regularization_glue_C2 : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (Θ th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ), A.Compatible B → (∀ x, ∃ j, x ∈ chartBall B j 1) → (∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target) → IsPotential A Θ → IsPosPot A Θ → IsPotential A th → IsClosed (bdry s) → A.SmoothOn (bdry s)ᶜ ph → ∃ K : ℝ, 0 < K ∧ ∀ (t₀ : ℝ) (δ : ℝ → ℝ) (f : ℝ → Fin B.n → X → ℝ), 0 < t₀ → Tendsto δ (𝓝[>] 0) (𝓝 0) → (∀ t, 0 < t → t ≤ t₀ → t ≤ δ t ∧ δ t ≤ 1 ∧ (∀ j, A.SmoothOn (chartBall B j (5 / 4)) (f t j)) ∧ (∃ Mb : ℝ, ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb) ∧ (∀ j, IsPshOn A (chartBall B j (5 / 4)) (th + LocPot.ofFun (f t j))) ∧ ∀ j k, ∀ y ∈ chartBall B j (5 / 4) ∩ chartBall B k (5 / 4), |f t j y - f t k y| ≤ δ t) → (∀ j, ∀ K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) ∩ (B.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K' → TendstoUniformlyOn (fun t => f t j ∘ (B.chart j).symm) (ph ∘ (B.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (f t j ∘ (B.chart j).symm)) (fderiv ℝ (ph ∘ (B.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (f t j ∘ (B.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph ∘ (B.chart j).symm))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (f t j ∘ (B.chart j).symm) z - fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤ M * t) → ∃ F : ℝ → X → ℝ, (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * δ t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * δ t) ∧ IsRegFamilyC2 A s ph F := by
  intro e X _ _ _ A B Θ th s ph hAB hcov h2 hΘ hΘpos hth hbd hph
  obtain ⟨η, hη⟩ := glue_cutoff A B hAB h2
  by_cases hne : Nonempty (Fin B.n)
  swap
  · have hX : IsEmpty X := ⟨fun x => hne ⟨(hcov x).choose⟩⟩
    refine ⟨1, one_pos, fun t₀ δ f _ _ _ _ => ⟨fun _ _ => 0, fun t _ _ => ⟨?_, ?_, ?_⟩, ?_⟩⟩
    · exact fun k y _ => (hX.false ((A.chart k).symm y)).elim
    · exact fun x => (hX.false x).elim
    · exact fun j y _ => (hX.false y).elim
    · exact fun j => (hX.false ((A.chart j).symm 0)).elim
  obtain ⟨K₀, hK₀, hG⟩ := reg_glue_explicit A B Θ th hAB hcov h2 hΘ hΘpos hth η hη
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro t₀ δ f ht₀ hδ H hc
  have hMbE : ∀ t, ∃ Mb : ℝ, 0 < t → t ≤ t₀ →
      ∀ j, ∀ y ∈ chartBall B j (5 / 4), |f t j y| ≤ Mb := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ t₀
    · obtain ⟨Mb, h⟩ := (H t ht.1 ht.2).2.2.2.1
      exact ⟨Mb, fun _ _ => h⟩
    · exact ⟨0, fun h1 h3 => (ht ⟨h1, h3⟩).elim⟩
  choose Mb hMb using hMbE
  refine ⟨fun t y => ReciprocityTheory.AnForm.A.regMax (δ t)
    (fun j => glueArg B (f t) η (δ t) (Mb t) j y) + K₀ * δ t, ?_, ?_⟩
  · intro t h0 h1
    obtain ⟨hle, hle1, hsm, -, hps, hov⟩ := H t h0 h1
    have hpos : 0 < δ t := h0.trans_le hle
    obtain ⟨s1, s2, s3⟩ := hG (δ t) (Mb t) (f t) hpos hle1 hsm (hMb t h0 h1) hps hov
    refine ⟨fun k => (s1 k).add contDiffOn_const, s2 _, fun j y hy => ?_⟩
    have := abs_le.1 (s3 j y hy)
    constructor <;> linarith [this.1, this.2]
  · intro jA K hKs hKc
    have hO : IsOpen ((A.chart jA).target ∩ (A.chart jA).symm ⁻¹' (bdry s)ᶜ) :=
      (A.chart jA).isOpen_inter_preimage_symm hbd.isOpen_compl
    have hloc := fun z hz => glue_C2_local A B s ph hAB hcov h2 hbd hph η hη K₀ t₀ δ Mb f ht₀ hδ
      (fun t h0 h1 => ⟨(H t h0 h1).1, (H t h0 h1).2.1, (H t h0 h1).2.2.1, hMb t h0 h1,
        (H t h0 h1).2.2.2.2.2⟩) (fun j K' hK' hK'c => hc j K' hK' hK'c) jA z hz
    refine ⟨?_, ?_, ?_⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, h, -, -⟩ := hloc y hy
      exact ⟨N, hN, h⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, -, h, -⟩ := hloc y hy
      exact ⟨N, hN, h⟩
    · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hO).1
        (GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds
          fun y hy => ?_) K hKs hKc
      obtain ⟨N, hN, -, -, h⟩ := hloc y hy
      exact ⟨N, hN, h⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.RefineAdaptedAtlasWithGradient
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem rLoc_rescale_bound {e : ℕ} (S : Finset (Fin e)) (m : Fin e → ℕ) (z₀ : Fin e → ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hz₀ : ‖z₀‖ < 1) (hfar : ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖) :
    ∃ c : ℝ, ∀ w ∈ closedBall (0 : Fin e → ℂ) 2, (∀ i ∈ S, z₀ i = 0 → w i ≠ 0) →
      |rLoc S m ((ρ : ℂ) • w + z₀) - rLoc (S.filter (fun i => z₀ i = 0)) m w| ≤ c := by
  classical
  set K : ℝ := Real.log (4 / ρ ^ 2) with hK
  refine ⟨∑ i ∈ S, (m i : ℝ) * K, fun w hw hne => ?_⟩
  have hw' : ∀ i, ‖w i‖ ≤ 2 := fun i =>
    (norm_le_pi_norm w i).trans (by simpa using hw)
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hone : (1 : ℝ) ≤ 1 / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]; nlinarith
  have hlog1 : Real.log (1 / ρ ^ 2) ≤ K :=
    Real.log_le_log (by positivity) (by
      apply div_le_div_of_nonneg_right (by norm_num) hρ2.le)
  have hlog0 : 0 ≤ Real.log (1 / ρ ^ 2) := Real.log_nonneg hone
  have hterm : ∀ i ∈ S, |(m i : ℝ) * Real.log (4 / ‖((ρ : ℂ) • w + z₀) i‖ ^ 2) -
      (if z₀ i = 0 then (m i : ℝ) * Real.log (4 / ‖w i‖ ^ 2) else 0)| ≤ (m i : ℝ) * K := by
    intro i hi
    have hm0 : (0 : ℝ) ≤ m i := Nat.cast_nonneg _
    have hzi : ((ρ : ℂ) • w + z₀) i = (ρ : ℂ) * w i + z₀ i := by simp
    by_cases h0 : z₀ i = 0
    · have hwi : ‖w i‖ ≠ 0 := norm_ne_zero_iff.2 (hne i hi h0)
      have hwp : 0 < ‖w i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwi)
      have hn : ‖((ρ : ℂ) • w + z₀) i‖ = ρ * ‖w i‖ := by
        rw [hzi, h0, add_zero, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
      have hsplit : Real.log (4 / (ρ * ‖w i‖) ^ 2) =
          Real.log (4 / ‖w i‖ ^ 2) + Real.log (1 / ρ ^ 2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [if_pos h0, hn, hsplit, mul_add, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hlog1 hm0
    · have hfi := hfar i h0
      have hz1 : ‖z₀ i‖ < 1 := (norm_le_pi_norm z₀ i).trans_lt hz₀
      have hρw : ‖(ρ : ℂ) * w i‖ ≤ 2 * ρ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
        nlinarith [hw' i]
      have hlo : ρ ≤ ‖((ρ : ℂ) • w + z₀) i‖ := by
        rw [hzi]
        have h3 := norm_sub_le ((ρ : ℂ) * w i + z₀ i) ((ρ : ℂ) * w i)
        rw [add_sub_cancel_left] at h3
        linarith
      have hhi : ‖((ρ : ℂ) • w + z₀) i‖ ≤ 2 := by
        rw [hzi]
        have := norm_add_le ((ρ : ℂ) * w i) (z₀ i)
        linarith
      set t := ‖((ρ : ℂ) • w + z₀) i‖ with ht
      have ht0 : 0 < t := lt_of_lt_of_le hρ hlo
      have ht2 : 0 < t ^ 2 := by positivity
      have hA : 0 ≤ Real.log (4 / t ^ 2) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ ht2]; nlinarith
      have hB : Real.log (4 / t ^ 2) ≤ K := by
        apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_left (by norm_num) hρ2
        nlinarith
      rw [if_neg h0, sub_zero, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hB hm0
  have hdiff : rLoc S m ((ρ : ℂ) • w + z₀) - rLoc (S.filter (fun i => z₀ i = 0)) m w =
      ∑ i ∈ S, ((m i : ℝ) * Real.log (4 / ‖((ρ : ℂ) • w + z₀) i‖ ^ 2) -
        (if z₀ i = 0 then (m i : ℝ) * Real.log (4 / ‖w i‖ ^ 2) else 0)) := by
    unfold rLoc
    rw [Finset.sum_filter, add_sub_add_left_eq_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)

theorem fderiv_rescale_norm_le {e : ℕ} (f : (Fin e → ℂ) → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (z₀ w : Fin e → ℂ) :
    ‖fderiv ℝ (fun w => f ((ρ : ℂ) • w + z₀)) w‖ ≤ ‖fderiv ℝ f ((ρ : ℂ) • w + z₀)‖ := by
  have hne : ρ ≠ 0 := hρ.ne'
  let I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ) := ContinuousLinearEquiv.equivOfInverse
    (ρ • ContinuousLinearMap.id ℝ (Fin e → ℂ)) (ρ⁻¹ • ContinuousLinearMap.id ℝ (Fin e → ℂ))
    (fun x => by simp [smul_smul, hne]) (fun x => by simp [smul_smul, hne])
  have hI : ∀ u, I u = (ρ : ℂ) • u := by
    intro u
    ext i
    simp [I]
  have hfun : (fun w => f ((ρ : ℂ) • w + z₀)) = (fun u => f (u + z₀)) ∘ I := by
    funext u
    simp [hI]
  rw [hfun, I.comp_right_fderiv, fderiv_comp_add_right, hI]
  have hIn : ‖((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
    have : ((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ)) u = (ρ : ℂ) • u := hI u
    rw [this, norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg u]
  calc _ ≤ ‖fderiv ℝ f ((ρ : ℂ) • w + z₀)‖ * ‖((I : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)) : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := by nlinarith [norm_nonneg (fderiv ℝ f ((ρ : ℂ) • w + z₀))]

theorem refine_local_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ M : ℝ)
    (hle : ∀ y, logNormSec L s y ≤ 0) (hAB : A.Compatible B)
    (h2 : ∀ j, closedBall (0 : Fin e → ℂ) 2 ⊆ (B.chart j).target)
    (hM : ∀ j, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
      (∀ y ∈ (B.chart j).target, ((B.chart j).symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
      ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, (B.chart j).symm y ∉ bdry s →
        |rW L s ((B.chart j).symm y) - rLoc S m y| ≤ M)
    (hG : IsGradBound B L s ph C₅) (j : Fin B.n) (x : X) (hx : x ∈ (B.chart j).source)
    (hx1 : B.chart j x ∈ ball (0 : Fin e → ℂ) 1) :
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), (IsCompatChart A ψ ∧
      closedBall (0 : Fin e → ℂ) 2 ⊆ ψ.target ∧
      (∃ M' : ℝ, ∃ (S : Finset (Fin e)) (m : Fin e → ℕ), (∀ i ∈ S, 1 ≤ m i) ∧
        (∀ y ∈ ψ.target, (ψ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧
        ∀ y ∈ closedBall (0 : Fin e → ℂ) 2, ψ.symm y ∉ bdry s →
          |rW L s (ψ.symm y) - rLoc S m y| ≤ M') ∧
      (∀ y ∈ ball (0 : Fin e → ℂ) (3 / 2), ψ.symm y ∉ bdry s →
        ‖fderiv ℝ (ph ∘ ψ.symm) y‖ ≤
          |C₅| * rW L s (ψ.symm y) ^ |C₅| * Real.exp (rW L s (ψ.symm y) / 2))) ∧
      x ∈ ψ.source ∧ ψ x ∈ ball (0 : Fin e → ℂ) 1 ∧ ψ.source ⊆ th.U x := by
  classical
  set c := B.chart j with hc
  set z₀ : Fin e → ℂ := c x with hz₀
  have hz₀1 : ‖z₀‖ < 1 := by simpa using hx1
  obtain ⟨S, m, hm, hb, hr⟩ := hM j
  have hOopen : IsOpen (c.target ∩ c.symm ⁻¹' th.U x) :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (th.isOpen_U x)
  have hz₀O : z₀ ∈ c.target ∩ c.symm ⁻¹' th.U x :=
    ⟨c.map_source hx, by
      show c.symm (c x) ∈ th.U x
      rw [c.left_inv hx]; exact th.mem_U x⟩
  obtain ⟨r, hr0, hrO⟩ := Metric.isOpen_iff.1 hOopen z₀ hz₀O
  obtain ⟨ρ, hρ0, hρ8, hρr, hfar⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 8 ∧ 3 * ρ ≤ r ∧
      ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖ := by
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ i, z₀ i ≠ 0 → 3 * ρ < ‖z₀ i‖ := by
      refine Filter.eventually_all.2 fun i => ?_
      by_cases h : z₀ i = 0
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · have hp : 0 < ‖z₀ i‖ / 3 := by
          have := norm_pos_iff.2 h
          positivity
        filter_upwards [Ioo_mem_nhdsGT hp] with ρ hρ _
        have := hρ.2
        linarith
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Set.Ioo (0 : ℝ) (min (1 / 8) (r / 3)) :=
      Ioo_mem_nhdsGT (lt_min (by norm_num) (by positivity))
    obtain ⟨ρ, hρ, hev'⟩ := (h1.and hev).exists
    have ha := lt_of_lt_of_le hρ.2 (min_le_left _ _)
    have hb' := lt_of_lt_of_le hρ.2 (min_le_right _ _)
    exact ⟨ρ, hρ.1, ha.le, by linarith, hev'⟩
  have hs : IsOpen (c.source ∩ c ⁻¹' ball z₀ (3 * ρ)) :=
    c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have ha : ((ρ : ℂ))⁻¹ ≠ 0 := inv_ne_zero hρC
  set ψ : OpenPartialHomeomorph X (Fin e → ℂ) :=
    (c.restrOpen _ hs).transHomeomorph (pa_aff ((ρ : ℂ))⁻¹ ha z₀) with hψ
  have hinv : ∀ w, (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w = (ρ : ℂ) • w + z₀ := by
    intro w
    show (((ρ : ℂ))⁻¹)⁻¹ • w + z₀ = _
    rw [inv_inv]
  have hsymm : ∀ w, ψ.symm w = c.symm ((ρ : ℂ) • w + z₀) := by
    intro w
    show c.symm ((pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w) = _
    rw [hinv]
  have hnorm : ∀ w : Fin e → ℂ, ‖(ρ : ℂ) • w‖ = ρ * ‖w‖ := by
    intro w
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
  have hdist : ∀ w : Fin e → ℂ, ‖(ρ : ℂ) • w + z₀ - z₀‖ = ρ * ‖w‖ := by
    intro w
    rw [add_sub_cancel_right, hnorm]

  have htar1 : ∀ w : Fin e → ℂ, ‖w‖ < 3 → w ∈ ψ.target := by
    intro w hw
    have hzb : (ρ : ℂ) • w + z₀ ∈ ball z₀ (3 * ρ) := by
      rw [Metric.mem_ball, dist_eq_norm, hdist]
      nlinarith
    have hzT : (ρ : ℂ) • w + z₀ ∈ c.target := (hrO (ball_subset_ball hρr hzb)).1
    have hmem : (ρ : ℂ) • w + z₀ ∈ (c.restrOpen _ hs).target :=
      ⟨hzT, c.map_target hzT, by
        show c (c.symm ((ρ : ℂ) • w + z₀)) ∈ ball z₀ (3 * ρ)
        rw [c.right_inv hzT]
        exact hzb⟩
    show (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w ∈ (c.restrOpen _ hs).target
    rw [hinv]
    exact hmem
  have htar2 : ∀ w ∈ ψ.target, (ρ : ℂ) • w + z₀ ∈ c.target ∧
      (ρ : ℂ) • w + z₀ ∈ ball z₀ (3 * ρ) := by
    intro w hw
    have hw' : (pa_aff ((ρ : ℂ))⁻¹ ha z₀).symm w ∈ (c.restrOpen _ hs).target := hw
    rw [hinv] at hw'
    obtain ⟨h1, -, h3⟩ := hw'
    refine ⟨h1, ?_⟩
    have h3' : c (c.symm ((ρ : ℂ) • w + z₀)) ∈ ball z₀ (3 * ρ) := h3
    rwa [c.right_inv h1] at h3'
  have hcl : closedBall (0 : Fin e → ℂ) 2 ⊆ ψ.target := fun w hw =>
    htar1 w (by
      have : ‖w‖ ≤ 2 := by simpa using hw
      linarith)

  have hbd : ∀ y ∈ ψ.target, (ψ.symm y ∈ bdry s ↔
      ∃ i ∈ S.filter (fun i => z₀ i = 0), y i = 0) := by
    intro w hw
    obtain ⟨hzT, hzb⟩ := htar2 w hw
    rw [hsymm, hb _ hzT]
    constructor
    · rintro ⟨i, hi, hzi⟩
      have hzi' : (ρ : ℂ) * w i + z₀ i = 0 := by simpa using hzi
      have h0 : z₀ i = 0 := by
        by_contra h0
        have h1 := hfar i h0
        have h2' : ‖z₀ i‖ ≤ ρ * ‖w‖ := by
          have h3 : z₀ i = -((ρ : ℂ) * w i) := eq_neg_of_add_eq_zero_right hzi'
          rw [h3, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm w i) hρ0.le
        have h4 : ρ * ‖w‖ < 3 * ρ := by
          have := hzb
          rwa [Metric.mem_ball, dist_eq_norm, hdist] at this
        linarith
      refine ⟨i, Finset.mem_filter.2 ⟨hi, h0⟩, ?_⟩
      rw [h0, add_zero] at hzi'
      exact (mul_eq_zero.1 hzi').resolve_left hρC
    · rintro ⟨i, hi, hwi⟩
      obtain ⟨hiS, h0⟩ := Finset.mem_filter.1 hi
      exact ⟨i, hiS, by simp [hwi, h0]⟩
  obtain ⟨cc, hcc⟩ := rLoc_rescale_bound S m z₀ ρ hρ0 hρ8 hz₀1 hfar
  have hsmall : ∀ w : Fin e → ℂ, ‖w‖ ≤ 2 → ‖(ρ : ℂ) • w + z₀‖ < 3 / 2 := by
    intro w hw
    have h1 := norm_add_le ((ρ : ℂ) • w) z₀
    rw [hnorm] at h1
    nlinarith [norm_nonneg w]
  refine ⟨ψ, ⟨pa_compat_aff A _ (pa_compat_restr A _ (fun k => ⟨hAB.1 k j, hAB.2 j k⟩) _ hs) _ ha _,
    hcl, ⟨M + cc, S.filter (fun i => z₀ i = 0), m,
      fun i hi => hm i (Finset.mem_filter.1 hi).1, hbd, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw hnb
    have hw2 : ‖w‖ ≤ 2 := by simpa using hw
    have hz2 : (ρ : ℂ) • w + z₀ ∈ closedBall (0 : Fin e → ℂ) 2 := by
      have := hsmall w hw2
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have hne : ∀ i ∈ S, z₀ i = 0 → w i ≠ 0 := fun i hi h0 hwi =>
      hnb ((hbd w (hcl hw)).2 ⟨i, Finset.mem_filter.2 ⟨hi, h0⟩, hwi⟩)
    rw [hsymm] at hnb ⊢
    have h1 := hr _ hz2 hnb
    have h3 := hcc w hw hne
    rw [abs_le] at h1 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
  · intro w hw hnb
    have hw32 : ‖w‖ < 3 / 2 := by simpa using hw
    have hz : (ρ : ℂ) • w + z₀ ∈ ball (0 : Fin e → ℂ) (3 / 2) := by
      simpa using hsmall w (by linarith)
    have hfun : ph ∘ ψ.symm = fun w => (ph ∘ c.symm) ((ρ : ℂ) • w + z₀) := by
      funext u
      simp [hsymm]
    rw [hfun]
    rw [hsymm] at hnb ⊢
    have h1 := fderiv_rescale_norm_le (ph ∘ c.symm) ρ hρ0 (by linarith) z₀ w
    have h3 : ‖fderiv ℝ (ph ∘ c.symm) ((ρ : ℂ) • w + z₀)‖ ≤ _ := hG j _ hz hnb
    refine (h1.trans h3).trans ?_
    set R := rW L s (c.symm ((ρ : ℂ) • w + z₀)) with hR
    have hR1 : 1 ≤ R := by
      have h4 : Real.exp 1 ≤ R := rW_ge L s hle _
      have h5 : (1 : ℝ) ≤ Real.exp 1 := by
        simpa using Real.add_one_le_exp (0 : ℝ) |>.trans (Real.exp_le_exp.2 zero_le_one)
      linarith
    have hR0 : 0 ≤ R := by linarith
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hR1 (le_abs_self _))
      (Real.rpow_nonneg hR0 _) (abs_nonneg _)
  · exact ⟨hx, hx, mem_ball_self (by positivity)⟩
  · have : ψ x = 0 := by
      show ((ρ : ℂ))⁻¹ • (c x - z₀) = 0
      simp [hz₀]
    rw [this]
    exact mem_ball_self one_pos
  · intro y hy
    have hy' : y ∈ (c.restrOpen _ hs).source := hy
    have h1 : y ∈ c.source := hy'.1
    have h3 : c y ∈ ball z₀ (3 * ρ) := hy'.2.2
    have h4 := (hrO (ball_subset_ball hρr h3)).2
    have h5 : c.symm (c y) ∈ th.U x := h4
    rwa [c.left_inv h1] at h5

theorem refine_adapted_atlas : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ : ℝ), (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → IsGradBound B L s ph C₅ → ∃ (B' : FinHolAtlas e X) (x : Fin B'.n → X), IsAdaptedAtlas A B' L s ∧ IsGradBound B' L s ph |C₅| ∧ ∀ j, (B'.chart j).source ⊆ th.U (x j) := by
  intro e X _ _ _ A B L th s ph C₅ hle hAd hG
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd
  have hcov₀ := hcov
  choose jf hj hj1 using hcov₀
  have hgood := fun x : X => refine_local_chart A B L th s ph C₅ M hle hAB h2 hM hG (jf x) x (hj x) (hj1 x)
  choose φ hφg hφx hφ1 hφU using hgood
  have hU : ∀ x, φ x ⁻¹' ball 0 1 ∩ (φ x).source ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ⟨hφ1 x, hφx x⟩
    rw [Set.inter_comm]
    exact (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover _ hU
  have hcov' : ∀ x, ∃ y ∈ t, x ∈ φ y ⁻¹' ball 0 1 ∩ (φ y).source := by
    intro x
    have : x ∈ (⊤ : Set X) := trivial
    rw [← ht] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hx⟩ := this
    exact ⟨y, hy, hx⟩
  obtain ⟨B', hAB', h1, h3⟩ := atlasOfCompat A (fun i => φ (t.equivFin.symm i))
    (fun i => (hφg _).1) (fun x => by
      obtain ⟨y, hy, hx⟩ := hcov' x
      exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hx.2⟩)
  choose idx hidx using h3
  have hMx := fun x => (hφg x).2.2.1
  choose Mf hMf using hMx
  refine ⟨B', fun j => (t.equivFin.symm (idx j) : X), ⟨hAB', fun j => ?_, fun x => ?_,
    ∑ i, |Mf (t.equivFin.symm i : X)|, fun j => ?_⟩, fun j => ?_, fun j => ?_⟩
  · rw [hidx j]
    exact (hφg _).2.1
  · obtain ⟨y, hy, hx⟩ := hcov' x
    obtain ⟨j, hj⟩ := h1 (t.equivFin ⟨y, hy⟩)
    refine ⟨j, ?_, ?_⟩
    · rw [hj]
      simpa using hx.2
    · rw [hj]
      simpa using hx.1
  · obtain ⟨S, m, hm, hb, hr⟩ := hMf (t.equivFin.symm (idx j) : X)
    refine ⟨S, m, hm, ?_, ?_⟩
    · rw [hidx j]
      exact hb
    · rw [hidx j]
      intro y hy hnb
      refine (hr y hy hnb).trans ((le_abs_self _).trans ?_)
      exact Finset.single_le_sum (f := fun i => |Mf (t.equivFin.symm i : X)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ (idx j))
  · rw [hidx j]
    exact (hφg _).2.2.2
  · rw [hidx j]
    exact hφU _

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviNonnegInChartOfPsh
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_nonneg_of_compat_fixedBase : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B →
    IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) →
    (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    ∀ w : Fin e → ℂ,
    0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  intro e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w
  have hp : (B.chart j).symm y ∈ (B.chart j).source := (B.chart j).map_target hy.1
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y := hAB.2 j k y ⟨hy.1, hk⟩
  have hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y :=
    (A.chart k).left_inv hk
  have htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target := (A.chart k).map_source hk
  have hthU : (B.chart j).symm y ∈ th.U x₀ := hsrc hp
  have hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀) :=
    (A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)
  have hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀ :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩
  have hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2
  have hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2
  have hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z))
      ((A.chart k ∘ (B.chart j).symm) y) := hC1.add hC2
  have hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y]
      ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘
        (A.chart k ∘ (B.chart j).symm)) := by
    have h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source :=
      ((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  rw [levi_congr hev w, levi_comp w hτ hC]
  exact hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _

end GlobalTheory.CompanionTheory.LeviChart
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartLeviNonneg
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.PshBack

theorem smoothOn_isPshOn_chartBack : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (x₀ : X) (j : Fin B.n) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → ℝ),
    A.Compatible B → IsPotential A th → (B.chart j).source ⊆ th.U x₀ → IsOpen V →
    V ⊆ (B.chart j).target → ContDiffOn ℝ ∞ g V →
    (∀ z ∈ V, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z' => th.φ x₀ ((B.chart j).symm z') + g z') z w) →
    A.SmoothOn ((B.chart j).source ∩ B.chart j ⁻¹' V) (g ∘ B.chart j) ∧
      IsPshOn A ((B.chart j).source ∩ B.chart j ⁻¹' V) (th + LocPot.ofFun (g ∘ B.chart j)) := by
  intro e X _ A B th x₀ j V g hAB hth hsrc hV hVt hg hlevi
  have hτ : ∀ (k : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart k).target →
      (A.chart k).symm y ∈ (B.chart j).source →
      AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := fun k y hy hp => hAB.1 k j y ⟨hy, hp⟩
  refine ⟨fun k y hy => ?_, fun x k y hy w => ?_⟩
  · obtain ⟨hyt, hp, hpV⟩ := hy
    have h1 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hpV)
    have h2 : ContDiffAt ℝ ∞ (B.chart j ∘ (A.chart k).symm) y :=
      ((hτ k y hyt hp).contDiffAt (n := ∞)).restrict_scalars ℝ
    exact (h1.comp y h2).contDiffWithinAt
  · obtain ⟨hyt, ⟨hpx, -⟩, hp, hpV⟩ := hy
    have hτy : AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := hτ k y hyt hp
    obtain ⟨W, hW, hpW, G, hG, hGe⟩ := hth.2 x x₀ ((A.chart k).symm y) ⟨hpx, hsrc hp⟩
    have hGa : AnalyticAt ℂ (G ∘ (A.chart k).symm) y := hG k y ⟨hyt, hpW⟩
    let h : (Fin e → ℂ) → ℝ := fun z' => th.φ x₀ ((B.chart j).symm z') + g z'
    have hB : B.SmoothOn (th.U x₀) (th.φ x₀) :=
      smoothOn_of_compatible hAB (th.isOpen_U x₀) (hth.1 x₀)
    have hτyV : (B.chart j ∘ (A.chart k).symm) y ∈ V := hpV
    have hh : ContDiffAt ℝ 2 h ((B.chart j ∘ (A.chart k).symm) y) := by
      have hmem : (B.chart j ∘ (A.chart k).symm) y ∈
          (B.chart j).target ∩ (B.chart j).symm ⁻¹' th.U x₀ := by
        refine ⟨hVt hτyV, ?_⟩
        show (B.chart j).symm (B.chart j ((A.chart k).symm y)) ∈ th.U x₀
        rw [(B.chart j).left_inv hp]
        exact hsrc hp
      have h1 : ContDiffAt ℝ ∞ (th.φ x₀ ∘ (B.chart j).symm) ((B.chart j ∘ (A.chart k).symm) y) :=
        (hB j).contDiffAt
          (((B.chart j).isOpen_inter_preimage_symm (th.isOpen_U x₀)).mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hτyV)
      exact (h1.add h2).of_le (by norm_cast)
    have hhτ : ContDiffAt ℝ 2 (h ∘ (B.chart j ∘ (A.chart k).symm)) y :=
      hh.comp y ((hτy.contDiffAt).restrict_scalars ℝ)
    have hGre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart k).symm) y').re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y ((hGa.contDiffAt).restrict_scalars ℝ)
    have hopen : IsOpen ((A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source)) :=
      (A.chart k).isOpen_inter_preimage_symm
        (((hW.inter (th.isOpen_U x)).inter (th.isOpen_U x₀)).inter (B.chart j).open_source)
    have hymem : y ∈ (A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source) :=
      ⟨hyt, ⟨⟨hpW, hpx⟩, hsrc hp⟩, hp⟩
    have hev : ((th + LocPot.ofFun (g ∘ B.chart j)).φ x ∘ (A.chart k).symm) =ᶠ[𝓝 y]
        (fun y' => (h ∘ (B.chart j ∘ (A.chart k).symm)) y' +
          1 * ((G ∘ (A.chart k).symm) y').re) := by
      filter_upwards [hopen.mem_nhds hymem] with y' hy'
      obtain ⟨-, ⟨⟨hW', hx'⟩, hx0'⟩, hs'⟩ := hy'
      have hd := hGe _ ⟨⟨hW', hx'⟩, hx0'⟩
      change th.φ x ((A.chart k).symm y') + g (B.chart j ((A.chart k).symm y')) =
        th.φ x₀ ((B.chart j).symm (B.chart j ((A.chart k).symm y'))) +
          g (B.chart j ((A.chart k).symm y')) + 1 * (G ((A.chart k).symm y')).re
      rw [(B.chart j).left_inv hs']
      linarith
    have e1 := levi_add_smul (f := h ∘ (B.chart j ∘ (A.chart k).symm))
      (g := fun y' => ((G ∘ (A.chart k).symm) y').re) (z := y) 1 hhτ hGre w
    rw [levi_congr hev w, e1, levi_re_analytic hGa w, levi_comp w hτy hh]
    have := hlevi _ hτyV (fderiv ℂ (B.chart j ∘ (A.chart k).symm) y w)
    simp only [mul_zero, add_zero]
    exact this

end GlobalTheory.CompanionTheory.Metric.PshBack
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBoundTransferBetweenRadii
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.BoundConv

theorem bound_conv_local (C₅ M : ℝ) : ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) := by
  set A := |C₅| with hA
  set M' := |M| with hM'
  have hA0 : 0 ≤ A := abs_nonneg _
  have hM0 : 0 ≤ M' := abs_nonneg _
  have hB1 : 1 ≤ (1 + M') ^ A := Real.one_le_rpow (by linarith) hA0
  have hE1 : 1 + M' ≤ Real.exp M' := by linarith [Real.add_one_le_exp M']
  have hE1' : 1 ≤ Real.exp M' := Real.one_le_exp hM0
  set K := A * (1 + M') ^ A * Real.exp M' with hK
  have hK0 : 0 ≤ K := by positivity
  have hKA : A ≤ K := by
    have : A * 1 * 1 ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1' (by norm_num) (by positivity)
    simpa using this
  have hKA' : A * (1 + M') ≤ K := by
    have : A * 1 * (1 + M') ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1 (by linarith) (by positivity)
    simpa using this
  refine ⟨K, hK0, ?_⟩
  intro x y p d hx hy hxy
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hy1 : 1 ≤ y := le_trans he1 hy
  have hx1 : 1 ≤ x := le_trans he1 hx
  have hlogy : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hy
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  have hxle : x ≤ y + M' := by
    have := (abs_le.mp (le_trans hxy (le_abs_self M))).2
    linarith
  have hxle2 : x ≤ y * (1 + M') := by nlinarith
  constructor
  · intro hp1 hp2
    refine ⟨?_, le_trans hp2 (le_trans (le_abs_self C₅) hKA)⟩
    rcases le_or_gt C₅ 0 with hC | hC
    · have h1 : 0 ≤ -C₅ * Real.log x := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ K * Real.log y := mul_nonneg hK0 (by linarith)
      linarith
    · have hAC : A = C₅ := abs_of_pos hC
      have hl1 : Real.log x ≤ Real.log (y * (1 + M')) := Real.log_le_log (by linarith) hxle2
      rw [Real.log_mul (by linarith) (by linarith)] at hl1
      have hl2 : Real.log (1 + M') ≤ M' := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + M' by linarith); linarith
      have hl3 : Real.log x ≤ Real.log y * (1 + M') := by nlinarith
      have hl4 : C₅ * Real.log x ≤ C₅ * (1 + M') * Real.log y := by
        have := mul_le_mul_of_nonneg_left hl3 hC.le; linarith
      have hl5 : C₅ * (1 + M') * Real.log y ≤ K * Real.log y :=
        mul_le_mul_of_nonneg_right (by rw [← hAC]; exact hKA') (by linarith)
      linarith
  · intro hd
    have h1 : x ^ A ≤ (y * (1 + M')) ^ A := Real.rpow_le_rpow (by linarith) hxle2 hA0
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : Real.exp (x / 2) ≤ Real.exp (y / 2) * Real.exp M' := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h3 : y ^ A ≤ y ^ K := Real.rpow_le_rpow_of_exponent_le hy1 hKA
    have hxA : 0 ≤ x ^ A := Real.rpow_nonneg (by linarith) _
    have hyK : 0 ≤ y ^ K := Real.rpow_nonneg (by linarith) _
    have hB0 : 0 ≤ (1 + M') ^ A := by linarith
    calc d ≤ A * x ^ A * Real.exp (x / 2) := hd
      _ ≤ A * (y ^ A * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hA0) h2 (Real.exp_pos _).le
          positivity
      _ ≤ A * (y ^ K * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hB0) hA0
      _ = K * y ^ K * Real.exp (y / 2) := by rw [hK]; ring

theorem bound_conv : ∀ (C₅ M : ℝ), ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) :=
  bound_conv_local

end GlobalTheory.CompanionTheory.Metric.BoundConv
end

section -- restored verbatim from Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem regGlobalStatement_holds : RegGlobalStatement := by
  intro e X _ _ _ A B Θ L s n m W hΘ hΘpos hL hS hSNC hs hAd th ph C₅ hSW hGB
  obtain ⟨B', x, hAd', hGB', hsrc⟩ := GlobalTheory.CompanionTheory.Ar.Giv.refine_adapted_atlas A B L th s ph C₅ hs hAd hGB
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd'
  choose S mm hm1 hbd hrl using hM
  have hcl : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨hth, hphs, hpsh, hb⟩ := hSW
  obtain ⟨C₅', hC₅'0, hconv⟩ := GlobalTheory.CompanionTheory.Metric.BoundConv.bound_conv C₅ M
  obtain ⟨hlogd, hmono, hle, htend, hsmall, hmin⟩ := GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics
  have hrWge : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hball : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      z ∈ (B'.chart j).target ∧ (B'.chart j).symm z ∉ bdry s := by
    intro j z hz
    have hzt : z ∈ (B'.chart j).target := h2 j (ball_subset_closedBall hz.1)
    exact ⟨hzt, fun hzb => hz.2 ((hbd j z hzt).1 hzb)⟩
  have hq : ∀ j, ContDiffOn ℝ ∞ (fun z => th.φ (x j) ((B'.chart j).symm z)) (ball (0 : Fin e → ℂ) 2) :=
    fun j => (smoothOn_of_compatible hAB (th.isOpen_U (x j)) (hth.1 (x j)) j).mono fun z hz =>
      ⟨h2 j (ball_subset_closedBall hz),
        hsrc j ((B'.chart j).map_target (h2 j (ball_subset_closedBall hz)))⟩
  have hphj : ∀ j, ContDiffOn ℝ ∞ (ph ∘ (B'.chart j).symm)
      (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j)) :=
    fun j => (smoothOn_of_compatible hAB hcl.isOpen_compl hphs j).mono fun z hz => hball j z hz
  have hlevi : ∀ j, ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j))
      (fun z => (fun z => th.φ (x j) ((B'.chart j).symm z)) z + (ph ∘ (B'.chart j).symm) z) := by
    intro j
    refine ⟨(((hq j).mono Set.diff_subset).add (hphj j)).of_le h2le, fun z hz w => ?_⟩
    exact GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase A B' th ph (bdry s)ᶜ (x j) j hAB hth hcl.isOpen_compl hphs hpsh (hsrc j) z (hball j z hz) w
  have hbnd : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      -C₅' * Real.log (rLoc (S j) (mm j) z) ≤ (ph ∘ (B'.chart j).symm) z ∧
        (ph ∘ (B'.chart j).symm) z ≤ C₅' := by
    intro j z hz
    obtain ⟨-, hzb⟩ := hball j z hz
    have hr := hrl j z (ball_subset_closedBall hz.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz.1)
    exact (hconv _ _ (ph ((B'.chart j).symm z)) 0 (hrWge _) hrl' hr).1 (hb _ hzb).1 (hb _ hzb).2
  have hgrad : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      ‖fderiv ℝ (ph ∘ (B'.chart j).symm) z‖ ≤
        C₅' * rLoc (S j) (mm j) z ^ C₅' * Real.exp (rLoc (S j) (mm j) z / 2) := by
    intro j z hz
    have hz2 : z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j) :=
      ⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩
    obtain ⟨-, hzb⟩ := hball j z hz2
    have hr := hrl j z (ball_subset_closedBall hz2.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz2.1)
    exact (hconv _ _ 0 _ (hrWge _) hrl' hr).2 (hGB' j z hz.1 hzb)
  have hch := fun j => GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart e (S j) (mm j) (fun z => th.φ (x j) ((B'.chart j).symm z))
    (ph ∘ (B'.chart j).symm) C₅' M (hm1 j) (hq j) (hphj j) (hlevi j) (hbnd j) (hgrad j)
  choose Cj tj g hCj1 htj0 htje hgt hgC2 using hch

  obtain ⟨C', t', ht'0, hcmp⟩ := GlobalTheory.CompanionTheory.Ar.Giv.polyMaxOff_charts_compare A B' L th s ph C₅ M x S mm hAB h2 hsrc hs hcl hbd hrl
    ⟨hth, hphs, hpsh, hb⟩
  set Cm : ℝ := 1 + ∑ j, |Cj j| with hCmdef
  have hCm : ∀ j, Cj j ≤ Cm := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2' := le_abs_self (Cj j)
    linarith
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ ∑ j, |Cj j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Cl : ℝ := |C'| + Cm with hCldef
  have hCl1 : 1 ≤ Cl := by have := abs_nonneg C'; linarith
  have hClj : ∀ j, Cj j ≤ Cl := fun j => by have := abs_nonneg C'; linarith [hCm j]
  obtain ⟨a, ha0, ha⟩ := hsmall Cl
  obtain ⟨tm, htm0, htm⟩ := hmin B'.n tj htj0
  set t₀ : ℝ := min (min tm t') (min a (Real.exp (-Real.exp 1))) with ht₀def
  have ht₀0 : 0 < t₀ := lt_min (lt_min htm0 ht'0) (lt_min ha0 (Real.exp_pos _))
  have ht₀j : ∀ j, t₀ ≤ tj j := fun j => ((min_le_left _ _).trans (min_le_left _ _)).trans (htm j)
  have ht₀' : t₀ ≤ t' := (min_le_left _ _).trans (min_le_right _ _)
  have ht₀a : t₀ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have ht₀e : t₀ ≤ Real.exp (-Real.exp 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hLL : ∀ t, 0 < t → t ≤ t₀ → 0 ≤ Real.log (Real.log (1 / t)) := fun t ht htt => by
    have := (log_inv_bounds ht (htt.trans ht₀e)).2; linarith

  have hy54 : ∀ j, ∀ y ∈ chartBall B' j (5 / 4), B'.chart j y ∈ ball (0 : Fin e → ℂ) (5 / 4) ∧
      B'.chart j y ∈ closedBall (0 : Fin e → ℂ) 2 ∧ (B'.chart j).symm (B'.chart j y) = y := by
    intro j y hy
    exact ⟨hy.2, ball_subset_closedBall (ball_subset_ball (by norm_num) hy.2), (B'.chart j).left_inv hy.1⟩
  have hsand : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) y + g j t (B'.chart j y) ∧
        th.φ (x j) y + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := by
    intro t ht htt j y hy
    obtain ⟨hz, -, hsy⟩ := hy54 j y hy
    have h := ((hgt j t ht (htt.trans (ht₀j j))).2.2.2.2.1 (B'.chart j y) hz)
    have h' : polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ∧
        th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := h
    rw [hsy] at h'
    exact h'
  have hloc : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ (g j t ∘ B'.chart j) y ∧
        (y ∉ bdry s → ph y ≤ (g j t ∘ B'.chart j) y ∧
          (rW L s y ≤ Real.log (1 / t) → (g j t ∘ B'.chart j) y ≤ ph y + t ^ ((1 : ℝ) / 3))) := by
    intro t ht htt j y hy
    obtain ⟨hz, hz2, hsy⟩ := hy54 j y hy
    obtain ⟨-, -, hgb, hgn, -, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    obtain ⟨hb1, hb2⟩ := hgb _ hz
    have hll := hLL t ht htt
    refine ⟨hb1.trans (hClj j), le_trans ?_ hb2, fun hyb => ?_⟩
    · have := mul_le_mul_of_nonneg_right (hClj j) hll
      show -Cl * _ ≤ -Cj j * _
      linarith
    · have hzt : B'.chart j y ∈ (B'.chart j).target := h2 j hz2
      have hzc : B'.chart j y ∉ ReciprocityTheory.AnForm.A.coordDiv (S j) := fun hc =>
        hyb (hsy ▸ (hbd j _ hzt).2 hc)
      obtain ⟨hn1, hn2⟩ := hgn _ ⟨hz, hzc⟩
      have hr := hrl j _ hz2 (by rw [hsy]; exact hyb)
      rw [hsy] at hr
      simp only [Function.comp_apply, hsy] at hn1 hn2 ⊢
      refine ⟨hn1, fun hrw => hn2 ?_⟩
      have := (abs_le.1 hr).1
      linarith
  have hmono' : ∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ (g j t' ∘ B'.chart j) y + epsT Cl t' := by
    intro t t'' ht htt' ht'' j y hy
    obtain ⟨hz, -, -⟩ := hy54 j y hy
    have h := (hgt j t ht ((htt'.trans ht'').trans (ht₀j j))).2.2.2.2.2 t'' htt' (ht''.trans (ht₀j j)) _ hz
    have := epsT_le_epsT (hClj j) (ht.trans_le htt') (ht''.trans ht₀e)
    simp only [Function.comp_apply]
    linarith

  obtain ⟨K, hK0, hgl⟩ := GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 A B' Θ th s ph hAB hcov h2 hΘ hΘpos hth hcl hphs
  have hback : ∀ t, 0 < t → t ≤ t₀ → ∀ j, A.SmoothOn (chartBall B' j (5 / 4)) (g j t ∘ B'.chart j) ∧
      IsPshOn A (chartBall B' j (5 / 4)) (th + LocPot.ofFun (g j t ∘ B'.chart j)) := by
    intro t ht htt j
    obtain ⟨hgs, hglevi, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    exact GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack A B' th (x j) j (ball (0 : Fin e → ℂ) (5 / 4)) (g j t) hAB hth (hsrc j) isOpen_ball
      (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))) hgs hglevi.2
  have hov : ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B' j (5 / 4) ∩ chartBall B' k (5 / 4),
      |(g j t ∘ B'.chart j) y - (g k t ∘ B'.chart k) y| ≤ epsT Cl t := by
    intro t ht htt j k y hy
    obtain ⟨sj1, sj2⟩ := hsand t ht htt j y hy.1
    obtain ⟨sk1, sk2⟩ := hsand t ht htt k y hy.2
    have hc := abs_le.1 (hcmp t ht (htt.trans ht₀') j k y hy)
    have hte := htt.trans ht₀e
    have e1 := epsT_le_epsT (hCm j) ht hte
    have e2 := epsT_le_epsT (hCm k) ht hte
    have e3 := epsT_le_epsT (le_abs_self C') ht hte
    have e4 : epsT Cl t = epsT |C'| t + epsT Cm t := by
      simp only [hCldef, epsT]; ring
    simp only [Function.comp_apply]
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨F, hF, hFC2⟩ := hgl t₀ (epsT Cl) (fun t j => g j t ∘ B'.chart j) ht₀0 (htend Cl)
    (fun t ht htt => ⟨hle Cl t hCl1 ht (htt.trans ht₀e), ha t ht (htt.trans ht₀a),
      fun j => (hback t ht htt j).1,
      ⟨Cl + Cl * Real.log (Real.log (1 / t)), fun j y hy => by
        obtain ⟨h1, h2', -⟩ := hloc t ht htt j y hy
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ Cl) (hLL t ht htt)
        rw [abs_le]; constructor <;> linarith⟩,
      fun j => (hback t ht htt j).2, hov t ht htt⟩)
    (fun j K' hK' hK'c => by
      have hsub : K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
        intro z hz
        have hzt : z ∈ (B'.chart j).target :=
          h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1))
        exact ⟨(hK' hz).1, fun hc => (hK' hz).2 ((hbd j z hzt).2 hc)⟩
      exact GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback (B'.chart j) (g j) (ph ∘ (B'.chart j).symm) K'
        (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1)))
        (hgC2 j K' hsub hK'c))
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Ar.RegFin.isRegFamily_of_glue A B' Θ L th s ph C₅ K Cl t₀ (fun t j => g j t ∘ B'.chart j) F hΘ hΘpos hth hs hcov
    (fun y hy => (hb y hy).1) hK0 hCl1 ht₀0 ht₀e hF hloc hmono'
  exact ⟨C, t₀, F, hC, hFC2⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem prov_an : Prov.An :=
  ⟨GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds, GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds,
    GlobalTheory.T.pullback_statement_holds, GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
namespace PositivityTheory.MbHsUse

open GroundTheory.Heights₂.Heights.HilbertSamuel

def HSUse : Prop :=
  ArithKleiman.Statement ∧ G7.Statement ∧ ArithmeticVolumeNef.Statement

theorem HSUse.g7 (h : HSUse) : G7.Statement := h.2.1

theorem HSUse.g7p (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticHilbertSamuelUpperBound := h.2.2

theorem HSUse.z1 (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.SuccessiveMinimaLowerBound :=
  G5.proof' h.1 CurvePointsFinite.proof

end PositivityTheory.MbHsUse

namespace GlobalTheory.CompanionTheory.Ar.Giv

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Small

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.Geo

theorem hsLinks_of_use :
    PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement →
      ArithmeticIntersectionNonneg ∧ SuccessiveMinimaLowerBound ∧ SuccessiveMinimaUpperBound ∧ ArithmeticVolumeLowerBound ∧
        GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement ∧ GroundTheory.Heights₂.Heights.DimX.Statement := by
  intro hU hBig
  have a0 : SuccessiveMinimaLowerBound := hU.z1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.G1.full, a0,
    GroundTheory.Heights₂.Heights.ForSecondHalf.Z2.proof hBig,
    GroundTheory.Heights₂.Heights.ForSecondHalf.BigLineBundleMoriwaki.of_moriwakiBig hBig,
    GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.proof a0,
    GroundTheory.Heights₂.Heights.DimX.proof⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GivenOfUse
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.InputsOfUse
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem inputs_of_use :
    ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  intro hII hU hBig hRes
  exact ⟨⟨GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds, GlobalTheory.T.pullback_statement_holds, GlobalTheory.CompanionTheory.Ar.Giv.regGlobalStatement_holds⟩,
    ⟨GlobalTheory.T.resolution_exists_of_resolution_statement hRes, degree_of_system hII, (hsLinks_of_use hU hBig).1⟩,
    ⟨GlobalTheory.T.rationality_of_resolution_statement hRes, metricLocal⟩,
    ⟨GlobalTheory.T.projection_formula_of_arith_system hII, lineFibre_holds, fibreDim⟩,
    ⟨GlobalTheory.T.kleiman_nef_criteria_hold.1, GlobalTheory.T.kleiman_nef_criteria_hold.2, GlobalTheory.CompanionTheory.Ar.Giv.siuZ⟩⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SelfIntersectionLeOfBoundedInjectionUse
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem selfIntersection_le_of_boundedInjection_use :
    PositivityTheory.MbHsUse.HSUse → MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement :=
  fun hU hBig =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.G3.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hBig)
      hU.g7 GlobalTheory.T.packing'

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.NineFreeOfUse
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GrassmannianHeightBoundOfSystems
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem grassmannian_height_bound_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement := by
  intro hSys hU hBig hResK
  exact GlobalTheory.T.grassmann_height_Z2_of_inputs_and_Z2 (inputs_of_use hSys hU hBig hResK) hSys
    (hsLinks_of_use hU hBig).2.2.1

end GlobalTheory.CompanionTheory.Ar.Giv
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem nineFree_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.ZhangDimensionPushDownGrassmannianHeightBounds := by
  intro hI hU hBig hRes
  obtain ⟨-, -, -, -, hZ, hD⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_use hU hBig
  exact ⟨hZ, hD, trivial, GlobalTheory.T.push_down_of_arith_intersection_system hI, GlobalTheory.CompanionTheory.Ar.Giv.grassmannian_height_bound_of_systems hI hU hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.ProvHSOfUse
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallSectionsUpperOfUse
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem smallSections_upper_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArithmeticHilbertSamuelUpperBoundNumberField := by
  intro hAIS hU hRes
  have hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement :=
    degreeGeneric_of_degree (degree_of_system hAIS)
  have a0 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionAnyDegree.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hAIS hRes) hDG
  have a1 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistMetric.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof a0
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNefDual.proof hU.g7p GlobalTheory.T.packing'
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.full a1

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.ArithmeticHilbertSamuelOfSystems
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem arithmetic_hilbert_samuel_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.Statement := by
  intro hSys hU hBig hRes
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.proof (selfIntersection_le_of_boundedInjection_use hU hBig)
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionInt.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hSys hRes)
      (degreeGeneric_of_degree (degree_of_system hSys)))
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem provHS_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → Prov.HS := by
  intro hI hU hBig hRes
  obtain ⟨g1, z1, z2, g6p, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Giv.hsLinks_of_use hU hBig
  exact ⟨z1, z2, g1, g6p, GlobalTheory.T.big_line_implies_height_positivity hBig, hU.g7p, GlobalTheory.CompanionTheory.Ar.Giv.smallSections_upper_of_use hI hU hRes,
    GlobalTheory.CompanionTheory.Ar.Giv.selfIntersection_le_of_boundedInjection_use hU hBig,
    GlobalTheory.CompanionTheory.Ar.Giv.arithmetic_hilbert_samuel_of_systems hI hU hBig hRes⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem given_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → Top.Given := by
  intro hAI hU hBig hRes hSA hHT hGaga hLine
  exact GlobalTheory.T.final_theorem_of_inputs_left GlobalTheory.CompanionTheory.Ar.Top.modelClause_holds GlobalTheory.KeyFam.keyFormula_holds hSA
    GlobalTheory.CompanionTheory.Segre.numericalSegre_closed hRes hHT hGaga hLine
    (GlobalTheory.CompanionTheory.Ar.Giv.inputs_of_use hAI hU hBig hRes) (provHS_of_use hAI hU hBig hRes) GlobalTheory.CompanionTheory.Ar.Link.prov_an
    (nineFree_of_use hAI hU hBig hRes)

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.DeepStROfUse
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.GoodTowerVolumeTheoremBis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem good_tower_volume_theorem_bis :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
    GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections →
    GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement →
    Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hAI hU hBig hResK hSA hFHT hGaga hLine hQ hZ
  exact GlobalTheory.T.final_theorem_of_inputs_right
    GlobalTheory.CompanionTheory.Ar.Top.modelClause_holds GlobalTheory.KeyFam.keyFormula_holds hSA
    GlobalTheory.CompanionTheory.Segre.numericalSegre_closed hResK hFHT hGaga hLine
    (GlobalTheory.CompanionTheory.Ar.Giv.inputs_of_use hAI hU hBig hResK)
    (provHS_of_use hAI hU hBig hResK) GlobalTheory.CompanionTheory.Ar.Link.prov_an
    (nineFree_of_use hAI hU hBig hResK)
    (GlobalTheory.T.points_integrable_of_resolution_statement hResK)
    GlobalTheory.CompanionTheory.Ar.Giv.topAvoid hQ hZ GlobalTheory.thetaUnifAV_closed

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.LineOfLargeDegreeOfUse
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights in
theorem lineOfLargeDegree_of_use :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
        GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement := by
  intro hAIS hU hBig hResK
  have hZ2 : SuccessiveMinimaUpperBound := (hsLinks_of_use hU hBig).2.2.1
  have hI : ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement := GlobalTheory.T.intersection_exists_of_arith_system hAIS
  have hGr : GraphStatement := GlobalTheory.T.graph_statement_holds
  have hAI3 : Inter.PushforwardArithIntersection.Statement := GlobalTheory.T.generic_degree_of_arith_system hAIS
  have hPts : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hResK
  have hInd : PtsIndepStatement :=
    ReciprocityTheory.ChartRestriction.G.Geo.ptsIndep_of (GlobalTheory.T.resolution_exists_of_resolution_statement hResK) HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge
  have hSheet : SheetIndepStatement :=
    ReciprocityTheory.ChartRestriction.G.Geo.sheetIndep_of ReciprocityTheory.ChartRestriction.G.Geo.osgood
      HilbertSamuel.Closed.ReciprocityTheory.ChartRestriction.G.Geo.FibreFinite
  have hChange : IntCoordChange.Statement :=
    IntCoordChange.proof Inter.Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique IntCoordGeoNum.proof
      (IntCoordArInt.proof hInd hSheet)
  have hBasis : DualTopBasisChange.Statement := DualTopBasisChange.proof hChange
  have hSDeg : DualStackedDegree.Statement := DualStackedDegree.proof DualLatticeIndex.proof
  have hCC : CurveCharts.Statement :=
    CurveCharts.proof (ClosedPointChart.proof ClosedPointUnitSection.proof)
  have hVPC : VertPointChart.Statement := VertPointChart.proof hCC
  have hVRI : VertRIndex.Statement :=
    VertRIndex.proof LogCardLength.proof SectionQuotFinite.closed
      (VertPointLength.proof hVPC (VertPointInj.proof hVPC)
        (VertPointSurj.proof hCC SectionQuotLocal.proof)
        (VertPointMultChart.proof hVPC (VertPointNagata.proof hVPC)) SectionQuotLocal.proof)
      (VertPointResidue.proof hCC)
  have hSN : SectionIndexNorm.Statement :=
    SectionIndexNorm.proof hCC
      (InvertibleIdealIndex.proof OrderIdealIndexExtension.proof LocallyPrincipalCoprime.proof)
  have hCELI : ChartEnergyLinearInvariant.Statement :=
    ChartEnergyLinearInvariant.proof ChartEnergySwapInvariant.proof
  have hCE : ChartEnergy.Statement :=
    ChartEnergy.proof hCELI
      (ChartEnergyDiagonal.proof hCELI
        (ChartEnergyCocycle.proof
          (ChartEnergySymm.proof
            (ChartIbpSymm.proof
              (ChartIbpCutoff.proof ChartCutoffEnergy.proof
                (ChartDiffEnergy.proof ChartCutoffEnergy.proof))))))
  have hEnergy : DualMetricEnergy.Statement :=
    DualMetricEnergy.proof
      (DualEnergyCharts.proof
        (ChartEnergyIntegrable.proof HermFormCompare.proof
          (ChartHessCompare.proof HermFormCompare.proof)))
      hCE GrassGeomDegChart.proof ChartMassInvariant.proof
  have hStdGenDeg : DualStdGenDeg.Statement :=
    DualStdGenDeg.proof OneBlockPointDeg.proof
      (DualStdFibreRatios.proof GenFibreModelTransport.proof DualStdGraphModel.proof
        DualStdModelRank.proof DualStdModelTransc.proof)
  have hLinear : DualStackedExcLinear.Statement :=
    DualStackedExcLinear.proof (DualStackedExcResidueExists.proof DualLatticeModPrime.proof)
      (DualStackedExcBaseLe.proof GlobalTheory.T.dual_stacked_graph_bihomogeneous GlobalTheory.T.dual_stacked_exceptional_leading_form)
      (DualStackedExcLinPrimeLe.proof DualCotangentKer.proof)
  have hFib : DualStackedGraphFibre.Statement :=
    DualStackedGraphFibre.proof
      (DualStackedExcCycle.proof
        (DualStackedExcReduced.proof GlobalTheory.T.dual_stacked_exceptional_coords GlobalTheory.T.dual_stacked_exceptional_base GlobalTheory.T.dual_stacked_exceptional_chart))
      (DualStackedExcGeoSecond.proof hLinear LinPrimeCut.proof LinPrimeBase.proof)
      DualStackedExcGeoFirst.proof
  have hStep : DualTopSimpleStacked.Statement :=
    DualTopSimpleStacked.proof hAI3 hGr (DualStackedGraphImage.proof hGr GlobalTheory.CompanionTheory.Ar.Giv.fibreDim)
      DualStackedGraphHorizontal.proof hFib GrassFibreDegree.proof
  have hStacked : DualTopStacked.Statement :=
    DualTopStacked.proof (DualTopSimpleSub.proof hBasis hStep hSDeg) hBasis hSDeg
  have hCM : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement :=
    Targets.ChangeOfModel.of_found hAI3 hGr
      (HilbertSamuel.IsomInvariance.proof (Inter.RatR.proof hPts))
      HilbertSamuel.GraphIsometric.proof
  have hBC : DualStdBaseChange.Statement :=
    DualStdBaseChange.proof hCM hGr Targets.genFibreExists
      (fun F _ K _ ι _ => Targets.ExistsUnique.full F ι)
      DualStdBasePtFree.proof DualStdImageBot.proof hStdGenDeg DualStdMetricPull.proof
  exact LineOfLargeDegreeFromZ.ofOpen hVRI hSN hEnergy hBasis hStacked hSDeg hBC
    (GrassLinesProj.proof (GlobalTheory.T.coordinate_projection_of_arith_system hAIS))
    (DualGeomDegCharts.proof ChartDensityIntegrable.proof) GrassGeomDegChart.proof ChartMassInvariant.proof
    (degree_of_system hAIS) hInd hU.z1 hZ2 hI

end GlobalTheory.CompanionTheory.Ar.Giv
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem deepStR_of_use : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → HT.FarguesHodgeTate → Flat.GagaSections → GR.QuotientByFiniteFlatStatement → GR.ZarhinStatement → Pub.NefRR → Plug.DeepStR := by
  intro hAIS hU hMB hResK hSA hFHT hGaga hQ hZ hNef
  have hLLD := GlobalTheory.CompanionTheory.Ar.Giv.lineOfLargeDegree_of_use hAIS hU hMB hResK
  have hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given := GlobalTheory.CompanionTheory.Ar.Link.given_of_use hAIS hU hMB hResK hSA hFHT hGaga hLLD
  have hTC := GlobalTheory.CompanionTheory.Ar.Link.good_tower_volume_theorem_bis hAIS hU hMB hResK hSA hFHT hGaga hLLD hQ hZ
  have hHS : Prov.HS := by
    unfold _root_.GlobalTheory.CompanionTheory.Ar.Top.Given at hG
    exact hG.2.2.2.2.2.2.2.2.2.2.1
  have hG6 : ReciprocityTheory.ChartRestriction.G.Geo.BirationalPullbackPushforwardFormula := by
    unfold Prov.HS at hHS
    exact hHS.2.2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Plug.deepStR_of_volume hNef hG hAIS hG6 hTC.1 hTC.2

end GlobalTheory.CompanionTheory.Ar.Plug
end

namespace PositivityTheory.HtPt.Ah

open GlobalTheory.CompanionTheory.Ar

theorem deep_slim_use (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) (hU : PositivityTheory.MbHsUse.HSUse)
    (hBig : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement) (hF : HT.FarguesExact) (hZ : GR.ZarhinStatement)
    (hN : Pub.NefRR) : Plug.DeepStR :=
  Plug.deepStR_of_use (ais h₁ h₂ hPL) hU hBig (resK h₁ h₂) GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension
    (GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact hF) GlobalTheory.CompanionTheory.Gaga.gagaSections quot hZ hN

end PositivityTheory.HtPt.Ah
