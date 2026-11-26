module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Set ContinuousLinearMap
open scoped ContDiff
open ReciprocityTheory.AnForm.M (FinHolAtlas HoloMap)

noncomputable section

namespace C2ConvergencePullback

theorem tendstoUniformlyOn_bilin {α ι P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (β : P →L[ℝ] Q →L[ℝ] R) {F : ι → α → P} {G : α → P} {p : Filter ι} {S : Set α}
    (h : TendstoUniformlyOn F G p S) (b : α → Q) (M : ℝ) (hb : ∀ y ∈ S, ‖b y‖ ≤ M) :
    TendstoUniformlyOn (fun t y => β (F t y) (b y)) (fun y => β (G y) (b y)) p S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hβ : ‖β‖ + 1 ≠ 0 := by positivity
  have hM : |M| + 1 ≠ 0 := by positivity
  have hC : 0 < (‖β‖ + 1) * (|M| + 1) := by positivity
  filter_upwards [h (ε / ((‖β‖ + 1) * (|M| + 1))) (div_pos hε hC)] with t ht y hy
  have h1 := ht y hy
  rw [dist_eq_norm] at h1
  have hby : ‖b y‖ ≤ |M| + 1 := (hb y hy).trans ((le_abs_self M).trans (by linarith))
  have heq : β (G y) (b y) - β (F t y) (b y) = β (G y - F t y) (b y) := by
    rw [map_sub, sub_apply]
  rw [dist_eq_norm, heq]
  calc ‖β (G y - F t y) (b y)‖ ≤ ‖β‖ * ‖G y - F t y‖ * ‖b y‖ := β.le_opNorm₂ _ _
    _ ≤ (‖β‖ + 1) * ‖G y - F t y‖ * (|M| + 1) := by gcongr; linarith
    _ < (‖β‖ + 1) * (ε / ((‖β‖ + 1) * (|M| + 1))) * (|M| + 1) := by gcongr
    _ = ε := by field_simp

theorem tendstoUniformlyOn_bilin' {α ι P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (β : Q →L[ℝ] P →L[ℝ] R) {F : ι → α → P} {G : α → P} {p : Filter ι} {S : Set α}
    (h : TendstoUniformlyOn F G p S) (b : α → Q) (M : ℝ) (hb : ∀ y ∈ S, ‖b y‖ ≤ M) :
    TendstoUniformlyOn (fun t y => β (b y) (F t y)) (fun y => β (b y) (G y)) p S := by
  simpa only [flip_apply] using tendstoUniformlyOn_bilin β.flip h b M hb

theorem tendstoLocallyUniformlyOn_of_nhds {α β ι : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {s : Set α}
    (h : ∀ x ∈ s, ∃ N ∈ 𝓝 x, TendstoUniformlyOn F f p N) : TendstoLocallyUniformlyOn F f p s := by
  intro u hu x hx
  obtain ⟨N, hN, hT⟩ := h x hx
  exact ⟨N, mem_nhdsWithin_of_mem_nhds hN, hT u hu⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

theorem fderiv_fderiv_comp_eq {W : Set X} (hW : IsOpen W) {τ : X → Y}
    (hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y) {U : Set Y} (hWU : MapsTo τ W U) {H : Y → ℝ}
    (hH : ∀ z ∈ U, ContDiffAt ℝ 2 H z) {Fh : X → ℝ} (hF : ∀ y ∈ W, Fh y = H (τ y)) {y : X}
    (hy : y ∈ W) :
    fderiv ℝ Fh y = (fderiv ℝ H (τ y)).comp (fderiv ℝ τ y) ∧
    fderiv ℝ (fderiv ℝ Fh) y =
      (compL ℝ X Y ℝ (fderiv ℝ H (τ y))).comp (fderiv ℝ (fderiv ℝ τ) y) +
        ((compL ℝ X Y ℝ).flip (fderiv ℝ τ y)).comp
          ((fderiv ℝ (fderiv ℝ H) (τ y)).comp (fderiv ℝ τ y)) := by
  have h1 : ∀ y' ∈ W, fderiv ℝ Fh y' = (fderiv ℝ H (τ y')).comp (fderiv ℝ τ y') := by
    intro y' hy'
    have heq : Fh =ᶠ[𝓝 y'] H ∘ τ := by
      filter_upwards [hW.mem_nhds hy'] with z hz using hF z hz
    rw [heq.fderiv_eq]
    exact fderiv_comp y' ((hH _ (hWU hy')).differentiableAt (by norm_num))
      ((hτ y' hy').differentiableAt (by norm_num))
  refine ⟨h1 y hy, ?_⟩
  have hev : fderiv ℝ Fh =ᶠ[𝓝 y] fun y' => (fderiv ℝ H (τ y')).comp (fderiv ℝ τ y') := by
    filter_upwards [hW.mem_nhds hy] with z hz using h1 z hz
  have hH' : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) (τ y)) (τ y) :=
    (((hH _ (hWU hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hT : HasFDerivAt (fderiv ℝ τ) (fderiv ℝ (fderiv ℝ τ) y) y :=
    (((hτ y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasFDerivAt (fun y' => fderiv ℝ H (τ y'))
      ((fderiv ℝ (fderiv ℝ H) (τ y)).comp (fderiv ℝ τ y)) y :=
    hH'.comp y ((hτ y hy).differentiableAt (by norm_num)).hasFDerivAt
  rw [hev.fderiv_eq]
  exact (hc.clm_comp hT).fderiv

theorem local_c2_convergence_pullback {ι : Type*} {p : Filter ι} {W : Set X} (hW : IsOpen W) {τ : X → Y}
    (hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y) {U : Set Y} (hWU : MapsTo τ W U)
    {G : ι → Y → ℝ} {Φ : Y → ℝ} (hG : ∀ᶠ t in p, ∀ z ∈ U, ContDiffAt ℝ 2 (G t) z)
    (hΦ : ∀ z ∈ U, ContDiffAt ℝ 2 Φ z) {F : ι → X → ℝ} {Ψ : X → ℝ}
    (hF : ∀ t, ∀ y ∈ W, F t y = G t (τ y)) (hΨ : ∀ y ∈ W, Ψ y = Φ (τ y))
    {K : Set X} (hK : IsCompact K) (hKW : K ⊆ W)
    (h0 : TendstoUniformlyOn G Φ p (τ '' K))
    (h1 : TendstoUniformlyOn (fun t => fderiv ℝ (G t)) (fderiv ℝ Φ) p (τ '' K))
    (h2 : TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (G t))) (fderiv ℝ (fderiv ℝ Φ)) p
      (τ '' K)) :
    TendstoUniformlyOn F Ψ p K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (F t)) (fderiv ℝ Ψ) p K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (F t))) (fderiv ℝ (fderiv ℝ Ψ)) p K := by
  set_option maxSynthPendingDepth 8 in
    have hsub : K ⊆ τ ⁻¹' (τ '' K) := subset_preimage_image τ K
    have c0 := (h0.comp τ).mono hsub
    have c1 := (h1.comp τ).mono hsub
    have c2 := (h2.comp τ).mono hsub
    have hτc : ContDiffOn ℝ 2 τ W := fun y hy => (hτ y hy).contDiffWithinAt
    have hD1 : ContinuousOn (fderiv ℝ τ) W := hτc.continuousOn_fderiv_of_isOpen hW (by norm_num)
    have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ τ)) W :=
      (hτc.fderiv_of_isOpen hW (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hW le_rfl
    obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn (hD1.mono hKW)
    obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
      (f := fderiv ℝ (fderiv ℝ τ)) (by exact hD2.mono hKW)
    have hP : ∀ y ∈ K, ‖(compL ℝ X Y ℝ).flip (fderiv ℝ τ y)‖ ≤ ‖(compL ℝ X Y ℝ).flip‖ * M1 := by
      intro y hy
      exact ((compL ℝ X Y ℝ).flip.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hM1 y hy) (norm_nonneg _))
    refine ⟨?_, ?_, ?_⟩
    · refine (c0.congr ?_).congr_right ?_
      · exact Eventually.of_forall fun t y hy => (hF t y (hKW hy)).symm
      · exact fun y hy => (hΨ y (hKW hy)).symm
    · have hA := tendstoUniformlyOn_bilin (compL ℝ X Y ℝ) c1 (fderiv ℝ τ) M1 hM1
      refine (hA.congr ?_).congr_right ?_
      · filter_upwards [hG] with t ht y hy
        rw [(fderiv_fderiv_comp_eq hW hτ hWU ht (hF t) (hKW hy)).1]
        simp only [Function.comp_apply, compL_apply]
      · intro y hy
        rw [(fderiv_fderiv_comp_eq hW hτ hWU hΦ hΨ (hKW hy)).1]
        simp only [Function.comp_apply, compL_apply]
    · have hA := tendstoUniformlyOn_bilin (R := X →L[ℝ] X →L[ℝ] ℝ)
        (by exact (compL ℝ X (X →L[ℝ] Y) (X →L[ℝ] ℝ)).comp (compL ℝ X Y ℝ)) c1 (fderiv ℝ (fderiv ℝ τ)) M2 hM2
      have hI := tendstoUniformlyOn_bilin (P := Y →L[ℝ] Y →L[ℝ] ℝ) (Q := X →L[ℝ] Y)
        (R := X →L[ℝ] Y →L[ℝ] ℝ) (by exact compL ℝ X Y (Y →L[ℝ] ℝ)) (by exact c2) (fderiv ℝ τ) M1 hM1
      have hB := tendstoUniformlyOn_bilin' (P := X →L[ℝ] Y →L[ℝ] ℝ)
        (Q := (Y →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ)) (R := X →L[ℝ] X →L[ℝ] ℝ)
        (by exact compL ℝ X (Y →L[ℝ] ℝ) (X →L[ℝ] ℝ)) (by exact hI)
        (fun y => (compL ℝ X Y ℝ).flip (fderiv ℝ τ y)) _ (by exact hP)
      refine ((hA.add hB).congr ?_).congr_right ?_
      · filter_upwards [hG] with t ht y hy
        rw [(fderiv_fderiv_comp_eq hW hτ hWU ht (hF t) (hKW hy)).2]
        simp only [Pi.add_apply, Function.comp_apply, compL_apply, ContinuousLinearMap.comp_apply]
      · intro y hy
        rw [(fderiv_fderiv_comp_eq hW hτ hWU hΦ hΨ (hKW hy)).2]
        simp only [Pi.add_apply, Function.comp_apply, compL_apply, ContinuousLinearMap.comp_apply]

end C2ConvergencePullback

theorem C2ConvergencePullback.proof : C2ConvergencePullback.Statement := by
  intro D E Y Z _ _ B A f hf V hV g φ φ' hφ hφ' hg hconv j K hK hKs
  have hOo : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (f ⁻¹' V)) :=
    (B.chart j).isOpen_inter_preimage_symm (hV.preimage hf.1)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top
  have hloc : ∀ y0 ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (f ⁻¹' V), ∃ N ∈ 𝓝 y0,
      TendstoUniformlyOn (fun t y => (g t ∘ f) ((B.chart j).symm y))
        (fun y => φ' ((B.chart j).symm y)) (𝓝[>] 0) N ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => (g t ∘ f) ((B.chart j).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ' ((B.chart j).symm y')) y) (𝓝[>] 0) N ∧
      TendstoUniformlyOn
        (fun t y => fderiv ℝ (fderiv ℝ fun y' => (g t ∘ f) ((B.chart j).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ' ((B.chart j).symm y')) y) (𝓝[>] 0) N := by
    intro y0 hy0
    obtain ⟨k, hk⟩ := A.cover (f ((B.chart j).symm y0))
    set W := (B.chart j).target ∩ (B.chart j).symm ⁻¹' (f ⁻¹' ((A.chart k).source ∩ V)) with hWdef
    have hWo : IsOpen W :=
      (B.chart j).isOpen_inter_preimage_symm (((A.chart k).open_source.inter hV).preimage hf.1)
    have hy0W : y0 ∈ W := ⟨hy0.1, hk, hy0.2⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hWo.mem_nhds hy0W)
    have hNW : Metric.closedBall y0 (ε / 2) ⊆ W :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
    set U := (A.chart k).target ∩ (A.chart k).symm ⁻¹' V with hUdef
    have hUo : IsOpen U := (A.chart k).isOpen_inter_preimage_symm hV
    set τ := A.chart k ∘ f ∘ (B.chart j).symm with hτdef
    have hτ : ∀ y ∈ W, ContDiffAt ℝ 2 τ y := by
      intro y hy
      have ha : AnalyticAt ℂ τ y := hf.2 j k y ⟨hy.1, hy.2.1⟩
      have hR : AnalyticAt ℝ τ y := ha.restrictScalars
      exact hR.contDiffAt
    have hWU : MapsTo τ W U := by
      intro y hy
      refine ⟨(A.chart k).map_source hy.2.1, ?_⟩
      show (A.chart k).symm ((A.chart k) (f ((B.chart j).symm y))) ∈ V
      rw [(A.chart k).left_inv hy.2.1]
      exact hy.2.2
    have hN : IsCompact (Metric.closedBall y0 (ε / 2)) := isCompact_closedBall _ _
    have hτN : IsCompact (τ '' Metric.closedBall y0 (ε / 2)) :=
      hN.image_of_continuousOn fun y hy => (hτ y (hNW hy)).continuousAt.continuousWithinAt
    obtain ⟨c0, c1, c2⟩ := hconv k _ hτN ((hWU.mono_left hNW).image_subset)
    refine ⟨Metric.closedBall y0 (ε / 2), Metric.closedBall_mem_nhds y0 (half_pos hε), ?_⟩
    refine C2ConvergencePullback.local_c2_convergence_pullback (G := fun t z => g t ((A.chart k).symm z))
      (Φ := fun z => φ ((A.chart k).symm z)) hWo hτ hWU ?_ ?_ ?_ ?_ hN hNW c0 c1 c2
    · filter_upwards [hg] with t ht z hz
      have hs := (show A.SmoothOn Set.univ (g t) from ht) k
      exact (hs.contDiffAt (((A.chart k).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
        ⟨hz.1, trivial⟩)).of_le h2
    · intro z hz
      exact ((hφ k).contDiffAt (hUo.mem_nhds hz)).of_le h2
    · intro t y hy
      show g t (f ((B.chart j).symm y)) =
        g t ((A.chart k).symm ((A.chart k) (f ((B.chart j).symm y))))
      rw [(A.chart k).left_inv hy.2.1]
    · intro y hy
      show φ' ((B.chart j).symm y) = φ ((A.chart k).symm ((A.chart k) (f ((B.chart j).symm y))))
      rw [(A.chart k).left_inv hy.2.1]
      exact hφ' _ hy.2.2
  refine ⟨?_, ?_, ?_⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, h, -, -⟩ := hloc y hy
    exact ⟨N, hN, h⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, -, h, -⟩ := hloc y hy
    exact ⟨N, hN, h⟩
  · refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hOo).1
      (C2ConvergencePullback.tendstoLocallyUniformlyOn_of_nhds fun y hy => ?_) K hKs hK
    obtain ⟨N, hN, -, -, h⟩ := hloc y hy
    exact ⟨N, hN, h⟩

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PHyperplaneDivisible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Metric Set Filter Topology
open scoped Interval

noncomputable section

def coordScale {D : ℕ} (i : Fin D) (t : ℝ) : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) :=
  ContinuousLinearMap.id ℂ _ +
    ((t : ℂ) - 1) • (ContinuousLinearMap.proj i : (Fin D → ℂ) →L[ℂ] ℂ).smulRight (Pi.single i (1 : ℂ))

variable {D : ℕ}

theorem coordScale_apply (i : Fin D) (t : ℝ) (v : Fin D → ℂ) (j : Fin D) :
    coordScale i t v j = if j = i then (t : ℂ) * v i else v j := by
  simp only [coordScale]
  simp only [Pi.single_apply, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  split_ifs <;> subst_vars <;> ring

theorem coordScale_of_eq_zero (i : Fin D) (t : ℝ) {v : Fin D → ℂ} (hv : v i = 0) : coordScale i t v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp [hv]
  · rfl

theorem coordScale_one (i : Fin D) (v : Fin D → ℂ) : coordScale i 1 v = v := by
  funext j; rw [coordScale_apply]; split_ifs with h
  · subst h; simp
  · rfl

theorem norm_coordScale_apply_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : Fin D → ℂ) :
    ‖coordScale i t v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => ?_
  rw [coordScale_apply]
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (norm_le_pi_norm v i)
  · exact norm_le_pi_norm v j

theorem norm_coordScale_le (i : Fin D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖coordScale i t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using norm_coordScale_apply_le i ht v

theorem coordScale_mem_ball (i : Fin D) {p z : Fin D → ℂ} {r t : ℝ} (hp : p i = 0) (hz : z ∈ ball p r)
    (ht : t ∈ Icc (0 : ℝ) 1) : coordScale i t z ∈ ball p r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  calc ‖coordScale i t z - p‖ = ‖coordScale i t (z - p)‖ := by
        rw [map_sub, coordScale_of_eq_zero i t hp]
    _ ≤ ‖z - p‖ := norm_coordScale_apply_le i ht _
    _ < r := hz

theorem hasDerivAt_coordScale (i : Fin D) (z : Fin D → ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordScale i s z) (z i • Pi.single i (1 : ℂ)) t := by
  have h := (((hasDerivAt_id t).ofReal_comp.sub_const (1 : ℂ)).smul_const
    (z i • Pi.single i (1 : ℂ) : Fin D → ℂ)).const_add z
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  funext j
  show coordScale i s z j = _
  rw [coordScale_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, id_eq]
  split_ifs <;> subst_vars <;> ring

theorem continuous_coordScale (i : Fin D) : Continuous (coordScale (D := D) i) :=
  continuous_const.add (((Complex.continuous_ofReal).sub continuous_const).smul continuous_const)

theorem analyticOnNhd_fderiv_apply {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    (v : Fin D → ℂ) : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w v) Ω := fun w hw =>
  (((ContinuousLinearMap.apply ℂ ℂ (E' := Fin D → ℂ) v).analyticAt (fderiv ℂ F w)).comp
    (hF.fderiv w hw)).congr (Eventually.of_forall fun _ => rfl)

theorem eq_mul_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) (h0 : ∀ z ∈ Ω, z i = 0 → F z = 0) {p : Fin D → ℂ} {r : ℝ}
    (hp : p i = 0) (hball : ball p r ⊆ Ω) {z : Fin D → ℂ} (hz : z ∈ ball p r) :
    F z = z i * ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1) := by
  have hFi : AnalyticOnNhd ℂ (fun w => fderiv ℂ F w (Pi.single i 1)) Ω := analyticOnNhd_fderiv_apply hF _
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t z ∈ Ω := fun t ht => hball (coordScale_mem_ball i hp hz ht)
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (coordScale i s z))
      (z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := ((hF _ (hmem t ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (hasDerivAt_coordScale i z t)
    refine h1.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : ContinuousOn (fun t : ℝ => z i * fderiv ℂ F (coordScale i t z) (Pi.single i 1)) (uIcc 0 1) := by
    refine continuousOn_const.mul (hFi.continuousOn.comp
      ((continuous_coordScale i).clm_apply continuous_const).continuousOn fun t ht => hmem t ?_)
    rwa [uIcc_of_le zero_le_one] at ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, coordScale_one,
    h0 _ (hmem 0 ⟨le_rfl, zero_le_one⟩) (by simp [coordScale_apply])] at h
  rw [h, sub_zero]

theorem differentiableOn_integral_partial {Ω : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → ℂ} {i : Fin D}
    (hF : AnalyticOnNhd ℂ F Ω) {p : Fin D → ℂ} {r : ℝ} (hp : p i = 0) (hball : ball p r ⊆ Ω) (hr : 0 < r) :
    DifferentiableOn ℂ (fun z => ∫ t in (0 : ℝ)..1, fderiv ℂ F (coordScale i t z) (Pi.single i 1))
      (ball p (r / 2)) := by
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  have hFi : AnalyticOnNhd ℂ Fi Ω := analyticOnNhd_fderiv_apply hF _
  have hK : closedBall p (r / 2) ⊆ Ω := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hB : ball p (r / 2) ⊆ Ω := ball_subset_closedBall.trans hK
  obtain ⟨C, hC⟩ := (isCompact_closedBall p (r / 2)).exists_bound_of_continuousOn
    (hFi.fderiv.continuousOn.mono hK)
  have hI : ∀ {t : ℝ}, t ∈ Ι (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 := fun ht =>
    Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
  have hmem : ∀ x ∈ ball p (r / 2), ∀ t ∈ Icc (0 : ℝ) 1, coordScale i t x ∈ ball p (r / 2) :=
    fun x hx t ht => coordScale_mem_ball i hp hx ht
  have hcont : ∀ x ∈ ball p (r / 2), ContinuousOn (fun t : ℝ => Fi (coordScale i t x)) (Icc 0 1) :=
    fun x hx => hFi.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x hx t ht)
  intro x₀ hx₀
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (F' := fun x t => (fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)) (bound := fun _ => C)
    (isOpen_ball.mem_nhds hx₀) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [isOpen_ball.mem_nhds hx₀] with x hx
    exact ((hcont x hx).mono fun t ht => hI ht).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont x₀ hx₀).intervalIntegrable_of_Icc zero_le_one
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact ((hFi.fderiv.continuousOn.comp ((continuous_coordScale i).clm_apply continuous_const).continuousOn
      fun t ht => hB (hmem x₀ hx₀ t (hI ht))).clm_comp (continuous_coordScale i).continuousOn)
  · refine Eventually.of_forall fun t ht x hx => ?_
    calc ‖(fderiv ℂ Fi (coordScale i t x)).comp (coordScale i t)‖
        ≤ ‖fderiv ℂ Fi (coordScale i t x)‖ * ‖coordScale i t‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := mul_le_mul (hC _ (ball_subset_closedBall (hmem x hx t (hI ht))))
          (norm_coordScale_le i (hI ht)) (norm_nonneg _)
          ((norm_nonneg _).trans (hC p (mem_closedBall_self (half_pos hr).le)))
      _ = C := mul_one C
  · refine Eventually.of_forall fun t ht x hx => ?_
    exact (hFi _ (hB (hmem x hx t (hI ht)))).differentiableAt.hasFDerivAt.comp x (coordScale i t).hasFDerivAt

theorem HyperplaneDivisible.proof : HyperplaneDivisible.Statement := by
  intro D Ω F i hΩ hF h0
  set Fi : (Fin D → ℂ) → ℂ := fun w => fderiv ℂ F w (Pi.single i 1)
  refine ⟨fun z => if z i = 0 then Fi z else F z / z i, fun p hp => ?_, fun z hz => ?_⟩
  · by_cases hpi : p i = 0
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
      have hH := ReciprocityTheory.AnForm.Osgood.osgood D _ _ isOpen_ball
        (differentiableOn_integral_partial hF hpi hball hr) p (mem_ball_self (half_pos hr))
      refine hH.congr ?_
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hr))] with z hz
      have hz' : z ∈ ball p r := ball_subset_ball (half_le_self hr.le) hz
      by_cases hzi : z i = 0
      · simp only [if_pos hzi, coordScale_of_eq_zero i _ hzi, intervalIntegral.integral_const, Fi]
        simp
      · rw [if_neg hzi, eq_mul_integral_partial hF h0 hpi hball hz', mul_div_cancel_left₀ _ hzi]
    · have hproj : AnalyticAt ℂ (fun z : Fin D → ℂ => z i) p :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt p
      refine ((hF p hp).div hproj hpi).congr ?_
      filter_upwards [(isOpen_ne_fun (continuous_apply i) continuous_const).mem_nhds hpi] with z hz
      simp only [if_neg (show z i ≠ 0 from hz)]
      rfl
  · by_cases hzi : z i = 0
    · simp [hzi, h0 z hz hzi]
    · simp only [if_neg hzi]
      rw [mul_div_cancel₀ _ hzi]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PNormSqSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open scoped ContDiff

theorem NormSqSmooth.proof : NormSqSmooth.Statement := by
  intro X _ D A U g hg j
  have h1 : ContDiffOn ℝ ∞ (g ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    ((hg j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiff ℝ ∞ (fun w : ℂ => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact h2.comp_contDiffOn h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdEqHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdEqHolo.proof : BdEqHolo.Statement := by
  intro X _ D A R j
  refine ⟨fun m v hv => ?_, fun y hy => ?_⟩
  · have h : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) v := (R.compat j m).1 v ⟨hv.1, hv.2.1⟩
    have hi : ∀ i, AnalyticAt ℂ (fun w => (R.ψ j ∘ (A.chart m).symm) w i) v :=
      (analyticAt_pi_iff (f := fun i w => (R.ψ j ∘ (A.chart m).symm) w i)).1 h
    show AnalyticAt ℂ (fun w => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart m).symm) w i) v
    exact Finset.analyticAt_fun_prod _ fun i _ => hi i
  · have hmem := R.mem_Yo_iff j (R.ψ j y) hy.2
    rw [(R.ψ j).left_inv hy.1] at hmem
    rw [hmem, not_not]
    simp only [bdEq, Finset.prod_eq_zero_iff, coordDiv, Set.mem_ofPred_eq]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdSectionProps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

theorem BdSectionProps.proof (hB : BdEqHolo.Statement) : BdSectionProps.Statement := by
  intro X _ D A R φ hφ c
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩
  · exact (h1 (bdIdx R x) j).add contDiffOn_const
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := h2 (bdIdx R x) (bdIdx R x') y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have h := hGe z ⟨hz.1.1, hz.1.2, hz.2⟩
    show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re
    linarith
  · show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) =
      ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))
    simp only [neg_add, Real.exp_add, ← mul_assoc]
    rw [h3 _ _ y hy]
  · ext y
    have h := (hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)
    show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo
    rw [Ne, h, not_not]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdCocycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdCocycle.proof (hDense : RegYoDense.Statement) (hHolo : BdEqHolo.Statement) :
    BdCocycle.Statement := by
  intro X _ D A R g hg hEq j k l
  have hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l) :=
    ((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)
  have hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l := fun _ hy => ⟨hy.1.1, hy.2⟩
  have hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k := fun _ hy => hy.1
  have hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l := fun _ hy => ⟨hy.1.2, hy.2⟩
  have hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y)
      ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo) := by
    rintro y ⟨hyO, hyY⟩
    have hne : bdEq R l y ≠ 0 := fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY
    have h1 := hEq j l y (hOjl hyO)
    have h2 := hEq j k y (hOjk hyO)
    have h3 := hEq k l y (hOkl hyO)
    apply mul_right_cancel₀ hne
    show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y
    rw [← h1, h2, h3, mul_assoc]
  have hall := hYo.of_subset_closure ((hg j l).mono hOjl)
    (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left
    ((hDense D A R).open_subset_closure_inter hOopen)
  intro y hy
  exact hall hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdNormCont
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem BdNormCont.proof (hCC : ChartCont.Statement) (hEq : BdEqHolo.Statement) :
    BdNormCont.Statement := by
  intro X _ D A R φ hφ c
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set j := bdIdx R y₀
  have hU : IsOpen (bdDom R j) := isOpen_bdDom R j
  have hy₀ : y₀ ∈ bdDom R j := mem_bdDom_bdIdx R y₀
  have hEqc : ContinuousOn (bdEq R j) (bdDom R j) := (hCC D A _ hU).2 _ (hEq D A R j).1
  have hφc : ContinuousOn (φ j) (bdDom R j) := (hCC D A _ hU).1 _ (hφ.1 j)
  have hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j) :=
    hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)
  have hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀ :=
    hg.continuousAt (hU.mem_nhds hy₀)
  refine hgy.congr ?_
  filter_upwards [hU.mem_nhds hy₀] with y hy
  have hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j := ⟨mem_bdDom_bdIdx R y, hy⟩
  have h3 := hφ.2.2 (bdIdx R y) j y hk
  show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)
  simp only [bdSec, bdPot]
  simp only [neg_add, Real.exp_add, ← mul_assoc, h3]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PRegYoDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)

theorem dense_compl_coordDiv {D : ℕ} (S : Finset (Fin D)) : Dense (coordDiv S)ᶜ := by
  have h : (coordDiv S)ᶜ = ⋂ i ∈ (S : Set (Fin D)), (fun z : Fin D → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [coordDiv]
  rw [h]
  refine dense_biInter_of_isOpen (fun i _ => ?_) S.countable_toSet (fun i _ => ?_)
  · exact isOpen_compl_singleton.preimage (continuous_apply i)
  · exact (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)

theorem RegYoDense.proof : RegYoDense.Statement := by
  intro X _ D A R
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hxU⟩
  have hxj : x ∈ bdDom R (bdIdx R x) := mem_bdDom_bdIdx R x
  set j := bdIdx R x
  have hO : IsOpen ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))) :=
    (R.ψ j).isOpen_image_source_inter (hU.inter (isOpen_bdDom R j))
  have hne : ((R.ψ j) '' ((R.ψ j).source ∩ (U ∩ bdDom R j))).Nonempty :=
    ⟨R.ψ j x, x, ⟨hxj.1, hxU, hxj⟩, rfl⟩
  obtain ⟨z, ⟨y, ⟨hys, hyU, hyD⟩, rfl⟩, hz⟩ :=
    (dense_compl_coordDiv (R.S j)).inter_open_nonempty _ hO hne
  have hYo := (R.mem_Yo_iff j (R.ψ j y) hyD.2).2 hz
  rw [(R.ψ j).left_inv hys] at hYo
  exact ⟨y, hyU, hYo⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PChartCont
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem continuousOn_of_chart_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {U : Set X} (hU : IsOpen U) {E : Type} [TopologicalSpace E] (h : X → E)
    (hc : ∀ j, ContinuousOn (h ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn h U := by
  intro x hx
  obtain ⟨m, hm⟩ := A.cover x
  set c := A.chart m
  have hT : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hcx : c x ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hm, by simpa [c.left_inv hm] using hx⟩
  have h1 : ContinuousAt (h ∘ c.symm) (c x) := (hc m).continuousAt (hT.mem_nhds hcx)
  have h2 : ContinuousAt ((h ∘ c.symm) ∘ c) x := by
    apply ContinuousAt.comp (f := c)
    · exact h1
    · exact c.continuousAt hm
  have heq : (h ∘ c.symm) ∘ c =ᶠ[nhds x] h := by
    filter_upwards [c.open_source.mem_nhds hm] with y hy
    simp [c.left_inv hy]
  exact (h2.congr heq).continuousWithinAt

theorem ChartCont.proof : ChartCont.Statement := by
  intro X _ D A U hU
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · exact continuousOn_of_chart_continuousOn A hU f fun j => (hf j).continuousOn
  · exact continuousOn_of_chart_continuousOn A hU g fun j => (hg j).continuousOn

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBddOnInner
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem bdDom_compact_inner {D : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (j : Fin R.n) :
    IsCompact ((R.ψ j).symm '' closure (R.W'' j)) ∧
      (R.ψ j).symm '' closure (R.W'' j) ⊆ bdDom R j ∧
      R.V'' j ⊆ (R.ψ j).symm '' closure (R.W'' j) := by
  have hW : closure (R.W'' j) ⊆ R.W j :=
    (R.closure_W''_subset j).trans (subset_closure.trans (R.closure_W'_subset j))
  have hT : closure (R.W'' j) ⊆ (R.ψ j).target := hW.trans (R.W_subset j)
  have hc : IsCompact (closure (R.W'' j)) :=
    (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
      ((R.closure_W''_subset j).trans subset_closure)
  refine ⟨hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hT), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(R.ψ j).map_target (hT hz), ?_⟩
    show R.ψ j ((R.ψ j).symm z) ∈ R.W j
    rw [(R.ψ j).right_inv (hT hz)]
    exact hW hz
  · intro y hy
    exact ⟨R.ψ j y, subset_closure hy.2, (R.ψ j).left_inv hy.1⟩

theorem BddOnInner.proof : BddOnInner.Statement := by
  intro X _ D A R j u hu
  obtain ⟨hK, hKD, hVK⟩ := bdDom_compact_inner R j
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hu.mono hKD)
  exact ⟨B, fun y hy => by simpa [Real.norm_eq_abs] using hB y (hVK hy)⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PIndicatorSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open Filter Topology
open scoped ContDiff

theorem IndicatorSmooth.proof : IndicatorSmooth.Statement := by
  intro X _ D A U O χ h hU hO hχ hsupp hh j
  set φ := A.chart j
  refine fun v hv => (?_ : ContDiffAt ℝ ∞ _ v).contDiffWithinAt
  by_cases hx : φ.symm v ∈ O
  ·
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := φ.isOpen_inter_preimage_symm (hU.inter hO)
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (U ∩ O) := ⟨hv.1, hv.2, hx⟩
    have hχT : ContDiffOn ℝ ∞ (χ ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) :=
      (hχ j).mono fun z hz => ⟨hz.1, Set.mem_univ _⟩
    have hprod : ContDiffOn ℝ ∞ (fun z => (χ ∘ φ.symm) z * (h ∘ φ.symm) z)
        (φ.target ∩ φ.symm ⁻¹' (U ∩ O)) := hχT.mul (hh j)
    refine (hprod.contDiffAt (hT.mem_nhds hvT)).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    simp [Function.comp, Set.indicator_of_mem hz.2.2]
  ·
    have hns : φ.symm v ∉ tsupport χ := fun hm => hx (hsupp hm)
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ) :=
      φ.isOpen_inter_preimage_symm (isClosed_tsupport χ).isOpen_compl
    have hvT : v ∈ φ.target ∩ φ.symm ⁻¹' (tsupport χ)ᶜ := ⟨hv.1, hns⟩
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hT.mem_nhds hvT] with z hz
    have h0 : χ (φ.symm z) = 0 := image_eq_zero_of_notMem_tsupport hz.2
    by_cases hzO : φ.symm z ∈ O
    · simp [Function.comp, Set.indicator_of_mem hzO, h0]
    · simp [Function.comp, Set.indicator_of_notMem hzO]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open scoped ContDiff

noncomputable section

theorem BdPartition.proof : BdPartition.Statement := by
  intro X _ _ _ D A R
  set e : Fin R.n → OpenPartialHomeomorph X (Fin D → ℂ) :=
    fun j => (R.ψ j).restrOpen (bdDom R j) (isOpen_bdDom R j) with he
  have hsrc : ∀ j, (e j).source = bdDom R j := by
    intro j
    simp only [he, OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.2 Set.inter_subset_left
  have hc : ∀ j, IsCompatChart A (e j) := fun j =>
    ReciprocityTheory.AnForm.M.pa_compat_restr A (R.ψ j) (R.compat j) _ (isOpen_bdDom R j)
  have hcov : ∀ x, ∃ j, x ∈ (e j).source := fun x =>
    ⟨bdIdx R x, by rw [hsrc]; exact mem_bdDom_bdIdx R x⟩
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := fun i j =>
    ReciprocityTheory.AnForm.M.pa_holoSmooth _ _ fun v hv =>
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (hc i) (hc j) hv.1 hv.2
  obtain ⟨χ, h0, h1, hs, hsm⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  obtain ⟨B, hAB, -, hB⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A e hc hcov
  have hBs : ∀ i, B.Smooth (χ i) := by
    intro i j
    obtain ⟨l, hl⟩ := hB j
    rw [hl]
    exact (hsm i l).mono Set.inter_subset_left
  refine ⟨χ, fun i => ReciprocityTheory.AnForm.M.smoothOn_of_compatible hAB.symm' isOpen_univ (hBs i),
    h0, h1, fun i => ?_⟩
  rw [← hsrc]
  exact hs i

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem BdWeight.proof (hP : BdPartition.Statement) (hI : IndicatorSmooth.Statement)
    (hN : NormSqSmooth.Statement) : BdWeight.Statement := by
  intro X _ _ _ D A R g hg hg0 hcoc
  obtain ⟨χ, hχs, hχ0, hχ1, hχsupp⟩ := hP D A R
  refine ⟨bdWeight R χ g, ?_, ?_, ?_⟩
  · intro j i
    have hterm : ∀ l, A.SmoothOn (bdDom R j)
        ((bdDom R l).indicator fun z => χ l z * ‖g j l z‖ ^ 2) := fun l =>
      hI D A (bdDom R j) (bdDom R l) (χ l) (fun z => ‖g j l z‖ ^ 2) (isOpen_bdDom R j)
        (isOpen_bdDom R l) (hχs l) (hχsupp l) (hN D A _ (g j l) (hg j l))
    have h := ContDiffOn.sum (s := Finset.univ) (fun l _ => hterm l i)
    convert h using 1
    ext x
    simp [bdWeight]
  · intro j y hy
    obtain ⟨l, hl⟩ : ∃ l, 0 < χ l y := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have h1 := hχ1 y
      have h2 : ∑ l, χ l y ≤ 0 := Finset.sum_nonpos fun l _ => h l
      linarith
    have hyl : y ∈ bdDom R l := hχsupp l (subset_tsupport _ (ne_of_gt hl))
    have hgne : g j l y ≠ 0 := hg0 j l y ⟨hy, hyl⟩
    unfold bdWeight
    refine Finset.sum_pos' (fun i _ => Set.indicator_nonneg
      (fun z _ => mul_nonneg (hχ0 i z) (sq_nonneg _)) y) ⟨l, Finset.mem_univ _, ?_⟩
    rw [Set.indicator_of_mem hyl]
    exact mul_pos hl (pow_pos (norm_pos_iff.mpr hgne) 2)
  · rintro j k y ⟨hyj, hyk⟩
    unfold bdWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hyl : y ∈ bdDom R l
    · simp only [Set.indicator_of_mem hyl]
      rw [hcoc j k l y ⟨⟨hyj, hyk⟩, hyl⟩, norm_mul, mul_pow]
      ring
    · simp [hyl]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBdComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdComparison.proof (hCC : ChartCont.Statement) (hBI : BddOnInner.Statement) :
    BdComparison.Statement := by
  intro X _ D A R φ hφ c
  have hp : ∀ j, ∃ B : ℝ, ∀ y ∈ R.V'' j, |φ j y| ≤ B := fun j =>
    hBI D A R j (φ j) ((hCC D A (bdDom R j) (isOpen_bdDom R j)).1 _ (hφ.1 j))
  choose Bf hBf using R.f_bdd
  choose Bp hBp using hp
  refine ⟨∑ j, (|Bf j| + 2 * |Bp j|) + 2 * |c|, fun y hy => ?_⟩
  have hV := mem_V''_bdIdx R y
  have hdom := V''_subset_bdDom R _ hV
  set j := bdIdx R y with hj
  have hW : R.ψ j y ∈ R.W j := hdom.2
  have hsymm : (R.ψ j).symm (R.ψ j y) = y := (R.ψ j).left_inv hV.1
  have hnd : R.ψ j y ∉ coordDiv (R.S j) := by
    rw [← R.mem_Yo_iff j _ hW, hsymm]; exact hy
  have hz : ∀ i ∈ R.S j, R.ψ j y i ≠ 0 := fun i hi h => hnd ⟨i, hi, h⟩
  have hr := R.r_chart j (R.ψ j y) ⟨hW, hnd⟩
  rw [hsymm] at hr
  have hs : rSec (bdPot R φ c) (bdSec R) y =
      Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c) := by
    have hprod : ‖∏ i ∈ R.S j, R.ψ j y i‖ ≠ 0 :=
      norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 hz)
    simp only [rSec, logNormSec, bdPot, bdSec, bdEq, ← hj]
    rw [Real.log_mul hprod (Real.exp_pos _).ne', Real.log_exp, norm_prod,
      Real.log_prod (fun i hi => norm_ne_zero_iff.2 (hz i hi))]
    simp only [Real.log_pow, Nat.cast_ofNat, ← Finset.mul_sum]
    ring
  rw [hr, hs]
  have e : Real.exp 1 + R.f j (R.ψ j y) - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) -
      (Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c)) =
      R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c := by ring
  rw [e]
  have h1 : |R.f j (R.ψ j y)| ≤ |Bf j| := (hBf j _ hW).trans (le_abs_self _)
  have h2 : |φ j y| ≤ |Bp j| := (hBp j y hV).trans (le_abs_self _)
  have h3 : |Bf j| + 2 * |Bp j| ≤ ∑ k, (|Bf k| + 2 * |Bp k|) :=
    Finset.single_le_sum (f := fun k => |Bf k| + 2 * |Bp k|)
      (fun k _ => by positivity) (Finset.mem_univ j)
  calc |R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c|
      ≤ |R.f j (R.ψ j y)| + |(-2) * φ j y| + |(-2) * c| := abs_add_three _ _ _
    _ = |R.f j (R.ψ j y)| + 2 * |φ j y| + 2 * |c| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ ∑ k, (|Bf k| + 2 * |Bp k|) + 2 * |c| := by linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
