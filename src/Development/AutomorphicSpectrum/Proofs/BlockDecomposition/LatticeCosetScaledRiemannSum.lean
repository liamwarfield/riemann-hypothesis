module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePointCountScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePointCountScaling
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.RiemannCore

theorem tile_sum_estimate {G ι : Type} [MeasurableSpace G] [Countable ι] (μ : Measure G)
    (tile : ι → Set G) (hm : ∀ i, MeasurableSet (tile i))
    (hd : Pairwise (Function.onFun Disjoint tile)) (hc : ⋃ i, tile i = Set.univ) (n : ℕ)
    (hn : ∀ i, μ (tile i) = n) (a : ι → ℝ) (ha : Summable a) (f g : G → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ i, ∀ y ∈ tile i, |a i - f y| ≤ g y) :
    |(n : ℝ) * ∑' i, a i - ∫ y, f y ∂μ| ≤ ∫ y, g y ∂μ := by
  have hsum : ∀ {u : G → ℝ}, Integrable u μ →
      HasSum (fun i => ∫ y in tile i, u y ∂μ) (∫ y, u y ∂μ) := by
    intro u hu
    have := hasSum_integral_iUnion (f := u) (μ := μ) hm hd (by rw [hc]; exact hu.integrableOn)
    rwa [hc, setIntegral_univ] at this
  have hfin : ∀ i, μ (tile i) ≠ ⊤ := fun i => by rw [hn]; exact ENNReal.natCast_ne_top n
  have hconst : ∀ i, ∫ y in tile i, (a i - f y) ∂μ = (n : ℝ) * a i - ∫ y in tile i, f y ∂μ := by
    intro i
    have hi : Integrable (fun _ : G => a i) (μ.restrict (tile i)) := integrableOn_const (hfin i)
    rw [integral_sub hi hf.integrableOn, setIntegral_const]
    simp [Measure.real, hn, smul_eq_mul]
  have hA : HasSum (fun i => ∫ y in tile i, (a i - f y) ∂μ)
      ((n : ℝ) * ∑' i, a i - ∫ y, f y ∂μ) := by
    simp_rw [hconst]
    exact (ha.hasSum.mul_left _).sub (hsum hf)
  have key := hA.norm_le_of_bounded (hsum hg) (fun i => by
    refine norm_integral_le_of_norm_le hg.integrableOn ?_
    exact ae_restrict_of_forall_mem (hm i) (fun y hy => by
      simpa [Real.norm_eq_abs] using h i y hy))
  simpa [Real.norm_eq_abs] using key

section
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem exists_nhds_close (φ : G → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ)
    {δ : ℝ} (hδ : 0 < δ) : ∃ V ∈ 𝓝 (0 : G), ∀ a b, a - b ∈ V → |φ a - φ b| < δ := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have huc : UniformContinuous φ := hs.uniformContinuous_of_continuous hc
  have hmem := huc (Metric.dist_mem_uniformity hδ)
  rw [uniformity_eq_comap_nhds_zero G] at hmem
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.1 hmem
  refine ⟨V, hV, fun a b hab => ?_⟩
  have h1 : (b, a) ∈ (fun p : G × G => p.2 - p.1) ⁻¹' V := hab
  have h2 := hsub h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.dist_eq] at h2
  rwa [abs_sub_comm]

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]

def cell (D : Set G) (R : Finset G) : Set G := ⋃ r ∈ R, (fun y => -r + y) ⁻¹' D

def tile (D : Set G) (R : Finset G) (l : G) : Set G := (fun y => -l + y) ⁻¹' cell D R

theorem mem_tile {D : Set G} {R : Finset G} {l y : G} :
    y ∈ tile D R l ↔ ∃ r ∈ R, y - r - l ∈ D := by
  simp only [tile, cell, Set.mem_preimage, Set.mem_iUnion, exists_prop]
  refine exists_congr fun r => and_congr Iff.rfl ?_
  have : -r + (-l + y) = y - r - l := by abel
  rw [this]

theorem measurableSet_cell {D : Set G} (hD : MeasurableSet D) (R : Finset G) :
    MeasurableSet (cell D R) :=
  Finset.measurableSet_biUnion _ fun r _ => (measurable_const_add (-r)) hD

theorem measurableSet_tile {D : Set G} (hD : MeasurableSet D) (R : Finset G) (l : G) :
    MeasurableSet (tile D R l) :=
  (measurable_const_add (-l)) (measurableSet_cell hD R)

theorem measure_tile (μ : Measure G) [μ.IsAddHaarMeasure] {D : Set G} (hD : MeasurableSet D)
    (hD1 : μ D = 1) (R : Finset G) (Λ : AddSubgroup G)
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) (l : G) :
    μ (tile D R l) = (R.card : ENNReal) := by
  rw [tile, measure_preimage_add, cell, measure_biUnion_finset]
  · simp [measure_preimage_add, hD1]
  · intro r hr r' hr' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne ?_
    simp only [Set.mem_preimage] at hy hy'
    have e1 : y - r - 0 ∈ D := by
      have : -r + y = y - r - 0 := by abel
      rwa [← this]
    have e2 : y - r' - 0 ∈ D := by
      have : -r' + y = y - r' - 0 := by abel
      rwa [← this]
    have := (ht y).unique (y₁ := (r, 0)) (y₂ := (r', 0)) ⟨hr, Λ.zero_mem, e1⟩ ⟨hr', Λ.zero_mem, e2⟩
    exact congrArg Prod.fst this
  · exact fun r _ => (measurable_const_add (-r)) hD

theorem tile_disjoint {D : Set G} {R : Finset G} {Λ : AddSubgroup G}
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) :
    Pairwise (Function.onFun Disjoint fun l : Λ => tile D R (l : G)) := by
  intro l l' hne
  refine Set.disjoint_left.2 fun y hy hy' => hne ?_
  obtain ⟨r, hr, h⟩ := mem_tile.1 hy
  obtain ⟨r', hr', h'⟩ := mem_tile.1 hy'
  have := (ht y).unique (y₁ := (r, (l : G))) (y₂ := (r', (l' : G))) ⟨hr, l.2, h⟩ ⟨hr', l'.2, h'⟩
  exact Subtype.ext (congrArg Prod.snd this)

theorem tile_cover {D : Set G} {R : Finset G} {Λ : AddSubgroup G}
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) :
    ⋃ l : Λ, tile D R (l : G) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨⟨r, l⟩, ⟨hr, hl, h⟩, -⟩ := ht y
  exact Set.mem_iUnion.2 ⟨⟨l, hl⟩, mem_tile.2 ⟨r, hr, h⟩⟩

theorem finite_lattice_points (μ : Measure G) [μ.IsAddHaarMeasure] {D K₀ : Set G}
    (hD : MeasurableSet D) (hK : IsCompact K₀) (hDK : D ⊆ K₀) (hD1 : μ D = 1) (R : Finset G)
    (Λ : AddSubgroup G) (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D)
    (x0 : G) {C : Set G} (hC : IsCompact C) : {l : Λ | x0 + (l : G) ∈ C}.Finite := by
  have hR : 1 ≤ R.card := by
    obtain ⟨⟨r, l⟩, ⟨hr, -, -⟩, -⟩ := ht 0
    exact Finset.card_pos.2 ⟨r, hr⟩
  set Q : Set G := (fun p : G × G × G => p.1 - x0 + p.2.1 + p.2.2) '' (C ×ˢ ((R : Set G) ×ˢ K₀))
    with hQ
  have hQc : IsCompact Q :=
    (hC.prod (R.finite_toSet.isCompact.prod hK)).image (by fun_prop)
  let As : {l : Λ // x0 + (l : G) ∈ C} → Set G := fun l => tile D R ((l : Λ) : G)
  have hsub : ⋃ i, As i ⊆ Q := by
    refine Set.iUnion_subset fun l y hy => ?_
    obtain ⟨r, hr, h⟩ := mem_tile.1 hy
    refine ⟨(x0 + ((l : Λ) : G), r, y - r - ((l : Λ) : G)), ⟨l.2, hr, hDK h⟩, ?_⟩
    simp only
    abel
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion μ (ε := 1) one_pos (As := As)
    (fun l => measurableSet_tile hD R _)
    (fun l l' hne => tile_disjoint ht (fun h => hne (Subtype.ext h)))
    (ne_top_of_le_ne_top hQc.measure_lt_top.ne (measure_mono hsub))
  have huniv : {i | (1 : ENNReal) ≤ μ (As i)} = Set.univ := by
    refine Set.eq_univ_of_forall fun l => ?_
    show 1 ≤ μ (tile D R _)
    rw [measure_tile μ hD hD1 R Λ ht]
    exact_mod_cast hR
  rw [huniv] at hfin
  exact Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hfin)

theorem scaling (μ : Measure G) {τ : G → G} (hτ : MeasurableEmbedding τ) {c : ℝ} (hc : 0 ≤ c)
    (hmap : Measure.map τ μ = ENNReal.ofReal c • μ) {h : G → ℝ} (hh : Integrable h μ) :
    Integrable (fun y => h (τ y)) μ ∧ ∫ y, h (τ y) ∂μ = c * ∫ y, h y ∂μ := by
  constructor
  · have h1 : Integrable h (Measure.map τ μ) := by
      rw [hmap]; exact hh.smul_measure ENNReal.ofReal_ne_top
    exact hτ.integrable_map_iff.1 h1
  · rw [← hτ.integral_map, hmap, integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]

end

theorem main : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by
  intro G _ _ _ _ _ _ _ _ μ _ Λ _ D K₀ R T M hD hK hDK hD1 ht hcont hinv hscale hshrink x0 φ hφc hφs
  let τ : ∀ ε : ℝ, 0 < ε → G ≃ₜ G := fun ε hε =>
    { toFun := T ε
      invFun := T ε⁻¹
      left_inv := fun y => (hinv ε hε y).1
      right_inv := fun y => (hinv ε hε y).2
      continuous_toFun := hcont ε hε
      continuous_invFun := hcont ε⁻¹ (inv_pos.2 hε) }
  have hsummable : ∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l)) := by
    intro ε hε
    have hfin := finite_lattice_points μ hD hK hDK hD1 R Λ ht x0 (C := T ε⁻¹ '' tsupport φ)
      (IsCompact.image hφs (hcont _ (inv_pos.2 hε)))
    refine summable_of_hasFiniteSupport (hfin.subset ?_)
    intro l hl
    exact ⟨T ε (x0 + l), subset_tsupport _ hl, (hinv ε hε _).1⟩
  refine ⟨hsummable, ?_⟩
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (0 : G)
  set C : Set G := (fun p : G × G => p.1 - p.2) '' (tsupport φ ×ˢ W) with hC
  have hCc : IsCompact C := (IsCompact.prod hφs hWc).image (by fun_prop)
  have hCm : MeasurableSet C := hCc.measurableSet
  set B : Set G := (fun p : G × G => x0 - p.1 - p.2) '' ((R : Set G) ×ˢ K₀) with hB
  have hBc : IsCompact B := (R.finite_toSet.isCompact.prod hK).image (by fun_prop)
  have hRpos : (0 : ℝ) < R.card := by
    obtain ⟨⟨r, l⟩, ⟨hr, -, -⟩, -⟩ := ht 0
    exact_mod_cast Finset.card_pos.2 ⟨r, hr⟩
  have hφi : Integrable φ μ := hφc.integrable_of_hasCompactSupport hφs
  have hCi : Integrable (C.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hCm).2 (integrableOn_const hCc.measure_lt_top.ne)
  have hkey : ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |ε ^ M * ∑' l : Λ, φ (T ε (x0 + l)) - (R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ| ≤
        δ * (μ.real C / R.card) := by
    intro δ hδ
    obtain ⟨V₁, hV₁, hclose⟩ := exists_nhds_close φ hφc hφs hδ
    filter_upwards [hshrink B hBc (V₁ ∩ W) (inter_mem hV₁ hW), self_mem_nhdsWithin]
      with ε hε hpos
    have hpos' : 0 < ε := hpos
    have hpow : 0 < ε ^ M := pow_pos hpos' M
    have hemb : MeasurableEmbedding (T ε) := (τ ε hpos').measurableEmbedding
    obtain ⟨hi1, he1⟩ := scaling μ hemb (inv_nonneg.2 hpow.le) (hscale ε hpos') hφi
    obtain ⟨hi2, he2⟩ := scaling μ hemb (inv_nonneg.2 hpow.le) (hscale ε hpos') hCi
    have est := tile_sum_estimate μ (fun l : Λ => tile D R (l : G))
      (fun l => measurableSet_tile hD R _) (tile_disjoint ht) (tile_cover ht) R.card
      (fun l => measure_tile μ hD hD1 R Λ ht _) (fun l : Λ => φ (T ε (x0 + l)))
      (hsummable ε hpos') (fun y => φ (T ε y))
      (fun y => δ * C.indicator (fun _ => (1 : ℝ)) (T ε y)) hi1 (hi2.const_mul δ) (by
        intro l y hy
        obtain ⟨r, hr, hyd⟩ := mem_tile.1 hy
        have hb : x0 + (l : G) - y ∈ B :=
          ⟨(r, y - r - l), ⟨hr, hDK hyd⟩, by simp only; abel⟩
        have hTU := hε _ hb
        rw [map_sub] at hTU
        generalize T ε (x0 + (l : G)) = a at hTU ⊢
        generalize T ε y = b at hTU ⊢
        by_cases hbC : b ∈ C
        · rw [Set.indicator_of_mem hbC]
          simpa using (hclose a b hTU.1).le
        · have hb0 : φ b = 0 := by
            by_contra h
            exact hbC ⟨(b, 0), ⟨subset_tsupport _ h, mem_of_mem_nhds hW⟩, by simp⟩
          have ha0 : φ a = 0 := by
            by_contra h
            exact hbC ⟨(a, a - b), ⟨subset_tsupport _ h, hTU.2⟩, by simp⟩
          rw [Set.indicator_of_notMem hbC]
          simp [ha0, hb0])
    rw [he1, integral_const_mul, he2, integral_indicator_const _ hCm] at est
    simp only [smul_eq_mul, mul_one] at est
    have hid : ε ^ M * ∑' l : Λ, φ (T ε (x0 + l)) - (R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ =
        (ε ^ M / R.card) * ((R.card : ℝ) * ∑' l : Λ, φ (T ε (x0 + l)) -
          (ε ^ M)⁻¹ * ∫ y, φ y ∂μ) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos (div_pos hpow hRpos)]
    calc ε ^ M / R.card * _ ≤ ε ^ M / R.card * (δ * ((ε ^ M)⁻¹ * μ.real C)) :=
          mul_le_mul_of_nonneg_left est (div_pos hpow hRpos).le
      _ = δ * (μ.real C / R.card) := by field_simp
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK0 : 0 ≤ μ.real C / R.card := div_nonneg measureReal_nonneg hRpos.le
  set L := μ.real C / R.card with hL
  have hδ : 0 < η / (L + 1) := by positivity
  filter_upwards [hkey _ hδ] with ε hε
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hε ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.RiemannCore
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePointCountScalingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_point_count_scaling : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.RiemannCore.main | exact GlobalTheory.CompanionTheory.RiemannCore.main | (intros; apply GlobalTheory.CompanionTheory.RiemannCore.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalingMeasureProductArchimedean
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalingMeasureProductArchimedean
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.InfScale

open GlobalTheory.CompanionTheory.SW.LocInf

theorem eInf_theta {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F) (t : ℝ)
    (w : InfinitePlace F) : eInf F h (θ t) w = t := by
  have key : ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp
      ((eInf F h).toRingHom.comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  exact congrArg (fun f : ℝ →+* ℝ => f t) key

theorem finrank_fun_places (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) :
    Module.finrank ℝ (InfinitePlace F → ℝ) = Module.finrank ℚ F := by
  haveI := h
  rw [Module.finrank_fintype_fun_eq_card, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]

theorem map_theta_mul {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (li : Measure (Ainf F)) [li.IsAddHaarMeasure] {ε : ℝ} (hε : 0 < ε) :
    Measure.map (fun y : Ainf F => θ ε * y) li =
      ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  have hL : Measurable (fun x : InfinitePlace F → ℝ => ε • x) := (continuous_const_smul ε).measurable
  have hθ : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
    funext y
    apply (eInf F h).injective
    simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
    funext w
    rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  have hdet : LinearMap.det (ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ))) ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ hε.ne'
  have hmapL := Measure.map_linearMap_addHaar_eq_smul_addHaar (Measure.map (eInf F h) li) hdet
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, finrank_fun_places F h] at hmapL
  have hcoe : (⇑(ε • (LinearMap.id : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ)))) =
      fun x => ε • x := by
    funext x
    simp
  rw [hcoe] at hmapL
  have hid : (eInf F h).symm ∘ (eInf F h) = id := by
    funext x
    simp
  rw [hθ, ← Measure.map_map hms (hL.comp hm), ← Measure.map_map hL hm, hmapL, Measure.map_smul,
    Measure.map_map hms hm, hid, Measure.map_id, abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  exact hms.aemeasurable

theorem pi_const_smul {X : Type} [MeasurableSpace X] (ι : Type) [Fintype ι] (μ : Measure X) [SigmaFinite μ]
    (c : ENNReal) [SigmaFinite (c • μ)] :
    (Measure.pi fun _ : ι => c • μ) = c ^ Fintype.card ι • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

theorem map_theta_mul_pi : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε →
    Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) =
      ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  intro F _ _ h θ _ li _ ι _ ε hε
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have h1 := map_theta_mul h θ li hε
  have hc : Continuous (eInf F h) := continuous_eInf F h
  have hcs : Continuous (eInf F h).symm := continuous_eInf_symm F h
  have hm : Measurable (eInf F h) := hc.measurable
  have hms : Measurable (eInf F h).symm := hcs.measurable
  haveI : (Measure.map (eInf F h) li).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map li (eInf F h).toAddEquiv hc hcs
  haveI : SigmaFinite (Measure.map (eInf F h) li) := Measure.IsAddHaarMeasure.sigmaFinite _
  let me : (InfinitePlace F → ℝ) ≃ᵐ Ainf F :=
    { toEquiv := (eInf F h).symm.toEquiv
      measurable_toFun := hms
      measurable_invFun := hm }
  have hme : (⇑me : (InfinitePlace F → ℝ) → Ainf F) = (eInf F h).symm := rfl
  have hli : Measure.map me (Measure.map (eInf F h) li) = li := by
    rw [Measure.map_map me.measurable hm, hme]
    have hid : ((eInf F h).symm ∘ (eInf F h)) = id := by
      funext x
      simp
    rw [hid, Measure.map_id]
  haveI : SigmaFinite li := by
    rw [← hli]
    exact MeasurableEquiv.sigmaFinite_map me
  haveI hsf : SigmaFinite (ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li) := by
    have hle : ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li =
        ((ε ^ Module.finrank ℚ F)⁻¹).toNNReal • li := rfl
    rw [hle]
    infer_instance
  have hmeas : Measurable (fun y : Ainf F => θ ε * y) := by
    have hθ' : (fun y : Ainf F => θ ε * y) = (eInf F h).symm ∘ (fun x => ε • x) ∘ (eInf F h) := by
      funext y
      apply (eInf F h).injective
      simp only [Function.comp_apply, RingEquiv.apply_symm_apply, map_mul]
      funext w
      rw [Pi.mul_apply, Pi.smul_apply, eInf_theta h θ ε w, smul_eq_mul]
    rw [hθ']
    exact hms.comp ((continuous_const_smul ε).measurable.comp hm)
  have h2 := Measure.pi_map_pi (μ := fun _ : ι => li) (f := fun _ y => θ ε * y)
    (hμ := fun _ => by
      show SigmaFinite (Measure.map (fun y : Ainf F => θ ε * y) li)
      rw [h1]
      exact hsf)
    (fun _ => hmeas.aemeasurable)
  rw [h2]
  simp only [h1]
  rw [pi_const_smul ι li _, ← ENNReal.ofReal_pow (inv_nonneg.mpr (pow_nonneg hε.le _)), inv_pow, ← pow_mul]

end GlobalTheory.CompanionTheory.Equi.InfScale

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalingMeasureProductArchimedeanStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_measure_product_archimedean : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε → Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) = ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  first | exact @GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | exact GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | (intros; apply GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFundamentalDomainIntegers
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFundamentalDomainIntegers
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi

open GlobalTheory.CompanionTheory.SW.RealCoord

section Domain

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def infToMixed (y : Ainf F) : mixedEmbedding.mixedSpace F := toMixed F (coord F y)

theorem infToMixed_add (x y : Ainf F) : infToMixed F (x + y) = infToMixed F x + infToMixed F y := by
  show toMixed F (coord F (x + y)) = toMixed F (coord F x) + toMixed F (coord F y)
  rw [map_add (f := _), toMixed_add]

theorem infToMixed_algebraMap (x : F) :
    infToMixed F (algebraMap F (Ainf F) x) = mixedEmbedding F x := toMixed_coord_algebraMap F x

theorem infToMixed_sub (x y : Ainf F) : infToMixed F (x - y) = infToMixed F x - infToMixed F y := by
  rw [eq_sub_iff_add_eq, ← infToMixed_add, sub_add_cancel]

theorem measurable_infToMixed : Measurable (infToMixed F) := (measurePreserving_toMixed F).measurable.comp (coord_measurable F)

def infDomain : Set (Ainf F) :=
  infToMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem measurableSet_infDomain : MeasurableSet (infDomain F) := measurable_infToMixed F (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F))

theorem exists_mem_lattice {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
  rw [mixedEmbedding.mem_span_latticeBasis F] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

theorem mem_lattice (a : 𝓞 F) :
    mixedEmbedding F (a : F) ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := (mixedEmbedding.mem_span_latticeBasis F).2 ⟨a, rfl⟩

theorem existsUnique_sub_mem_infDomain (y : Ainf F) :
    ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ infDomain F := by
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F)
    (infToMixed F y)
  obtain ⟨a, ha⟩ := exists_mem_lattice F (Submodule.neg_mem _ v.2)
  have key : ∀ b : 𝓞 F, infToMixed F (y - algebraMap F (Ainf F) (b : F)) =
      -mixedEmbedding F (b : F) + infToMixed F y := fun b => by
    rw [infToMixed_sub, infToMixed_algebraMap]
    abel
  refine ⟨a, ?_, fun b hb => ?_⟩
  · show infToMixed F (y - algebraMap F (Ainf F) (a : F)) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [key, ha, neg_neg]
    exact hv
  · have hw := huniq ⟨-mixedEmbedding F (b : F), neg_mem (mem_lattice F b)⟩ (by
      show -mixedEmbedding F (b : F) + infToMixed F y ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
      rw [← key]
      exact hb)
    have hb' : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      have := congrArg Subtype.val hw
      simp only at this
      rw [← this, neg_neg]
    exact RingOfIntegers.ext (mixedEmbedding_injective F hb')

theorem exists_isCompact_superset_infDomain :
    ∃ K₀ : Set (Ainf F), IsCompact K₀ ∧ infDomain F ⊆ K₀ := by
  let g : mixedEmbedding.mixedSpace F → (InfinitePlace F → ℝ) := fun x w => x.1 ⟨w, IsTotallyReal.isReal w⟩
  have hg : Continuous g := continuous_pi fun w => (continuous_apply _).comp continuous_fst
  have hC : IsCompact (closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  refine ⟨coord F ⁻¹' (g '' closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))), ?_, ?_⟩
  · rw [← coordHomeo_coe]
    exact (coordHomeo F).isCompact_preimage.2 (hC.image hg)
  · intro y hy
    exact ⟨infToMixed F y, subset_closure hy, rfl⟩

theorem measure_infDomain (li : Measure (Ainf F)) (hl : IsStdInf li) : li (infDomain F) = 1 := by
  have hfd := ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)
  have hmeas := (measurePreserving_toMixed F).measurable hfd
  have hpos : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))
  have hv : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
      one_mul, ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  calc li (infDomain F)
      = (li.map (coord F)) (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
        (Measure.map_apply (coord_measurable F) hmeas).symm
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [map_coord_eq F li hl, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [(measurePreserving_toMixed F).measure_preimage hfd.nullMeasurableSet]
    _ = 1 := by
        rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_mul_cancel₀ hpos.ne',
          ENNReal.ofReal_one]

end Domain

theorem exists_bounded_infDomain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧
      li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  intro F _ _ hTR li hl
  have := hTR
  obtain ⟨K₀, hK₀, hsub⟩ := exists_isCompact_superset_infDomain F
  exact ⟨infDomain F, K₀, measurableSet_infDomain F, hK₀, hsub, measure_infDomain F li hl,
    existsUnique_sub_mem_infDomain F⟩

end GlobalTheory.CompanionTheory.Equi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFundamentalDomainIntegersStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_fundamental_domain_integers : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧ li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  first | exact @GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | exact GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain | (intros; apply GlobalTheory.CompanionTheory.Equi.exists_bounded_infDomain <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCosetScaledRiemannSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi.LatSum

section Abstract

variable {A O Q ι : Type} [AddCommGroup A] [AddCommGroup O] [Fintype ι] [Fintype Q]

def reps (j : O →+ A) (rep : Q → O) : Finset (ι → A) :=
  Finset.univ.image fun (c : ι → Q) (i : ι) => j (rep (c i))

theorem card_reps (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) :
    (reps (ι := ι) j rep).card = Fintype.card Q ^ Fintype.card ι := by
  unfold reps
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fun]
  intro c c' h
  funext i
  have h1 : j (rep (c i)) = j (rep (c' i)) := congrFun h i
  have h2 := congrArg q (hj h1)
  rwa [hrep, hrep] at h2

theorem tile_pi (H : AddSubgroup O) (j : O →+ A) (hj : Function.Injective j) (q : O → Q) (rep : Q → O)
    (hrep : ∀ c, q (rep c) = c) (hq : ∀ a b, q a = q b ↔ a - b ∈ H) (D₀ : Set A)
    (hD : ∀ y : A, ∃! a : O, y - j a ∈ D₀) (y : ι → A) :
    ∃! p : (ι → A) × (ι → A), p.1 ∈ reps (ι := ι) j rep ∧
      p.2 ∈ AddSubgroup.pi Set.univ (fun _ : ι => H.map j) ∧
      y - p.1 - p.2 ∈ Set.pi Set.univ (fun _ : ι => D₀) := by
  choose a ha hau using fun i => hD (y i)
  refine ⟨(fun i => j (rep (q (a i))), fun i => j (a i - rep (q (a i)))), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.2 ⟨fun i => q (a i), Finset.mem_univ _, rfl⟩
  · intro i _
    refine AddSubgroup.mem_map.2 ⟨a i - rep (q (a i)), ?_, rfl⟩
    exact (hq _ _).1 (hrep _).symm
  · intro i _
    have : y i - j (rep (q (a i))) - j (a i - rep (q (a i))) = y i - j (a i) := by
      rw [map_sub]; abel
    simpa [this] using ha i
  · rintro ⟨p₁, p₂⟩ ⟨h1, h2, h3⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
    have hl : ∀ i, ∃ l ∈ H, j l = p₂ i := fun i => by
      obtain ⟨l, hl, e⟩ := AddSubgroup.mem_map.1 (h2 i (Set.mem_univ i))
      exact ⟨l, hl, e⟩
    choose l hlH hlj using hl
    have hai : ∀ i, rep (c i) + l i = a i := fun i => by
      refine hau i _ ?_
      have h4 := h3 i (Set.mem_univ i)
      have h5 : y i - j (rep (c i) + l i) = (y - (fun i => j (rep (c i))) - p₂) i := by
        simp only [Pi.sub_apply, map_add (f := _), hlj]; abel
      show y i - j (rep (c i) + l i) ∈ D₀
      rw [h5]; exact h4
    have hc : ∀ i, q (a i) = c i := fun i => by
      have h6 : q (a i) = q (rep (c i)) := (hq _ _).2 (by rw [← hai i]; simpa using hlH i)
      rwa [hrep] at h6
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show j (rep (c i)) = j (rep (q (a i)))
      rw [hc]
    · show p₂ i = j (a i - rep (q (a i)))
      rw [hc, ← hai i, add_sub_cancel_left, hlj]

end Abstract

def scal {R : Type} (ι : Type) [CommRing R] (t : R) : (ι → R) →+ (ι → R) where
  toFun y i := t * y i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [mul_add]

end GlobalTheory.CompanionTheory.Equi.LatSum


open GlobalTheory.CompanionTheory.Equi.LatSum in
theorem GlobalTheory.CompanionTheory.Equi.lat_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  intro F _ _ hF θ hθ li hli ι _ I hI x0 φ hφ hφs
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : li.IsAddHaarMeasure := hli.1
  obtain ⟨D₀, K₀, hDm, hK, hDK, hD1, htile⟩ := GlobalTheory.T.archimedean_fundamental_domain_integers F hF li hli
  have hg : Function.Injective (algebraMap F (Ainf F)) := (algebraMap F (Ainf F)).injective
  let j : 𝓞 F →+ Ainf F := ((algebraMap F (Ainf F)).comp (algebraMap (𝓞 F) F)).toAddMonoidHom
  have hj : Function.Injective j := hg.comp (IsFractionRing.injective (𝓞 F) F)
  let H : AddSubgroup (𝓞 F) := I.toAddSubgroup
  haveI hfin : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  let rep : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective
  have hrep : ∀ c, Ideal.Quotient.mk I (rep c) = c := Function.surjInv_eq _
  have hq : ∀ a b, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ a - b ∈ H := fun a b => Ideal.Quotient.eq
  let Λ : AddSubgroup (ι → Ainf F) := AddSubgroup.pi Set.univ (fun _ : ι => H.map j)
  haveI : Countable (𝓞 F) := (RingOfIntegers.basis F).equivFun.toEquiv.injective.countable
  haveI : Countable (H.map j) := by
    have : (↑(H.map j) : Set (Ainf F)).Countable := (Set.to_countable (H : Set (𝓞 F))).image j
    exact this.to_subtype
  haveI : Countable Λ := by
    refine Function.Injective.countable (f := fun (l : Λ) (i : ι) => (⟨l.1 i, l.2 i (Set.mem_univ i)⟩ : H.map j)) ?_
    intro l l' h
    exact Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i))
  have hcard : ((reps (ι := ι) j rep).card : ℝ) = (Ideal.absNorm I : ℝ) ^ Fintype.card ι := by
    rw [card_reps j hj (Ideal.Quotient.mk I) rep hrep, Nat.cast_pow, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let T : ℝ → (ι → Ainf F) →+ (ι → Ainf F) := fun ε => scal ι (θ ε)
  have hjoint : Continuous fun p : ℝ × (ι → Ainf F) => T p.1 p.2 :=
    continuous_pi fun i => (hθ.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have hθ0 : θ 0 = 0 := map_zero θ
  have key := GlobalTheory.T.lattice_point_count_scaling (ι → Ainf F) (Measure.pi fun _ => li) Λ (Set.pi Set.univ fun _ => D₀)
    (Set.pi Set.univ fun _ => K₀) (reps (ι := ι) j rep) T (Module.finrank ℚ F * Fintype.card ι)
    (MeasurableSet.univ_pi fun _ => hDm) (isCompact_univ_pi fun _ => hK)
    (Set.pi_mono fun _ _ => hDK)
    (by rw [Measure.pi_pi]; simp [hD1])
    (fun y => tile_pi H j hj (Ideal.Quotient.mk I) rep hrep hq D₀ htile y)
    (fun ε _ => continuous_pi fun i => continuous_const.mul (continuous_apply i))
    (fun ε hε y => by
      have h1 : θ ε⁻¹ * θ ε = 1 := by rw [← map_mul, inv_mul_cancel₀ hε.ne', map_one]
      have h2 : θ ε * θ ε⁻¹ = 1 := by rw [mul_comm, h1]
      constructor
      · funext i
        show θ ε⁻¹ * (θ ε * y i) = y i
        rw [← mul_assoc, h1, one_mul]
      · funext i
        show θ ε * (θ ε⁻¹ * y i) = y i
        rw [← mul_assoc, h2, one_mul])
    (fun ε hε => GlobalTheory.T.scaling_measure_product_archimedean F hF θ hθ li hli.1 ι ε hε)
    (fun B hB U hU => by
      have h0 : ∀ b ∈ B, ∀ᶠ z : ℝ × (ι → Ainf F) in 𝓝 ((0 : ℝ), b), T z.1 z.2 ∈ U := by
        intro b _
        refine hjoint.continuousAt.eventually_mem ?_
        have : T (0 : ℝ) b = 0 := by
          funext i
          show θ 0 * b i = 0
          rw [hθ0, zero_mul]
        simpa [this] using hU
      exact (hB.eventually_forall_of_forall_eventually h0).filter_mono nhdsWithin_le_nhds)
    (fun i => algebraMap F (Ainf F) (x0 i)) φ hφ hφs
  rw [hcard] at key

  let f : latCoset I x0 → Λ := fun x => ⟨fun i => algebraMap F (Ainf F) (x.1 i - x0 i), fun i _ => by
    obtain ⟨y, hy, e⟩ := x.2 i
    refine AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩
    show algebraMap F (Ainf F) (y : F) = algebraMap F (Ainf F) (x.1 i - x0 i)
    rw [e]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x x' h
      refine Subtype.ext (funext fun i => ?_)
      have h1 := hg (congrFun (congrArg Subtype.val h) i)
      exact sub_left_injective h1
    · rintro ⟨l, hl⟩
      have hy : ∀ i, ∃ y ∈ I, j y = l i := fun i => by
        obtain ⟨y, hy, e⟩ := AddSubgroup.mem_map.1 (hl i (Set.mem_univ i))
        exact ⟨y, hy, e⟩
      choose y hyI hyl using hy
      refine ⟨⟨fun i => x0 i + (y i : F), fun i => ⟨y i, hyI i, by simp⟩⟩, Subtype.ext (funext fun i => ?_)⟩
      show algebraMap F (Ainf F) (x0 i + (y i : F) - x0 i) = l i
      rw [add_sub_cancel_left, ← hyl]
      rfl
  let e : latCoset I x0 ≃ Λ := Equiv.ofBijective f hf
  have hterm : ∀ (ε : ℝ) (x : latCoset I x0), φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i)) =
      φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + (e x : ι → Ainf F))) := by
    intro ε x
    congr 1
    funext i
    show _ = θ ε * (algebraMap F (Ainf F) (x0 i) + algebraMap F (Ainf F) (x.1 i - x0 i))
    rw [← map_add (f := _), add_sub_cancel]
  constructor
  · intro ε hε
    have h1 := (e.summable_iff (f := fun l : Λ => φ (T ε ((fun i => algebraMap F (Ainf F) (x0 i)) + l)))).2 (key.1 ε hε)
    refine h1.congr fun x => ?_
    exact (hterm ε x).symm
  · refine key.2.congr fun ε => ?_
    congr 1
    rw [← e.tsum_eq]
    exact tsum_congr fun x => (hterm ε x).symm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCosetScaledRiemannSumStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_scaled_riemann_sum : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), IsStdInf li → ∀ (ι : Type) [Fintype ι] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun x : latCoset I x0 => φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) ∧ Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : latCoset I x0, φ (fun i => θ ε * algebraMap F (Ainf F) (x.1 i))) (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ * ∫ y, φ y ∂(Measure.pi fun _ => li))) := by
  first | exact @GlobalTheory.CompanionTheory.Equi.lat_sum | exact GlobalTheory.CompanionTheory.Equi.lat_sum | (intros; apply GlobalTheory.CompanionTheory.Equi.lat_sum <;> assumption)
end
