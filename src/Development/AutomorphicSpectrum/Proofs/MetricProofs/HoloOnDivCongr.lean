module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamily

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_eval {σ : Type} (A : FinHolAtlas e X) {W : Set X} {b : X → σ → ℂ}
    (hb : ∀ q, A.HoloOn W fun y => b y q) (p : MvPolynomial σ ℤ) :
    A.HoloOn W fun y => eval (b y) (map (Int.castRingHom ℂ) p) := by
  intro j
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [Function.comp_def] using
      (analyticOnNhd_const (v := ((a : ℤ) : ℂ)) (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W))
  | add p q hp hq =>
    convert hp.add hq using 1
    funext u
    simp [Function.comp_def]
  | mul_X p q hp =>
    simpa [Function.comp_def] using hp.mul (hb q j)

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f) {y : X}
    (hy : y ∈ W) : ContinuousAt f y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hy⟩
  have h2 : ContinuousAt (f ∘ (A.chart j).symm) ((A.chart j) y) := (hf j _ h1).continuousAt
  have h3 : ContinuousAt (fun u => (f ∘ (A.chart j).symm) ((A.chart j) u)) y :=
    ContinuousAt.comp (f := A.chart j) h2 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
  simp only [Function.comp_apply, (A.chart j).left_inv hu]

theorem isOpen_inter_ne (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) : IsOpen (W ∩ {y | f y ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, h0⟩
  filter_upwards [hW.mem_nhds hy, (continuousAt_of_holoOn A hf hy).eventually_ne h0] with u h1 h2
  exact ⟨h1, h2⟩

theorem holoOn_div_congr (A : FinHolAtlas e X) {W : Set X} {f g v : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hg : A.HoloOn W g) (h0 : ∀ y ∈ W, g y ≠ 0) (hv : ∀ y ∈ W, v y = f y / g y) :
    A.HoloOn W v := by
  intro j
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  have h1 : AnalyticOnNhd ℂ (fun u => (f ∘ (A.chart j).symm) u / (g ∘ (A.chart j).symm) u)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) := fun u hu =>
    (hf j u hu).div (hg j u hu) (h0 _ hu.2)
  exact h1.congr hO fun u hu => (hv _ hu.2).symm

theorem holoOn_valAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (W : Set X)
    (b : X → (Σ k, ι k) → ℂ) (y₀ : X) (hW : IsOpen W) (hy₀ : y₀ ∈ W) (hb : ∀ q, A.HoloOn W fun y => b y q)
    (hpt : ∀ y ∈ W, b y ∈ mcPts (mCoordIdeal x)) (hs : RegAt x (mCoordIdeal (b y₀)) s) :
    ∃ W' : Set X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧ A.HoloOn W' fun y => valAt x s (b y) := by
  obtain ⟨d, g, h, hg, hh, hQ, heq⟩ := hs
  have hz : eval (b y₀) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    refine hQ (mem_mCoordIdeal_of_aeval_eq_zero (b y₀) hh ?_)
    rw [← h0]
    rw [aeval_def, eval_map, Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have hx : aeval x h ≠ 0 := fun h0 =>
    hz (eval_eq_zero_of_mem_mcPts (hpt y₀ hy₀) (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have Hg := holoOn_eval A hb g
  have Hh := holoOn_eval A hb h
  refine ⟨W ∩ {y | eval (b y) (map (Int.castRingHom ℂ) h) ≠ 0}, isOpen_inter_ne A hW Hh, ⟨hy₀, hz⟩,
    Set.inter_subset_left, ?_⟩
  refine holoOn_div_congr A (isOpen_inter_ne A hW Hh) (fun j => (Hg j).mono ?_) (fun j => (Hh j).mono ?_)
    (fun y hy => hy.2) fun y hy => ?_
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact valAt_eq (hpt y hy.1) ⟨d, g, h, hg, hh, hx, heq, hy.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

theorem exists_holoMap_inverse_of_degree_one : ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y)
    (h : Y → X), HoloMap B A h → IsDegreeOff A B h 1 ∅ →
    ∃ g : X → Y, (∀ y, g (h y) = y) ∧ (∀ x, h (g x) = x) ∧ HoloMap A B g := by
  intro e X Y _ _ _ _ _ A B h hh hd
  obtain ⟨-, -, -, -, hfib, hdet⟩ := hd
  have hex : ∀ x, ∃ y, h ⁻¹' {x} = {y} := fun x => Set.ncard_eq_one.1 (hfib x (by simp))
  have hinj : Function.Injective h := by
    intro a b hab
    obtain ⟨c, hc⟩ := hex (h a)
    have ha : a ∈ h ⁻¹' {h a} := rfl
    have hb : b ∈ h ⁻¹' {h a} := hab.symm
    rw [hc] at ha hb
    exact ha.trans hb.symm
  have hsurj : Function.Surjective h := by
    intro x
    obtain ⟨c, hc⟩ := hex x
    have hcx : c ∈ h ⁻¹' {x} := by rw [hc]; rfl
    exact ⟨c, hcx⟩
  let E : Y ≃ X := Equiv.ofBijective h ⟨hinj, hsurj⟩
  have hEc : Continuous E := hh.1
  obtain ⟨g, hgE⟩ : ∃ g : X → Y, g = E.symm := ⟨_, rfl⟩
  have hgc : Continuous g := by
    rw [hgE]; exact hEc.homeoOfEquivCompactToT2.symm.continuous
  have hgh : ∀ y, g (h y) = y := fun y => by rw [hgE]; exact E.symm_apply_apply y
  have hhg : ∀ x, h (g x) = x := fun x => by rw [hgE]; exact E.apply_symm_apply x
  refine ⟨g, hgh, hhg, hgc, fun j k w hw => ?_⟩
  obtain ⟨hwt, hws⟩ := hw
  have hys : g ((A.chart j).symm w) ∈ (B.chart k).source := hws
  obtain ⟨v, hv⟩ : ∃ v, v = B.chart k (g ((A.chart j).symm w)) := ⟨_, rfl⟩
  have hvt : v ∈ (B.chart k).target := hv ▸ (B.chart k).map_source hys
  have hsv : (B.chart k).symm v = g ((A.chart j).symm w) := by
    rw [hv]; exact (B.chart k).left_inv hys
  have hhv : h ((B.chart k).symm v) ∈ (A.chart j).source := by
    rw [hsv, hhg]; exact (A.chart j).map_target hwt
  obtain ⟨T, hT⟩ : ∃ T : (Fin e → ℂ) → Fin e → ℂ, T = A.chart j ∘ h ∘ (B.chart k).symm := ⟨_, rfl⟩
  have hTa : AnalyticAt ℂ T v := by
    rw [hT]; exact hh.2 k j v ⟨hvt, hhv⟩
  have hTv : T v = w := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [hsv, hhg]
    exact (A.chart j).right_inv hwt
  have hdet' : (fderiv ℂ T v).det ≠ 0 := by
    rw [hT]; exact hdet k j v hvt (by simp) hhv
  have hCe := ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero (fderiv ℂ T v) hdet'
  obtain ⟨Ce, hCedef⟩ : ∃ Ce, Ce = (fderiv ℂ T v).toContinuousLinearEquivOfDetNeZero hdet' := ⟨_, rfl⟩
  rw [← hCedef] at hCe
  have hstrict : HasStrictFDerivAt T (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) v := by
    rw [hCe]; exact hTa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph T with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = T := hstrict.toOpenPartialHomeomorph_coe
  have hus : v ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hsym : AnalyticAt ℂ F.symm w := by
    have h1 : AnalyticAt ℂ F.symm (F v) :=
      F.analyticAt_symm' (i := Ce) hus (by rw [hFc]; exact hTa) (by rw [hFc, hCe])
    rwa [hFc, hTv] at h1
  have hc2 : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hgc.continuousAt.comp ((A.chart j).continuousAt_symm hwt)
  have hc : ContinuousAt (B.chart k ∘ g ∘ (A.chart j).symm) w :=
    ContinuousAt.comp (g := B.chart k) ((B.chart k).continuousAt hys) hc2
  have hus' : F.source ∈ nhds ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    have : (B.chart k ∘ g ∘ (A.chart j).symm) w = v := hv.symm
    rw [this]; exact F.open_source.mem_nhds hus
  refine hsym.congr ?_
  filter_upwards [hc.preimage_mem_nhds hus',
    hc2.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hys),
    (A.chart j).open_target.mem_nhds hwt] with w' h1 h2 h3
  have h2' : g ((A.chart j).symm w') ∈ (B.chart k).source := h2
  have e1 : T ((B.chart k ∘ g ∘ (A.chart j).symm) w') = w' := by
    rw [hT]
    simp only [Function.comp_apply]
    rw [(B.chart k).left_inv h2', hhg]
    exact (A.chart j).right_inv h3
  have e2 := F.left_inv h1
  rw [hFc, e1] at e2
  exact e2

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphismStatement
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degree_one_biholomorphism : ∀ {e : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X), HoloMap B A h → IsDegreeOff A B h 1 ∅ → ∃ g : X → Y, (∀ y, g (h y) = y) ∧ (∀ x, h (g x) = x) ∧ HoloMap A B g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_holoMap_inverse_of_degree_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MCoordIdealCompLeImageZ
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal

theorem mCoordIdeal_comp_le_imageZ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K' → K) (v : (Σ k, ι' k) → Σ k, ι k) (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ), IsBlockMap κ v → mCoordIdeal (y ∘ v) ≤ imageZ v (mCoordIdeal y) := by
  intro K _ ι _ K' _ ι' _ κ v Φ _ y hv f hf
  have key : ∀ g : MRing ι', mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, hv.2.2.1 n]
  have hf' : mConeMap (y ∘ v) f = 0 := hf
  show mConeMap y (rename v f) = 0
  rw [key, hf', map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficients
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficients
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem tower_seq : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  intro Ψ _ _ N T II B u g c s q m hII hT1 hW hB hs hs0 hq hm
  obtain ⟨h1, -, h3, h4, h5⟩ := hT1 u g hW B hB c
  have hs' : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hs0, Eventually.of_forall fun n => hs n⟩
  have hδ : ((T.M B c).δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (T.M B c).δ_pos.ne'
  have hqn : ∀ n, (q n : ℝ) ≠ 0 := fun n => Nat.cast_ne_zero.2 (hq n).ne'
  have hgeo : ∀ n, geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) =
      (T.M B c).δ * (q n : ℝ) ^ dimFl Ψ N * T.mDeg B c u (s n) := by
    intro n
    have := geoFun_comb_mixed II hII Ψ N (T.M B c) (scale (s n)) (fun _ => T.lamS u (s n)) (fun _ => s n) (q n)
      (fun _ => m n) (fun _ j => hm n j)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  have har : ∀ n, II (T.M B c).K (T.M B c).ι (T.M B c).P (dimFl Ψ N + 1)
      (fun _ => combLine ((T.M B c).line (scale (s n))) (m n)) =
      (T.M B c).δ * (q n : ℝ) ^ (dimFl Ψ N + 1) * T.mbarTop II B c u (s n) := fun n =>
    top_comb_eq_arFun II hII Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)
  refine ⟨?_, ?_, ?_, h4⟩
  · filter_upwards [hs'.eventually h1] with n hn
    have a := (nefFib_integral_multiple Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n)).2 hn.1
    have b := RootFieldNumerics.root_model_line_semipositive Ψ N (T.M B c) (scale (s n)) (T.lamS u (s n)) (s n) (q n) (m n) (hm n) hn.2
    exact ⟨⟨_, le_rfl, b.1⟩, b.2, a⟩
  · refine ((h3.comp hs').const_mul ((T.M B c).δ : ℝ)).congr fun n => ?_
    rw [hgeo n]
    have := hqn n
    simp only [Function.comp]
    field_simp
  · refine (h5.comp hs').congr fun n => ?_
    unfold normHt
    rw [hgeo n, har n]
    have := hqn n
    simp only [Function.comp]
    by_cases h0 : T.mDeg B c u (s n) = 0
    · simp [h0]
    · have h2 : ((dimFl Ψ N : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficientsStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_threshold_limit_coefficients : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.tower_seq | exact GlobalTheory.CompanionTheory.Ar.Small.tower_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.tower_seq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentMulSelM
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot

variable {N : ℕ}

theorem mul_selM_apply {m : Type} (A : Matrix m (Fin N) ℂ) (S : Finset (Fin N)) (a : m) (b : Fin S.card) :
    (A * selM S) a b = A a (S.orderEmbOfFin rfl b) := by
  rw [Matrix.mul_apply]
  simp [selM, Matrix.of_apply]

theorem selM_conjTranspose_mul_mul (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    (selM S)ᴴ * A * selM S = A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl) := by
  ext a b
  rw [mul_selM_apply, Matrix.mul_apply]
  simp [selM, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite]

theorem det_selM (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((selM S)ᴴ * A * selM S).det = minorIJ A S S := by
  rw [selM_conjTranspose_mul_mul, minorIJ, dite_eq_left rfl]

theorem selM_transpose (S : Finset (Fin N)) (b : Fin S.card) :
    (selM S)ᵀ b = Pi.basisFun ℂ (Fin N) (S.orderEmbOfFin rfl b) := by
  ext a
  simp [selM, Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]

theorem linearIndependent_selM (S : Finset (Fin N)) : LinearIndependent ℂ (selM S)ᵀ := by
  have h := (Pi.basisFun ℂ (Fin N)).linearIndependent.comp _ (S.orderEmbOfFin rfl).injective
  have e : (selM S)ᵀ = (Pi.basisFun ℂ (Fin N)) ∘ (S.orderEmbOfFin rfl) := funext fun b => selM_transpose S b
  rw [e]
  exact h

theorem linearIndependent_mul_selM {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    LinearIndependent ℂ (h * selM S)ᵀ := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hi : Function.Injective h.mulVecLin := Matrix.mulVec_injective_of_isUnit hu
  have := (linearIndependent_selM S).map' h.mulVecLin (LinearMap.ker_eq_bot.2 hi)
  have e : (h * selM S)ᵀ = h.mulVecLin ∘ (selM S)ᵀ := by
    funext b
    ext a
    rfl
  rw [e]
  exact this

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (S : Finset (Fin N)) :
    0 < minorIJ G S S := by
  rw [minorIJ, dite_eq_left rfl]
  exact (hG.submatrix (S.orderEmbOfFin rfl).injective).det_pos

theorem log_re_mul {a b : ℂ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b).re = Real.log a.re + Real.log b.re := by
  have ha' := Complex.lt_def.1 ha
  have hb' := Complex.lt_def.1 hb
  have hi : a.im = 0 := ha'.2.symm
  rw [Complex.mul_re, hi, zero_mul, sub_zero]
  exact Real.log_mul ha'.1.ne' hb'.1.ne'

theorem gram_mul_selM (G h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((h * selM S)ᴴ * G * (h * selM S)).det = minorIJ (hᴴ * G * h) S S := by
  rw [← det_selM, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem blockPot_eq_gram (N j : ℕ) (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    (∀ S : Finset (Fin N), LinearIndependent ℂ (selM S)ᵀ) ∧
    (h.det ≠ 0 → ∀ S : Finset (Fin N), LinearIndependent ℂ (h * selM S)ᵀ) ∧
    (G.PosDef → blockPot j i G h = (1 / 2) * ((if j ≤ (i : ℕ) + 1 then Real.log ((selM (wIdx N j))ᴴ * G * selM (wIdx N j)).det.re else 0) + (if (i : ℕ) + 1 = N then Real.log ((selM (omIdx N j))ᴴ * G * selM (omIdx N j)).det.re else 0) + (if IsProperStep N j i then Real.log ((h * selM (stepCols N j i))ᴴ * G * (h * selM (stepCols N j i))).det.re else 0))) := by
  refine ⟨linearIndependent_selM, fun hd S => linearIndependent_mul_selM hd S, fun hG => ?_⟩
  simp only [det_selM, gram_mul_selM, blockPot, detFac]
  have hW := minor_pos hG (wIdx N j)
  have hO := minor_pos hG (omIdx N j)
  split_ifs <;>
    simp only [one_mul, mul_one, Complex.one_re, Real.log_one, log_re_mul hW hO] <;> ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.SncPull

theorem holoOn_comp_pr {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {U : Set Z} {g : Z → ℂ} (hg : Ab.HoloOn U g) : A.HoloOn (pr ⁻¹' U) (fun x => g (pr x)) := by
  intro j t ht
  obtain ⟨k, hk⟩ := Ab.cover (pr ((A.chart j).symm t))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((Ab.chart k).open_source.preimage hp.1)
  have htO : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source) :=
    ⟨ht.1, hk⟩
  have h1 : AnalyticAt ℂ (Ab.chart k ∘ pr ∘ (A.chart j).symm) t := hp.2 j k t htO
  have hmem : (Ab.chart k ∘ pr ∘ (A.chart j).symm) t ∈
      (Ab.chart k).target ∩ (Ab.chart k).symm ⁻¹' U := by
    refine ⟨(Ab.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (Ab.chart k).left_inv hk]
    exact ht.2
  have h2 : AnalyticAt ℂ (g ∘ (Ab.chart k).symm) ((Ab.chart k ∘ pr ∘ (A.chart j).symm) t) :=
    hg k _ hmem
  have h3 := AnalyticAt.comp (g := g ∘ (Ab.chart k).symm)
    (f := Ab.chart k ∘ pr ∘ (A.chart j).symm) h2 h1
  refine h3.congr ?_
  filter_upwards [hO.mem_nhds htO] with t' ht'
  simp [Function.comp, (Ab.chart k).left_inv ht'.2]

theorem isSection_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} (hs : IsSection Ab L s) :
    IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) :=
  ⟨fun x => holoOn_comp_pr hp (hs.1 (pr x)), fun x x' y hy => hs.2 (pr x) (pr x') (pr y) hy⟩

theorem isSNC_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} {nb : ℕ} {m : Fin nb → ℕ} {W : Fin nb → Set Z}
    (hsnc : IsSNC Ab L s m W)
    (hprod : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧
        ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) :
    IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) := by
  intro x
  obtain ⟨ψb, hcb, hxb, hsub, σb, hinj, hW, u, hu, hu0, hfac⟩ := hsnc (pr x)
  obtain ⟨ψ, kb, σ, hc, hx, hpr⟩ := hprod x
  obtain ⟨ψ', hc', hsrc, hco⟩ := GlobalTheory.T.compatible_chart_product_projection e n X Z A Ab pr ψ kb σ ψb hc hcb hpr
  have hsrc' : ∀ y ∈ ψ'.source, pr y ∈ ψb.source := fun y hy => by
    rw [hsrc] at hy; exact hy.2
  refine ⟨ψ', hc', by rw [hsrc]; exact ⟨hx, hxb⟩, fun y hy => hsub (hsrc' y hy),
    fun k => (σb k).map σ, ?_, ?_, fun y => u (pr y), ?_, fun y hy => hu0 _ (hsrc' y hy), ?_⟩
  · intro k k' i hk hk'
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain ⟨b, hb, hab⟩ := Option.map_eq_some_iff.1 hk'
    obtain rfl := σ.injective hab
    exact hinj k k' _ ha hb
  · intro k
    ext y
    constructor
    · rintro ⟨hyW, hy⟩
      have h1 : pr y ∈ W k ∩ ψb.source := ⟨hyW, hsrc' y hy⟩
      rw [hW k] at h1
      obtain ⟨-, i, hi, h0⟩ := h1
      exact ⟨hy, σ i, by simp [hi], by rw [hco y hy]; exact h0⟩
    · rintro ⟨hy, i, hi, h0⟩
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [hco y hy] at h0
      have h1 : pr y ∈ W k ∩ ψb.source := by
        rw [hW k]; exact ⟨hsrc' y hy, a, ha, h0⟩
      exact ⟨h1.1, hy⟩
  · exact fun j => (holoOn_comp_pr hp hu j).mono fun t ht => ⟨ht.1, hsrc' _ ht.2⟩
  · intro y hy
    show s (pr x) (pr y) = _
    rw [hfac _ (hsrc' y hy)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    cases h : σb k with
    | none => simp [h]
    | some i => simp [h, hco y hy]

theorem exists_adapted {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {nb : ℕ} {m : Fin nb → ℕ}
    {W : Fin nb → Set X} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m W) :
    ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  choose φ S μ v hc hx hball h0 hU hμ hv hv0 hfac using GlobalTheory.T.exists_snc_adapted_chart_at_point e X A L s nb m W hsnc
  have hb := fun x => GlobalTheory.T.snc_adapted_chart_section_form e X A L s hL hs x (φ x) (S x) (μ x) (v x) (hc x) (hball x) (hU x)
    (hμ x) (hv x) (hv0 x) (hfac x)
  choose hzero M hM using fun x => And.intro (hb x).1 (hb x).2
  have hopen : ∀ x, IsOpen ((φ x).source ∩ φ x ⁻¹' Metric.ball (0 : Fin e → ℂ) 1) := fun x =>
    (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen (fun x _ =>
    Set.mem_iUnion.2 ⟨x, hx x, by simp [h0 x]⟩)
  let E := t.equivFin
  have hcov : ∀ x, ∃ i : Fin t.card, x ∈ (φ (E.symm i).1).source ∧
      φ (E.symm i).1 x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    refine ⟨E ⟨p, hp⟩, ?_⟩
    simpa using hxp
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A (fun i : Fin t.card => φ (E.symm i).1)
    (fun i => hc _) (fun x => (hcov x).imp fun _ h => h.1)
  refine ⟨B, hAB, ?_, ?_, ∑ i : Fin t.card, |M (E.symm i).1|, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    rw [hi]; exact hball _
  · intro x
    obtain ⟨i, hi, hi'⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, by rw [hj]; exact hi, by rw [hj]; exact hi'⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    refine ⟨S (E.symm i).1, μ (E.symm i).1, hμ _, ?_, ?_⟩
    · rw [hi]; exact hzero _
    · rw [hi]
      intro y hy hy'
      exact ((hM _ y hy hy').trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun i : Fin t.card => |M (E.symm i).1|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem pullback_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  intro e n X Z _ _ _ _ _ _ A Ab Bb pr hp L s nb m W hL hs hsnc _ hprod
  have hL' := ReciprocityTheory.AnForm.M.isPotentialPullback Ab A pr hp L hL
  have hs' := isSection_pull hp hs
  have hn' := isSNC_pull hp hsnc hprod
  exact ⟨hL', hs', hn', exists_adapted A _ _ hL' hs' hn'⟩

end GlobalTheory.CompanionTheory.Ar.PB.SncPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjectionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_adapted_atlas_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | exact GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem epsT_small (C : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → |epsT C t| ≤ 1 / 2 ∧ C * epsT C t ≤ 1 := by
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := by
      first | exact tendsto_inv_nhdsGT_zero | exact tendsto_inv_zero_atTop
    exact (Real.tendsto_log_atTop.comp hinv).congr fun t => by simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he : Tendsto (fun t => epsT C t) (𝓝[>] 0) (𝓝 0) := by
    have h := (hq.comp hL).const_mul C
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp, epsT]
    ring
  have ha : ∀ᶠ t in 𝓝[>] (0:ℝ), |epsT C t| < 1 / 2 := by
    have h := he.abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), C * epsT C t < 1 := by
    have h := he.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨u, hu, hsub⟩ : ∃ u ∈ Set.Ioi (0:ℝ), Set.Ioc 0 u ⊆ {t | |epsT C t| < 1 / 2 ∧ C * epsT C t < 1} := by
    first | exact mem_nhdsGT_iff_exists_Ioc_subset.mp (ha.and hb) | exact mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.mp (ha.and hb)
  refine ⟨u, hu, fun t ht htu => ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨ht, htu⟩
  exact ⟨h1.le, h2.le⟩

private theorem contDiffAt_comp_chart_symm_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (hU : IsOpen U) (hf : A.SmoothOn U f) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  refine ((hf j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le ?_
  first | exact_mod_cast (le_top : ((2 : ℕ∞)) ≤ ⊤) | simp | decide

private theorem levi_add_mul {ι : Type} [Fintype ι] (F G : (ι → ℂ) → ℝ) (y w : ι → ℂ) (k : ℝ)
    (hF : ContDiffAt ℝ 2 F y) (hG : ContDiffAt ℝ 2 G y) :
    levi (fun z => F z + k * G z) y w = levi F y w + k * levi G y w := by
  have hF1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ F z :=
    (hF.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ G z :=
    (hG.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hD : (fderiv ℝ fun z => F z + k * G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + k • fderiv ℝ G z := by
    filter_upwards [hF1, hG1] with z hz1 hz2
    exact (hz1.hasFDerivAt.add (hz2.hasFDerivAt.const_mul k)).fderiv
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG2 : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ fun z => F z + k * G z) y =
      fderiv ℝ (fderiv ℝ F) y + k • fderiv ℝ (fderiv ℝ G) y := by
    rw [hD.fderiv_eq]
    exact (hF2.hasFDerivAt.add (hG2.hasFDerivAt.const_smul k)).fderiv
  unfold levi
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_split {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ th : LocPot X)
    (u : X → ℝ) (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (x : X)
    (j : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target)
    (h1 : (A.chart j).symm y ∈ th.U x) (h2 : (A.chart j).symm y ∈ Θ.U x) (w : Fin e → ℂ) :
    levi (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
        c * Θ.φ x ((A.chart j).symm z)) y w =
      levi ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y w +
        (c - ε) * levi (Θ.φ x ∘ (A.chart j).symm) y w := by
  have hthC := contDiffAt_comp_chart_symm_of_smoothOn A (th.U x) (th.φ x) (th.isOpen_U x) (hth.1 x) j y hy h1
  have hΘC := contDiffAt_comp_chart_symm_of_smoothOn A (Θ.U x) (Θ.φ x) (Θ.isOpen_U x) (hΘ.1 x) j y hy h2
  have huC := contDiffAt_comp_chart_symm_of_smoothOn A Set.univ u isOpen_univ hu j y hy trivial
  have hPC : ContDiffAt ℝ 2 ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hthC.add huC).add (contDiffAt_const.mul hΘC)
  rw [← levi_add_mul _ _ y w (c - ε) hPC hΘC]
  congr 1
  funext z
  show _ = th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) + ε * Θ.φ x ((A.chart j).symm z) +
    (c - ε) * Θ.φ x ((A.chart j).symm z)
  ring

private theorem levi_sub_const' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (a : ℝ) (y w : ι → ℂ) :
    levi (fun z => g z - a) y w = levi g y w := by
  have h : fderiv ℝ (fun z => g z - a) = fderiv ℝ g := by
    funext z
    by_cases hg : DifferentiableAt ℝ g z
    · exact (hg.hasFDerivAt.sub_const a).fderiv
    · have hg' : ¬ DifferentiableAt ℝ (fun z => g z - a) z := fun h => hg (by simpa using h.add_const a)
      rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
  unfold levi
  rw [h]

private theorem levi_zero' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (y : ι → ℂ) : levi g y 0 = 0 := by
  unfold levi
  simp

theorem isPsh_of_le {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c a : ℝ) (hεc : ε ≤ c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z - a) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => (th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) - a := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_sub_const' (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) a y w,
    levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  rcases eq_or_ne w 0 with rfl | hw
  · simp [levi_zero']
  · have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
    have hce : 0 ≤ c - ε := sub_nonneg.mpr hεc
    nlinarith

theorem isPosPot_of_lt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (hεc : ε < c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z) : IsPosPot A Q := by
  intro x j y hy w hw
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z) := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
  have hce : 0 < c - ε := sub_pos.mpr hεc
  nlinarith

private theorem isPotential_add' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) : IsPotential A (P + Q) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · show ContDiffOn ℝ _ (fun z => P.φ x ((A.chart j).symm z) + Q.φ x ((A.chart j).symm z))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x))
    exact ((hP.1 x j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) =>
      ⟨hz.1, hz.2.1⟩).add ((hQ.1 x j).mono fun z
        (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) => ⟨hz.1, hz.2.2⟩)
  · obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hd1⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hd2⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W1 ∩ W2, hW1o.inter hW2o, ⟨hyW1, hyW2⟩, fun z => G1 z + G2 z, fun j => ?_, fun z hz => ?_⟩
    · exact ((hG1 j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) =>
        ⟨hz.1, hz.2.1⟩).add ((hG2 j).mono fun z
          (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) => ⟨hz.1, hz.2.2⟩)
    · obtain ⟨⟨⟨hz1, hz2⟩, hzPx, hzQx⟩, hzPx', hzQx'⟩ := hz
      have e1 := hd1 z ⟨⟨hz1, hzPx⟩, hzPx'⟩
      have e2 := hd2 z ⟨⟨hz2, hzQx⟩, hzQx'⟩
      show P.φ x z + Q.φ x z - (P.φ x' z + Q.φ x' z) = (G1 z + G2 z).re
      rw [Complex.add_re, ← e1, ← e2]
      ring

theorem fixedMember_base : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → ∃ t₂ : ℝ, 0 < t₂ ∧ t₂ ≤ t₀ ∧ ∀ t₁, 0 < t₁ → t₁ ≤ t₂ → IsPotential A (th + LocPot.ofFun (phT t₁) + Θ) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + Θ.rsmul (-(1 / 2))) ∧ IsPosPot A (th + LocPot.ofFun (phT t₁) + Θ) ∧ ∀ t, 0 < t → t ≤ t₁ → A.Smooth (fun y => phT t y - phT t₁ y - C * epsT C t₁) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + LocPot.ofFun (fun y => phT t y - phT t₁ y - C * epsT C t₁)) ∧ (∀ y, phT t y - phT t₁ y - C * epsT C t₁ ≤ 0) ∧ ∀ y ∉ bdry s, -(|C₅| + |C| + 1) * Real.log (rW L s y) ≤ phT t y - phT t₁ y - C * epsT C t₁ := by
  intro e X _ A Θ L s th ph phT C₅ C t₀ hΘ hpos hlog hSW hRF
  obtain ⟨a, ha, hab⟩ := epsT_small C
  obtain ⟨ht0, -, hR⟩ := hRF
  obtain ⟨hthP, -, -, hSW4⟩ := hSW
  refine ⟨min t₀ a, lt_min ht0 ha, min_le_left _ _, fun t₁ ht₁ ht₁2 => ?_⟩
  have ht₁0 : t₁ ≤ t₀ := ht₁2.trans (min_le_left _ _)
  have ht₁a : t₁ ≤ a := ht₁2.trans (min_le_right _ _)
  obtain ⟨hsm1, hC1, -, -, hpsh1, -, -, -⟩ := hR t₁ ht₁ ht₁0
  obtain ⟨he1, he1'⟩ := hab t₁ ht₁ ht₁a
  have hepsle : epsT C t₁ ≤ 1 / 2 := (le_abs_self _).trans he1
  refine ⟨isPotential_add' A _ _ (isPotential_add' A _ _ hthP (isPotential_ofFun A _ hsm1)) hΘ,
    ?_, ?_, fun t ht htt₁ => ?_⟩
  · exact isPsh_of_le A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) (1 / 2) 0 hepsle hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Θ.U x) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + -(1 / 2) * Θ.φ x z = th.φ x z + phT t₁ z + 1 / 2 * Θ.φ x z - 0
        ring)
  · exact isPosPot_of_lt A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) 1 (by linarith) hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x) => ⟨hz.1.1, hz.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z = th.φ x z + phT t₁ z + 1 * Θ.φ x z
        ring)
  have htt0 : t ≤ t₀ := htt₁.trans ht₁0
  obtain ⟨hsm, -, hph, -, hpsh, -, -, hmono⟩ := hR t ht htt0
  obtain ⟨he, -⟩ := hab t ht (htt₁.trans ht₁a)
  have hepsle' : epsT C t ≤ 1 := by linarith [le_abs_self (epsT C t)]
  refine ⟨fun j => ((hsm j).sub (hsm1 j)).sub contDiffOn_const, ?_, fun y => ?_, fun y hy => ?_⟩
  · exact isPsh_of_le A Θ th (phT t) hΘ hpos hthP hsm (epsT C t) 1 (C * epsT C t₁) hepsle' hpsh _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Set.univ) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + (phT t z - phT t₁ z - C * epsT C t₁) =
          th.φ x z + phT t z + 1 * Θ.φ x z - C * epsT C t₁
        ring)
  · have h := hmono t₁ htt₁ ht₁0 y
    linarith
  · have h1 := hph y hy
    have h2 := (hSW4 y hy).1
    have h3 := hC1 y
    have hr : Real.exp 1 ≤ rW L s y := by
      have := hlog y
      unfold rW
      linarith
    have hL : 1 ≤ Real.log (rW L s y) := by
      have h := Real.log_le_log (Real.exp_pos 1) hr
      rwa [Real.log_exp] at h
    have k1 : 0 ≤ (|C₅| - C₅) * Real.log (rW L s y) :=
      mul_nonneg (sub_nonneg.mpr (le_abs_self C₅)) (by linarith)
    have k2 : 0 ≤ (|C| + 1) * (Real.log (rW L s y) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hL)
    have k3 := le_abs_self C
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapTorusInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapTorusInvariant
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem stepGap_torus : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) →
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → stepGap M BM p (fun q => c q.1 * z q) = stepGap M BM p z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p z c hc hz
  have hpos : 0 < ∏ k, ‖c k‖ ^ M.dy p k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have h1 := (BM.hom p).smul c z hc
  rw [BM.hom_deg p] at h1
  have h2 : (fsHerm ι (M.dy p)).h (fun q => c q.1 * z q) =
      (∏ k, ‖c k‖ ^ M.dy p k) * (fsHerm ι (M.dy p)).h z := (fsHerm ι (M.dy p)).smul c z hc
  unfold stepGap
  rw [h1, h2, Real.log_mul hpos.ne' ((BM.hom p).pos z hz).ne',
    Real.log_mul hpos.ne' ((fsHerm ι (M.dy p)).pos z hz).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapTorusInvariantStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_torus_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (c : K → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → stepGap M BM p (fun q => c q.1 * z q) = stepGap M BM p z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_torus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCompactRWSublevel
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem continuous_normSec {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L) (hS : IsSection A L s) :
    Continuous (fun y => ‖s y y‖ * Real.exp (-L.φ y y)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc := LeviFormBoundaryTopology.continuousAt_of_holoOn A (hS.1 x) (L.mem_U x)
  have hφ := LeviFormBoundaryTopology.continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (L.mem_U x)
  have hF : ContinuousAt (fun z => ‖s x z‖ * Real.exp (-L.φ x z)) x :=
    hc.norm.mul (Real.continuous_exp.continuousAt.comp hφ.neg)
  refine hF.congr ?_
  filter_upwards [(L.isOpen_U x).mem_nhds (L.mem_U x)] with z hz
  exact hS.2 x z z ⟨hz, L.mem_U z⟩

theorem isCompact_rW_sublevel : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ R : ℝ, IsCompact {y | y ∉ bdry s ∧ rW L s y ≤ R} := by
  intro e X _ _ _ A L s hL hS R
  have hset : {y | y ∉ bdry s ∧ rW L s y ≤ R} =
      {y | Real.exp ((Real.exp 1 - R) / 2) ≤ ‖s y y‖ * Real.exp (-L.φ y y)} := by
    ext y
    simp only [Set.mem_setOf_eq, bdry, rW, logNormSec]
    constructor
    · rintro ⟨h0, h1⟩
      have hpos : 0 < ‖s y y‖ * Real.exp (-L.φ y y) :=
        mul_pos (norm_pos_iff.2 h0) (Real.exp_pos _)
      exact (Real.le_log_iff_exp_le hpos).1 (by linarith)
    · intro h
      have hpos : 0 < ‖s y y‖ * Real.exp (-L.φ y y) := lt_of_lt_of_le (Real.exp_pos _) h
      have h0 : s y y ≠ 0 := by
        intro h0
        simp [h0] at hpos
      have h1 := (Real.le_log_iff_exp_le hpos).2 h
      exact ⟨h0, by linarith⟩
  rw [hset]
  exact (isClosed_le continuous_const (continuous_normSec A L s hL hS)).isCompact

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamilyStatement
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_index_of_orthogonal_family : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r : ℕ) (v : Fin r → V), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → ∀ s, logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L = -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) + Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | exact GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.torusPartDegree <;> assumption)
end
