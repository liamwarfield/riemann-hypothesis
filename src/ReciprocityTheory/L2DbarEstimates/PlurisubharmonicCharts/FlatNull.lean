module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNullB
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcC
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxE

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNull
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem dense_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) :
    Dense (A.Mset w0 s De) :=
  fn_dense A hD hF

theorem mu_compl_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hN : EXTNullStatement n) (hD : A.D0 L w w0 s)
    (hF : A.Flat w0 s De) : A.mu (A.Mset w0 s De)ᶜ = 0 :=
  fn_mu_compl A hN hD hF

theorem ext_Mset {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hE : EXTStatement n) (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (la : La) (F : ι → Y → ℂ) (hFs : A.IsSecOn la (A.Mset w0 s De) F)
    (hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ A.Mset w0 s De, ENNReal.ofReal (A.nsq la F x) ∂A.mu < ⊤) :
    ∃ G : ι → Y → ℂ, A.IsSec la G ∧
      ∀ i y, y ∈ A.Mset w0 s De → y ∈ (A.chart i).source → G i y = F i y :=
  fn_ext A hE hD hF la F hFs hloc

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalc
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

def jz {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (i : ι)
    (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (A.zLoc w0 s i) (A.chart i y)

theorem holo_flat_iff {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (u : Y → ℂ) :
    Holo n (flatStein A hD hF).z (fun y : A.Mset w0 s De => u y) ↔
      ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm)
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) := by
  constructor
  · intro hH i v hv
    set m : A.Mset w0 s De := ⟨(A.chart i).symm v, hv.2⟩
    have hmi : (m : Y) ∈ (A.chart i).source := (A.chart i).map_target hv.1
    have hcm : A.chart i m = v := (A.chart i).right_inv hv.1
    obtain ⟨e, he, hme⟩ := exists_chart n (flatStein A hD hF).z
      (flatStein A hD hF).isLocalHomeomorph m
    have hfw := fc_chart_fwd A hD e he m hme i hmi
    rw [hcm] at hfw
    have hZ := fc_zLoc_chart A hD e he m hme i hmi
    rw [hcm] at hZ
    have hd1 : DifferentiableAt ℂ ((fun y : A.Mset w0 s De => u y) ∘ e.symm)
        (A.zLoc w0 s i v) := by
      rw [hZ]
      exact (hH e he).differentiableAt (e.open_target.mem_nhds (e.map_source hme))
    have hd2 : DifferentiableAt ℂ (A.zLoc w0 s i) v :=
      ((fc_zLoc_contDiffOn A hD i).differentiableOn (by simp)).differentiableAt
        ((fc_isOpen_O A hD i).mem_nhds hv)
    refine ((hd1.comp v hd2).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hfw] with v' hv'
    simp only [Function.comp_apply]
    rw [hv']
  · intro hd e he w hw
    have hme : e.symm w ∈ e.source := e.map_target hw
    have hem : e (e.symm w) = w := e.right_inv hw
    have hmi : ((e.symm w : A.Mset w0 s De) : Y) ∈ (A.chart (A.pick (e.symm w : Y))).source :=
      A.mem_pick _
    obtain ⟨G, hG, hGx, hGe⟩ := fc_chart_inv A hD hF e he _ hme _ hmi
    rw [hem] at hG hGx hGe
    have hd1 : DifferentiableAt ℂ (u ∘ (A.chart (A.pick (e.symm w : Y))).symm) (G w) := by
      rw [hGx]
      exact (hd _).differentiableAt ((fc_isOpen_O A hD _).mem_nhds (fc_mem_O A _ _ hmi))
    refine ((hd1.comp w (hG.differentiableAt (by simp))).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hGe] with w' hw'
    simp only [Function.comp_apply]
    rw [hw']

theorem lintegral_flat {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (φ : Y → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y in A.Mset w0 s De, φ y ∂A.mu =
      ∫⁻ x : A.Mset w0 s De, φ x * ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick x) x) /
        ‖(jz A w0 s (A.pick x) x).det‖ ^ 2) ∂vol n (flatStein A hD hF).z := by
  have hMm : MeasurableSet (A.Mset w0 s De) := (isOpen_Mset A hD).measurableSet
  have hz := (flatStein A hD hF).isLocalHomeomorph
  have hρ : Measurable fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) :=
    ENNReal.measurable_ofReal.comp (fc_rho_continuous A hD hF).measurable
  have hmeas : A.mu.comap Subtype.val =
      (vol n (flatStein A hD hF).z).withDensity fun m => ENNReal.ofReal ((fun x : A.Mset w0 s De => Real.exp (A.ph A.kap (A.pick x) x) / ‖(fderiv ℂ (A.zLoc w0 s (A.pick x)) (A.chart (A.pick x) x)).det‖ ^ 2) m) := by
    choose e he hxe using fun x : A.Mset w0 s De => exists_chart n _ hz x
    let U : A.Mset w0 s De → Set (A.Mset w0 s De) := fun x =>
      (e x).source ∩ Subtype.val ⁻¹' (A.chart (A.pick x)).source
    have hUo : ∀ x, IsOpen (U x) := fun x =>
      (e x).open_source.inter ((A.chart _).open_source.preimage continuous_subtype_val)
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
    have huniv : ⋃ t : T, U t = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      have hx : x ∈ ⋃ i ∈ T, U i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxe x, A.mem_pick _⟩
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
    haveI := hTc.to_subtype
    refine Measure.ext_of_iUnion_eq_univ huniv fun t => ?_
    ext B hB
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
      withDensity_apply _ (hB.inter (hUo t).measurableSet)]
    exact fc_mu_piece A hD hF (e t) (he t) (A.pick (t : Y)) (B ∩ U t)
      (hB.inter (hUo t).measurableSet) (fun m hm => hm.2.1) (fun m hm => hm.2.2)
  rw [← lintegral_subtype_comap hMm, hmeas]
  exact (lintegral_withDensity_eq_lintegral_mul _ hρ (hφ.comp measurable_subtype_coe)).trans
    (lintegral_congr fun x => mul_comm _ _)

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem mem_ovl {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) :
    A.chart j y ∈ ovl A.chart j i :=
  ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hi]⟩

theorem trans_contDiffAt {j i : ι} {y : Y} (hj : y ∈ (A.chart j).source)
    (hi : y ∈ (A.chart i).source) :
    ContDiffAt ℂ 2 ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) :=
  ((A.trans_contDiffOn j i).contDiffAt ((A.isOpen_ovl j i).mem_nhds (A.mem_ovl hj hi))).of_le
    (by norm_cast)

theorem levi_transfer (la : La) (f : Y → ℝ) (hf : A.SmoothFn f) (j i : ι) {y : Y}
    (hj : y ∈ (A.chart j).source) (hi : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt j (fun x => A.ph la j x + f x) y ξ =
      A.leviAt i (fun x => A.ph la i x + f x) y
        (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j y) (WithLp.toLp 2 ξ)).ofLp := by
  set Φ := (A.chart i) ∘ (A.chart j).symm
  set v0 := (A.chart j) y
  have hv0 := A.mem_ovl hj hi
  have hO : ovl A.chart j i ∈ 𝓝 v0 := (A.isOpen_ovl j i).mem_nhds hv0
  have hΦ : ContDiffAt ℂ 2 Φ v0 := A.trans_contDiffAt hj hi
  have hΦv : Φ v0 = (A.chart i) y := by simp [Φ, v0, (A.chart j).left_inv hj]
  set h : V n → ℝ := fun u => A.ph la i ((A.chart i).symm u) + f ((A.chart i).symm u)
  have hh : ContDiffAt ℝ 2 h (Φ v0) := by
    rw [hΦv]
    exact (((A.smooth_ph la i).add (hf i)).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))).of_le (by norm_cast)
  set G := A.g la j i ∘ (A.chart j).symm
  have hG : ContDiffAt ℂ 2 G v0 :=
    contDiffAt_two_of_holo (A.isOpen_ovl j i) (A.holo_g la j i) hv0
  have hG0 : G v0 ≠ 0 := by
    simp only [G, Function.comp, v0, (A.chart j).left_inv hj]; exact A.g_ne la j i y hj hi
  set u2 : Fin 2 → V n → ℝ := ![fun v => h (Φ v), fun v => Real.log (Complex.normSq (G v))]
  have hu2 : ∀ k, ContDiffAt ℝ 2 (u2 k) v0 := by
    intro k; fin_cases k
    · exact hh.comp v0 (hΦ.restrict_scalars ℝ)
    · exact (contDiffAt_normSq_comp hG).log (Complex.normSq_pos.2 hG0).ne'
  have hev : (fun v => ((A.ph la j ((A.chart j).symm v) + f ((A.chart j).symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((∑ k, u2 k v : ℝ) : ℂ) := by
    filter_upwards [hO] with v hv
    have hxj : (A.chart j).symm v ∈ (A.chart j).source := (A.chart j).map_target hv.1
    have hxi : (A.chart j).symm v ∈ (A.chart i).source := hv.2
    have hsy : (A.chart i).symm (Φ v) = (A.chart j).symm v := by
      simp only [Φ, Function.comp]; exact (A.chart i).left_inv hxi
    have hne : ‖A.g la j i ((A.chart j).symm v)‖ ≠ 0 := norm_ne_zero_iff.2 (A.g_ne la j i _ hxj hxi)
    simp only [Fin.sum_univ_two, u2, Matrix.cons_val_zero, Matrix.cons_val_one, h, hsy, G,
      Function.comp, A.ph_trans la j i _ hxj hxi, Complex.normSq_eq_norm_sq]
    push_cast; ring
  unfold leviAt
  rw [leviV_congr hev, leviV_ofReal_sum hu2, Fin.sum_univ_two]
  have e1 : u2 0 = fun v => h (Φ v) := rfl
  have e2 : u2 1 = fun v => Real.log (Complex.normSq (G v)) := rfl
  rw [e1, e2, leviV_log_normSq hG hG0, add_zero]
  have hc := leviV_comp (f := fun u => ((h u : ℝ) : ℂ)) (Φ := Φ) (y := v0) ?_ hΦ ξ
  · rw [show (fun v => ((h (Φ v) : ℝ) : ℂ)) = (fun u => ((h u : ℝ) : ℂ)) ∘ Φ from rfl, hc, hΦv]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hh

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end
