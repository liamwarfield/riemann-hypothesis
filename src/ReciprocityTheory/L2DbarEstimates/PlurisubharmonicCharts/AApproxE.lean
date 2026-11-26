module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxD
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem isOpen_ovl (j i : ι) : IsOpen (ovl A.chart j i) :=
  (A.chart j).isOpen_inter_preimage_symm (A.chart i).open_source

theorem trans_contDiffOn (j i : ι) :
    ContDiffOn ℂ ∞ ((A.chart i) ∘ (A.chart j).symm) (ovl A.chart j i) := by
  refine contDiffOn_piLp' 2 fun k => ?_
  have h : DifferentiableOn ℂ (fun x => ((A.chart i) ((A.chart j).symm x)) k) (ovl A.chart j i) :=
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn (A.holo_trans j i)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.isOpen_ovl j i) h

def chiC (i : ι) (β : V n → ℝ) (y : Y) : ℝ :=
  open Classical in if y ∈ (A.chart i).source then β (A.chart i y) else 0

theorem chiC_of_mem {i : ι} {β : V n → ℝ} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.chiC i β y = β (A.chart i y) := by simp [chiC, hy]

theorem chiC_eq_zero {i : ι} {β : V n → ℝ} {K0 : Set (V n)} (hβs : ∀ u, β u ≠ 0 → u ∈ K0)
    {y : Y} (hy : y ∉ (A.chart i).symm '' K0) : A.chiC i β y = 0 := by
  unfold chiC
  split_ifs with h
  · by_contra hne
    exact hy ⟨_, hβs _ hne, (A.chart i).left_inv h⟩
  · rfl

theorem isCompact_chartImage {i : ι} {K0 : Set (V n)} (hK0 : IsCompact K0)
    (hK0t : K0 ⊆ (A.chart i).target) : IsCompact ((A.chart i).symm '' K0) :=
  hK0.image_of_continuousOn ((A.chart i).continuousOn_symm.mono hK0t)

theorem chartImage_subset {i : ι} {K0 : Set (V n)} (hK0t : K0 ⊆ (A.chart i).target) :
    (A.chart i).symm '' K0 ⊆ (A.chart i).source := by
  rintro _ ⟨u, hu, rfl⟩; exact (A.chart i).map_target (hK0t hu)

theorem chiC_smooth {i : ι} {β : V n → ℝ} (hβ : ContDiff ℝ ∞ β) {K0 : Set (V n)}
    (hβs : ∀ u, β u ≠ 0 → u ∈ K0) (hK0 : IsCompact K0) (hK0t : K0 ⊆ (A.chart i).target) :
    A.SmoothFn (A.chiC i β) := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  by_cases hx : (A.chart j).symm v ∈ (A.chart i).source
  · refine ⟨ovl A.chart j i, A.isOpen_ovl j i, ⟨hv, hx⟩, ?_⟩
    refine (hβ.comp_contDiffOn (((A.trans_contDiffOn j i).restrict_scalars ℝ).mono
      Set.inter_subset_right)).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_of_mem hv'.2.2
  · have hKc := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hxK : (A.chart j).symm v ∉ (A.chart i).symm '' K0 :=
      fun h => hx (A.chartImage_subset hK0t h)
    refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ((A.chart i).symm '' K0)ᶜ,
      (A.chart j).isOpen_inter_preimage_symm hKc.isOpen_compl, ⟨hv, hxK⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : ℝ))).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_eq_zero hβs hv'.2.2

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

theorem leviV_smul_real {n : ℕ} (g : V n → ℂ) (u : V n) (r : ℝ) (ζ : V n) :
    leviV n g u (r • ζ).ofLp = ((r ^ 2 : ℝ) : ℂ) * leviV n g u ζ.ofLp := by
  unfold leviV
  simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private theorem contDiffOn_infty_wd_wdb {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) :
    ContDiffOn ℝ ∞ (wd n j g) U ∧ ContDiffOn ℝ ∞ (wdb n j g) U := by
  have hF : ∀ v : V n, ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) U := fun v =>
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2

theorem continuousOn_wd_wdb {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (j k : Fin n) : ContinuousOn (wd n j (wdb n k g)) U := ((contDiffOn_infty_wd_wdb hU (contDiffOn_infty_wd_wdb hU hg k).2 j).1).continuousOn

theorem levi_pos_compact {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) {K0 : Set (V n)} (hK0 : IsCompact K0) (hK0U : K0 ⊆ U)
    (hpos : ∀ u ∈ K0, ∀ ζ : V n, ζ ≠ 0 → 0 < (leviV n g u ζ.ofLp).re) :
    ∃ m > 0, ∀ u ∈ K0, ∀ ζ : V n, m * ‖ζ‖ ^ 2 ≤ (leviV n g u ζ.ofLp).re := by
  have hcont : ContinuousOn (fun q : V n × V n => (leviV n g q.1 q.2.ofLp).re)
      (K0 ×ˢ Metric.sphere (0 : V n) 1) := by
    unfold leviV
    refine Complex.continuous_re.comp_continuousOn ?_
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    have hfst : Set.MapsTo Prod.fst (K0 ×ˢ Metric.sphere (0 : V n) 1) U :=
      fun _ hq => hK0U hq.1
    refine (((continuousOn_wd_wdb hU hg j k).comp continuousOn_fst hfst).mul
      ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).continuous.comp continuous_snd).continuousOn).mul
      (Complex.continuous_conj.comp
        ((EuclideanSpace.proj k : V n →L[ℂ] ℂ).continuous.comp continuous_snd)).continuousOn
  by_cases hne : (K0 ×ˢ Metric.sphere (0 : V n) 1).Nonempty
  · obtain ⟨q0, hq0, hmin⟩ := (hK0.prod (isCompact_sphere 0 1)).exists_isMinOn hne hcont
    have hq0ne : q0.2 ≠ 0 := by
      intro h
      have := mem_sphere_zero_iff_norm.1 hq0.2
      rw [h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨(leviV n g q0.1 q0.2.ofLp).re, hpos _ hq0.1 _ hq0ne, fun u hu ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [leviV]
    · have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
      have h1 : (‖ζ‖⁻¹ : ℝ) • ζ ∈ Metric.sphere (0 : V n) 1 := by
        simp [norm_smul, hn.ne']
      have hmin' : (leviV n g q0.1 q0.2.ofLp).re ≤ (leviV n g u ((‖ζ‖⁻¹ : ℝ) • ζ).ofLp).re :=
        isMinOn_iff.1 hmin (u, (‖ζ‖⁻¹ : ℝ) • ζ) ⟨hu, h1⟩
      have hζ' : ζ = ‖ζ‖ • ((‖ζ‖⁻¹ : ℝ) • ζ) := by
        rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      conv_rhs => rw [hζ', leviV_smul_real, Complex.re_ofReal_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
  · refine ⟨1, one_pos, fun u hu ζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ
    · simp [leviV]
    · exfalso
      apply hne
      refine ⟨(u, (‖ζ‖⁻¹ : ℝ) • ζ), hu, ?_⟩
      simp [norm_smul, (norm_pos_iff.2 hζ).ne']

end

end ReciprocityTheory.L2DbarEstimates.Y
