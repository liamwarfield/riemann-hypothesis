module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
open MeasureTheory
open scoped BigOperators

namespace GlobalTheory.LatticeMean

theorem exists_strict_domain (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    Countable Λ ∧ ∃ F : Set ℂ, MeasurableSet F ∧ ∀ x : ℂ, ∃! g : Λ, (g : ℂ) + x ∈ F := by
  obtain ⟨w₁, w₂, hli, hΛ⟩ := h
  let b : Module.Basis (Fin 2) ℝ ℂ :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : Set.range b = {w₁, w₂} := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    ext x
    simp [or_comm]
  have hΛ' : Λ = (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    rw [hΛ, hb, Submodule.span_int_eq_addSubgroupClosure]
  subst hΛ'
  refine ⟨?_, ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  · exact inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  · exact ZSpan.exist_unique_vadd_mem_fundamentalDomain b x

theorem setAverage_eq_of_domain {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (A : AddSubgroup V) [Countable A] (f : V → ℝ)
    (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z) (P : Set V) (hP : IsAddFundamentalDomain A P μ) :
    ⨍ z in Classical.epsilon (fun Fd : Set V => IsAddFundamentalDomain A Fd μ), f z ∂μ
      = ⨍ z in P, f z ∂μ := by
  have hE := Classical.epsilon_spec (p := fun Fd : Set V => IsAddFundamentalDomain A Fd μ) ⟨P, hP⟩
  rw [setAverage_eq, setAverage_eq, hE.setIntegral_eq hP (fun g x => hf g g.2 x),
    measureReal_def, measureReal_def, hE.measure_eq hP]

theorem setAverage_pi (r : ℕ) (F : Set ℂ) (f : ℂ → ℝ) :
    ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) = (⨍ z in F, f z) ^ r := by
  rw [setAverage_eq, setAverage_eq, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow, measureReal_def, Measure.pi_pi]
  simp [measureReal_def, mul_pow]

theorem mean_prod_eq_pow : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → ∀ (f : ℂ → ℝ), (∀ ω ∈ Λ, ∀ z, f (ω + z) = f z) → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (r : ℕ) (e : V ≃ₗ[ℝ] (Fin r → ℂ)) (A : AddSubgroup V), (∀ x, x ∈ A ↔ ∀ k, e x k ∈ Λ) → ⨍ z in Classical.epsilon (fun Fd : Set V => MeasureTheory.IsAddFundamentalDomain A Fd μ), ∏ k, f (e z k) ∂μ = (⨍ z in Classical.epsilon (fun Fd : Set ℂ => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume), f z) ^ r := by
  intro Λ hΛ f hf V _ _ _ _ _ μ _ r e A hA
  obtain ⟨hc, F, hFm, hF⟩ := exists_strict_domain Λ hΛ
  let ec : V ≃L[ℝ] (Fin r → ℂ) := e.toContinuousLinearEquiv
  let em : V ≃ᵐ (Fin r → ℂ) := ec.toHomeomorph.toMeasurableEquiv
  have hem : ∀ x, em x = e x := fun _ => rfl
  have hAc : Countable A := by
    refine Function.Injective.countable
      (f := fun (a : A) (k : Fin r) => (⟨e a k, (hA a).1 a.2 k⟩ : Λ)) ?_
    intro a b hab
    apply Subtype.ext
    apply e.injective
    funext k
    exact congrArg Subtype.val (congrFun hab k)
  have hQm : MeasurableSet (Set.univ.pi (fun _ : Fin r => F)) :=
    MeasurableSet.univ_pi fun _ => hFm
  have hP : IsAddFundamentalDomain A (em ⁻¹' Set.univ.pi (fun _ : Fin r => F)) μ := by
    refine IsAddFundamentalDomain.mk' (em.measurable hQm).nullMeasurableSet fun x => ?_
    choose g hg hu using fun k => hF (e x k)
    refine ⟨⟨e.symm fun k => (g k : ℂ), (hA _).2 fun k => by simp⟩, ?_, ?_⟩
    · intro k _
      show e (e.symm (fun k => (g k : ℂ)) + x) k ∈ F
      simpa using hg k
    · intro a ha
      apply Subtype.ext
      apply e.injective
      funext k
      have h1 : e ((a : V) + x) k ∈ F := ha k (Set.mem_univ k)
      have h2 := hu k ⟨e a k, (hA a).1 a.2 k⟩ (by simpa using h1)
      simpa using congrArg Subtype.val h2
  have hF' : IsAddFundamentalDomain Λ F volume :=
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
  rw [setAverage_eq_of_domain μ A (fun z => ∏ k, f (e z k)) ?_ _ hP,
    setAverage_eq_of_domain volume Λ f hf F hF', ← setAverage_pi]
  swap
  · intro a ha z
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_add (f := _), Pi.add_apply, hf _ ((hA a).1 ha k)]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) (volume : Measure (Fin r → ℂ))
  have hc0 : Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' Set.univ.pi (fun _ : Fin r => F), ∏ k, f (e z k) ∂μ
      = ⨍ z in Set.univ.pi (fun _ : Fin r => F), ∏ k, f (z k) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    rfl
  rw [h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) (volume : Measure (Fin r → ℂ)) : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

end GlobalTheory.LatticeMean
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateChartBallDistortion
open MeasureTheory Filter Topology Metric Set

namespace GlobalTheory

theorem translate_chart_ball_distortion
    (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (e : V → G)
    (m : G → M) (ι : V →ₗᵢ[ℝ] M) (L : G → M →L[ℝ] M) (he : Continuous e) (he0 : e 0 = 1)
    (hd : HasStrictFDerivAt (fun x => m (e x)) ι.toContinuousLinearMap 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h))
    (hopen : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) (κ : ℝ) (hκ : 1 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ ball (0 : V) δ, ∀ r ∈ Ioo (0 : ℝ) δ,
      (fun g => e x * g) '' (e '' ball 0 r) ⊆ e '' ball x (κ * r) ∧
      e '' ball x r ⊆ (fun g => e x * g) '' (e '' ball 0 (κ * r)) := by
  set ε : ℝ := (κ - 1) / (2 * (3 + 2 * κ)) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]
    linarith
  have hκε : (1 + ε) ^ 2 < κ * (1 - ε) ^ 2 := by
    have h3 : ε * (3 + 2 * κ) = (κ - 1) / 2 := by
      rw [hε]
      field_simp
    nlinarith [mul_pos (sub_pos.mpr hκ) (mul_pos hε0 hε0)]
  obtain ⟨η, hη0, hη⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)
  have hD : ∀ a b : V, ‖a‖ < η → ‖b‖ < η →
      ‖m (e a) - m (e b) - ι (a - b)‖ ≤ ε * ‖a - b‖ := by
    intro a b ha hb
    have h := @hη (a, b) (by
      simp only [Prod.dist_eq, dist_zero_right]
      exact max_lt ha hb)
    simpa using h
  have hLc : ContinuousAt (fun x => L (e x)) 0 := hL.comp_of_eq he.continuousAt he0
  obtain ⟨η2, hη20, hη2⟩ := Metric.continuousAt_iff.mp hLc ε hε0
  have hLx : ∀ x : V, ‖x‖ < η2 → ∀ v : M, ‖L (e x) v - v‖ ≤ ε * ‖v‖ := by
    intro x hx v
    have h1 := hη2 (by rwa [dist_zero_right] : dist x 0 < η2)
    simp only [he0, hL1, dist_eq_norm] at h1
    have h2 := (L (e x) - ContinuousLinearMap.id ℝ M).le_opNorm v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg v))
  have hU : e '' ball 0 η ∈ 𝓝 (1 : G) := hopen η hη0
  have hφ : Continuous (fun p : V × V => e p.1 * e p.2) :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  have hψ : Continuous (fun p : V × V => (e p.1)⁻¹ * e p.2) :=
    (he.comp continuous_fst).inv.mul (he.comp continuous_snd)
  have hφU : (fun p : V × V => e p.1 * e p.2) ⁻¹' (e '' ball 0 η) ∈ 𝓝 ((0 : V), (0 : V)) :=
    hφ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  have hψU : (fun p : V × V => (e p.1)⁻¹ * e p.2) ⁻¹' (e '' ball 0 η) ∈
      𝓝 ((0 : V), (0 : V)) :=
    hψ.continuousAt.preimage_mem_nhds (by simpa [he0] using hU)
  obtain ⟨η3, hη30, hη3⟩ := Metric.mem_nhds_iff.mp hφU
  obtain ⟨η4, hη40, hη4⟩ := Metric.mem_nhds_iff.mp hψU
  have hφ' : ∀ a b : V, ‖a‖ < η3 → ‖b‖ < η3 → ∃ z, ‖z‖ < η ∧ e z = e a * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η3 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη3 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have hψ' : ∀ a b : V, ‖a‖ < η4 → ‖b‖ < η4 → ∃ z, ‖z‖ < η ∧ e z = (e a)⁻¹ * e b := by
    intro a b ha hb
    have hab : (a, b) ∈ ball ((0 : V), (0 : V)) η4 := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_zero_right]
      exact max_lt ha hb
    obtain ⟨z, hz, hze⟩ := hη4 hab
    exact ⟨z, mem_ball_zero_iff.mp hz, hze⟩
  have h0η : ‖(0 : V)‖ < η := by simpa using hη0
  refine ⟨min (η / 2) (min η2 (min (η3 / 2) (η4 / 2))),
    lt_min (by linarith) (lt_min hη20 (lt_min (by linarith) (by linarith))), ?_⟩
  intro x hx r hr
  rw [mem_ball_zero_iff] at hx
  obtain ⟨hr0, hrδ⟩ := hr
  have b1 : ‖x‖ < η / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have b2 : ‖x‖ < η2 := lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : ‖x‖ < η3 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have b4 : ‖x‖ < η4 / 2 := lt_of_lt_of_le hx
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have r1 : r < η / 2 := lt_of_lt_of_le hrδ (min_le_left _ _)
  have r3 : r < η3 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have r4 : r < η4 / 2 := lt_of_lt_of_le hrδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmx : ∀ y, m (e x * e y) - m (e x) = L (e x) (m (e y) - m (e 0)) := by
    intro y
    rw [map_sub, he0, ← hm, ← hm, mul_one]
  constructor
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [mem_ball_zero_iff] at hy
    obtain ⟨z, hz, hze⟩ := hφ' x y (by linarith) (by linarith)
    refine ⟨z, ?_, hze⟩
    rw [mem_ball, dist_eq_norm]
    have e1 := hD z x hz (by linarith)
    have e2 := hD y 0 (by linarith) h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hze, hmx y] at e1
    have nι : ‖ι (z - x)‖ = ‖z - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have t1 : ‖z - x‖ ≤ ‖L (e x) v‖ + ε * ‖z - x‖ := by
      have h := norm_sub_norm_le (ι (z - x)) (L (e x) v)
      have h' : ‖ι (z - x) - L (e x) v‖ = ‖L (e x) v - ι (z - x)‖ := norm_sub_rev _ _
      linarith
    have t2 : ‖L (e x) v‖ ≤ (1 + ε) * ‖v‖ := by
      have h := norm_sub_norm_le (L (e x) v) v
      linarith
    have t3 : ‖v‖ ≤ (1 + ε) * ‖y‖ := by
      have h := norm_sub_norm_le v (ι y)
      linarith
    have k1 : (1 - ε) * ‖z - x‖ ≤ (1 + ε) ^ 2 * ‖y‖ := by
      have := mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 + ε)
      linarith only [t1, t2, this]
    have k2 : (1 + ε) ^ 2 * ‖y‖ < (1 + ε) ^ 2 * r := mul_lt_mul_of_pos_left hy (by positivity)
    have k3 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k4 : κ * (1 - ε) ^ 2 * r ≤ κ * (1 - ε) * r := by
      have h1 : (1 - ε) ^ 2 ≤ 1 - ε := by
        rw [sq]
        exact mul_le_of_le_one_left (by linarith) (by linarith)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by linarith)) hr0.le
    have k5 : (1 - ε) * ‖z - x‖ < (1 - ε) * (κ * r) := by linarith only [k1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (by linarith)
  · rintro _ ⟨w, hw, rfl⟩
    rw [mem_ball, dist_eq_norm] at hw
    have hwx := norm_sub_norm_le w x
    obtain ⟨y, hyη, hye⟩ := hψ' x w (by linarith) (by linarith)
    have hexy : e w = e x * e y := by rw [hye, mul_inv_cancel_left]
    refine ⟨e y, ⟨y, ?_, rfl⟩, hexy.symm⟩
    rw [mem_ball_zero_iff]
    have e1 := hD w x (by linarith) (by linarith)
    have e2 := hD y 0 hyη h0η
    rw [sub_zero] at e2
    have e3 := hLx x b2 (m (e y) - m (e 0))
    rw [hexy, hmx y] at e1
    have nι : ‖ι (w - x)‖ = ‖w - x‖ := ι.norm_map _
    have nιy : ‖ι y‖ = ‖y‖ := ι.norm_map _
    set v := m (e y) - m (e 0) with hv
    have s1 : ‖L (e x) v‖ ≤ (1 + ε) * ‖w - x‖ := by
      have h := norm_sub_norm_le (L (e x) v) (ι (w - x))
      linarith
    have s2 : (1 - ε) * ‖v‖ ≤ ‖L (e x) v‖ := by
      have h := norm_sub_norm_le v (L (e x) v)
      have h' : ‖v - L (e x) v‖ = ‖L (e x) v - v‖ := norm_sub_rev _ _
      linarith
    have s3 : (1 - ε) * ‖y‖ ≤ ‖v‖ := by
      have h := norm_sub_norm_le (ι y) v
      have h' : ‖ι y - v‖ = ‖v - ι y‖ := norm_sub_rev _ _
      linarith
    have k1 : (1 - ε) ^ 2 * ‖y‖ ≤ (1 - ε) * ‖v‖ := by
      have := mul_le_mul_of_nonneg_left s3 (by linarith : (0 : ℝ) ≤ 1 - ε)
      linarith only [this]
    have k2 : (1 + ε) * ‖w - x‖ < (1 + ε) * r := mul_lt_mul_of_pos_left hw (by linarith)
    have k3 : (1 + ε) * r ≤ (1 + ε) ^ 2 * r := by
      linarith only [mul_pos hε0 hr0, mul_pos (mul_pos hε0 hε0) hr0]
    have k4 : (1 + ε) ^ 2 * r < κ * (1 - ε) ^ 2 * r := mul_lt_mul_of_pos_right hκε hr0
    have k5 : (1 - ε) ^ 2 * ‖y‖ < (1 - ε) ^ 2 * (κ * r) := by
      linarith only [k1, s2, s1, k2, k3, k4]
    exact lt_of_mul_lt_mul_left k5 (pow_pos (by linarith) 2).le

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
namespace GlobalTheory

open Finset

theorem _root_.GlobalTheory.splitHeight_summable_pi_prod {ι : Type} [Fintype ι] {α : ι → Type} {f : ∀ i, α i → ℝ}
    (h0 : ∀ i x, 0 ≤ f i x) (hf : ∀ i, Summable (f i)) :
    Summable fun n : ∀ i, α i => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i (n i)) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image fun n : (∀ i, α i) => n i, ∏ i, f i (n i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
          Finset.prod_nonneg fun i _ => h0 i (n i)
        intro n hn
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ hn
    _ = ∏ i, ∑ x ∈ s.image fun n : (∀ i, α i) => n i, f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' x, f i x := Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Target
namespace GlobalTheory.IntegralNormBound

theorem main {k A : Type} [Field k] [CommRing A] [Algebra k A] {Q : Ideal A} {π : A}
    (hπ : π ∈ Q) (hres : ∀ c : A, ∃ a : k, c - algebraMap k A a ∈ Q)
    (hfil : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) :
    ∀ (m : ℕ) (u : A), ∃ p : Polynomial k, u - Polynomial.aeval π p ∈ Q ^ m := by
  intro m u
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨y, hy, q, hq, hyq⟩ := Submodule.mem_sup.mp (hfil m hp)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨a, ha⟩ := hres c
    refine ⟨p + Polynomial.C a * Polynomial.X ^ m, ?_⟩
    have hpm : π ^ m * (c - algebraMap k A a) ∈ Q ^ (m + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ m) ha
    have key : u - Polynomial.aeval π (p + Polynomial.C a * Polynomial.X ^ m)
        = q + π ^ m * (c - algebraMap k A a) := by
      simp only [map_add (f := _), map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      linear_combination (-1 : A) * hyq
    rw [key]
    exact Ideal.add_mem _ hq hpm

theorem target : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] {Q : Ideal A} {π : A}, π ∈ Q → (∀ (c : A), ∃ (a : k), c - (Algebra.algebraMap k A : k → A) a ∈ Q) → (∀ (m : ℕ), Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + (1 : ℕ))) → ∀ (m : ℕ) (u : A), ∃ (p : Polynomial k), u - (Polynomial.aeval π : Polynomial k → A) p ∈ Q ^ m :=
  fun hπ hres hfil => main hπ hres hfil

end GlobalTheory.IntegralNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotient
namespace GlobalTheory

open Polynomial

theorem valuationSubring_pow_sub_one_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω}
    (hx : A.valuation x ≤ 1) (k : ℕ) :
    A.valuation (x ^ k - 1) ≤ A.valuation (x - 1) := by
  have h : x ^ k - 1 = (∑ i ∈ Finset.range k, x ^ i) * (x - 1) := (geom_sum_mul x k).symm
  rw [h, map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, x ^ i) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_pow]; exact pow_le_one' hx i
  exact mul_le_of_le_one_left' hs

theorem valuation_zeta_sub_one_pow_totient (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω) (hn : 1 ≤ n)
    (hζ : IsPrimitiveRoot ζ (l ^ n)) :
    A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  have hN : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hv1 : ∀ {μ : Ω}, IsPrimitiveRoot μ (l ^ n) → A.valuation μ ≤ 1 := by
    intro μ hμ
    have h1 : A.valuation μ ^ (l ^ n) = 1 := by rw [← map_pow, hμ.pow_eq_one, map_one]
    exact (pow_eq_one_iff.1 h1 |>.resolve_right hN.ne').le
  have key : ∀ μ ∈ primitiveRoots (l ^ n) Ω, A.valuation (1 - μ) = A.valuation (ζ - 1) := by
    intro μ hμ
    rw [mem_primitiveRoots hN] at hμ
    rw [Valuation.map_sub_swap]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact valuationSubring_pow_sub_one_le A (hv1 hζ) i
    · rw [← hj]; exact valuationSubring_pow_sub_one_le A (hv1 hμ) j
  have hcyc := cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (l : Ω) = ∏ μ ∈ primitiveRoots (l ^ (k + 1)) Ω, (1 - μ) := by
    have := congrArg (eval 1) hcyc
    rw [eval_one_cyclotomic_prime_pow, eval_prod] at this
    simpa using this
  rw [h1, map_prod, Finset.prod_congr rfl key, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationZetaSubOnePowTotientStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_ratAlg : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (n : ℕ) (ζ : Ω), 1 ≤ n → IsPrimitiveRoot ζ (l ^ n) → A.valuation (ζ - 1) ^ (l ^ n).totient = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_zeta_sub_one_pow_totient | exact GlobalTheory.valuation_zeta_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_zeta_sub_one_pow_totient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowLeSpanPowSup
namespace GlobalTheory.SpanPowerSupremum

theorem span_sup_sq_eq {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Q.IsPrime]
    (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ 2) :
    Ideal.span {π} ⊔ Q ^ 2 = Q := by
  have hp : Prime Q := Ideal.prime_of_isPrime hQ ‹_›
  have hle : Ideal.span {π} ⊔ Q ^ 2 ≤ Q :=
    sup_le ((Ideal.span_singleton_le_iff_mem Q).mpr h1) (Ideal.pow_le_self two_ne_zero)
  have hdvd : Ideal.span {π} ⊔ Q ^ 2 ∣ Q ^ 2 := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hp 2).mp hdvd
  have heq : Ideal.span {π} ⊔ Q ^ 2 = Q ^ i := associated_iff_eq.mp hassoc
  interval_cases i
  ·
    rw [pow_zero, Ideal.one_eq_top] at heq
    rw [heq, top_le_iff] at hle
    exact (Ideal.IsPrime.ne_top ‹_› hle).elim
  · rw [pow_one] at heq
    exact heq
  ·
    have hmem : π ∈ Ideal.span {π} ⊔ Q ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self π)
    rw [heq] at hmem
    exact (h2 hmem).elim

theorem pow_le_span_pow_sup {A : Type} [CommRing A] [IsDedekindDomain A] {Q : Ideal A}
    [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (h1 : π ∈ Q) (h2 : π ∉ Q ^ (2 : ℕ)) (m : ℕ) :
    Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + (1 : ℕ)) := by
  have hπ : Ideal.span {π} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr h1
  induction m with
  | zero => simp
  | succ m ih =>
    have hπm : Ideal.span {π ^ m} ≤ Q ^ m := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono hπ m
    calc Q ^ (m + 1) = Q ^ m * Q := pow_succ Q m
      _ ≤ (Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) * (Ideal.span {π} ⊔ Q ^ 2) :=
          Ideal.mul_mono ih (span_sup_sq_eq hQ h1 h2).ge
      _ ≤ Ideal.span {π ^ (m + 1)} ⊔ Q ^ (m + 1 + 1) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_left
          · refine le_sup_of_le_right ?_
            calc Ideal.span {π ^ m} * Q ^ 2 ≤ Q ^ m * Q ^ 2 := Ideal.mul_mono_left hπm
              _ = Q ^ (m + 1 + 1) := by rw [← pow_add]
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Ideal.span {π} ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right hπ
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm
          · refine le_sup_of_le_right ?_
            calc Q ^ (m + 1) * Q ^ 2 ≤ Q ^ (m + 1) * Q := Ideal.mul_mono_right (Ideal.pow_le_self two_ne_zero)
              _ = Q ^ (m + 1 + 1) := (pow_succ Q (m + 1)).symm

end GlobalTheory.SpanPowerSupremum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotient
open Polynomial

namespace GlobalTheory

theorem valuation_primitiveRoot_sub_one_pow_totient :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ),
      1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) →
        A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  intro l hl Ω _ _ A m hm ζ hζ
  have hpos : 0 < l ^ m := pow_pos hl.out.pos m

  have memA : ∀ x : Ω, x ^ (l ^ m) = 1 → x ∈ A := by
    intro x hx
    rcases A.mem_or_inv_mem x with h | h
    · exact h
    · have h1 : x * x ^ (l ^ m - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hpos]; exact hx
      have h2 : x⁻¹ = x ^ (l ^ m - 1) := inv_eq_of_mul_eq_one_right h1
      have h3 : x = (x⁻¹) ^ (l ^ m - 1) := by
        rw [inv_pow, ← h2, inv_inv]
      rw [h3]; exact A.pow_mem h _
  have key : ∀ x : Ω, x ∈ A → ∀ a : ℕ, A.valuation (x ^ a - 1) ≤ A.valuation (x - 1) := by
    intro x hx a
    rw [← geom_sum_mul, map_mul]
    have hs : A.valuation (∑ i ∈ Finset.range a, x ^ i) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (sum_mem fun i _ => A.pow_mem hx i)
    calc _ ≤ 1 * A.valuation (x - 1) := by gcongr
      _ = _ := one_mul _
  have eqv : ∀ η ∈ primitiveRoots (l ^ m) Ω, A.valuation (1 - η) = A.valuation (ζ - 1) := by
    intro η hη
    have hη' : IsPrimitiveRoot η (l ^ m) := (mem_primitiveRoots hpos).1 hη
    rw [Valuation.map_sub_swap]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hη'.pow_eq_one
    obtain ⟨b, -, hb⟩ := hη'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm
    · rw [← ha]; exact key ζ (memA ζ hζ.pow_eq_one) a
    · rw [← hb]; exact key η (memA η hη'.pow_eq_one) b
  have hprod : (l : Ω) = ∏ η ∈ primitiveRoots (l ^ m) Ω, (1 - η) := by
    have e1 := Polynomial.eval_one_cyclotomic_prime_pow (R := Ω) (p := l) (m - 1)
    rw [Nat.sub_add_cancel hm, cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at e1
    simpa using e1.symm
  rw [hprod, map_prod, Finset.prod_congr rfl eqv, Finset.prod_const, hζ.card_primitiveRoots]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotientStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (m : ℕ), 1 ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → A.valuation (ζ - 1) ^ Nat.totient (l ^ m) = A.valuation (l : Ω) := by
  first | exact @GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | exact GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient | (intros; apply GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixed
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem mem_adjoin_div_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  intro R Ω _ _ _ _ _ _ _ hinj S x hx
  set A := Algebra.adjoin R S with hA
  set F : Subfield Ω := Subfield.closure (A : Set Ω) with hF
  have hAF : ∀ y ∈ A, y ∈ F := fun y hy => Subfield.subset_closure hy
  let φ : R →+* F := (algebraMap R Ω).codRestrict F (fun r => hAF _ (A.algebraMap_mem r))
  have hφ : ∀ r, algebraMap F Ω (φ r) = algebraMap R Ω r := fun r => rfl
  haveI : Algebra.IsAlgebraic F Ω := by
    constructor
    intro y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) y
    refine ⟨p.map φ, ?_, ?_⟩
    · intro h
      apply hp0
      have hφi : Function.Injective φ := by
        intro a b hab
        apply hinj
        have := congrArg (algebraMap F Ω) hab
        simpa [hφ] using this
      exact (Polynomial.map_eq_zero_iff hφi).mp h
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      rw [Polynomial.aeval_def] at hp
      convert hp using 2
      exact RingHom.ext hφ
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero F := RingHom.charZero (algebraMap F Ω)
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfix : ∀ f : Ω ≃ₐ[F] Ω, f x = x := by
    intro f
    have hfF : ∀ y ∈ F, f y = y := fun y hy => f.commutes ⟨y, hy⟩
    let g : Ω ≃ₐ[R] Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => hfF _ (hAF _ (A.algebraMap_mem r)))
    exact hx g (fun s hs => hfF _ (hAF _ (Algebra.subset_adjoin hs)))
  have hxF : x ∈ F := by
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) x).mpr hfix
    rw [← hy]; exact y.2
  obtain ⟨b, hb, c, hc, hbc⟩ := Subfield.mem_closure_iff.mp hxF
  have hcl : ∀ y ∈ Subring.closure (A : Set Ω), y ∈ A := fun y hy =>
    (Subring.closure_le (t := A.toSubring)).mpr (fun z hz => hz) hy
  by_cases hc0 : c = 0
  · refine ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, ?_⟩
    rw [← hbc, hc0]; simp
  · exact ⟨b, hcl _ hb, c, hcl _ hc, hc0, hbc.symm⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixedStatement
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_div_mem_adjoin_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  first | exact @GlobalTheory.mem_adjoin_div_of_fixed | exact GlobalTheory.mem_adjoin_div_of_fixed | (intros; apply GlobalTheory.mem_adjoin_div_of_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
namespace GlobalTheory

theorem mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by
  intro K _ _ Φ h
  ext d
  set n := ∑ i, d i with hn
  let S : Finset (Fin 3 →₀ ℕ) :=
    (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)
  have hS : ∀ e, e ∈ S ↔ ∑ i, e i = n := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
    intro he i
    change e i ≤ n
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  let P : MvPolynomial (Fin 3) K := ∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)
  have hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst
      (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P := by
    intro t
    have ha : MvPowerSeries.HasSubst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        rw [map_mul]; exact mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))
    have hprod : ∀ e : Fin 3 →₀ ℕ,
        (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) =
          PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s) := by
      intro e
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
    have h1 : PowerSeries.coeff n (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) =
        ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) :=
      MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)
    have hsupp : Function.support (fun e : Fin 3 →₀ ℕ =>
        MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k)) ⊆ S := by
      intro e he
      rw [Function.mem_support] at he
      rw [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul] at he
      rw [Finset.mem_coe, hS]
      by_contra hne
      exact he (by simp [Ne.symm hne])
    rw [h1]
    rw [finsum_eq_sum_of_support_subset _ (s := S) hsupp]
    simp only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [P, map_sum, MvPolynomial.eval_monomial]
        refine Finset.sum_congr rfl (fun e he => ?_)
        rw [if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
  have hP : P = 0 := MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])
  have hd := congrArg (AddMonoidAlgebra.coeff · d) hP
  simp only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd
  simpa using hd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul
open Polynomial

namespace GlobalTheory

theorem algebraMap_norm_dvd_polyX {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}
    (b : Module.Basis (Fin n) k[X] A) (g : A) : g ∣ algebraMap k[X] A (Algebra.norm k[X] g) := by
  classical
  set M := Algebra.leftMulMatrix b g with hM
  have hCH : Polynomial.aeval g M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, map_zero, ← hM, Matrix.aeval_self_charpoly]
  have hsplit := Polynomial.X_mul_divX_add M.charpoly
  have h0 : g * Polynomial.aeval g M.charpoly.divX + algebraMap k[X] A (M.charpoly.coeff 0) = 0 := by
    have := congrArg (Polynomial.aeval g) hsplit
    rw [hCH, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at this
    exact this
  have hdet : Algebra.norm k[X] g = (-1) ^ n * M.charpoly.coeff 0 := by
    rw [Algebra.norm_eq_matrix_det b, ← hM, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  rw [hdet, map_mul, eq_neg_of_add_eq_zero_right h0]
  exact ⟨-(algebraMap k[X] A ((-1) ^ n) * Polynomial.aeval g M.charpoly.divX), by ring⟩

theorem exists_lowDegree_coords_mod : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  intro k A _ _ _ _ n b g q d hg hq hdeg w
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  have hN : Algebra.norm k[X] g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  set p₀ := Algebra.norm k[X] g * q with hp₀
  have hp₀0 : p₀ ≠ 0 := mul_ne_zero hN hq
  have hp₀deg : p₀.natDegree ≤ d + 1 := by rw [hp₀, natDegree_mul hN hq]; exact hdeg
  refine ⟨fun i => b.repr w i % p₀, ?_, ?_⟩
  · intro i
    by_cases h0 : b.repr w i % p₀ = 0
    · simp [h0]
    · have hlt : (b.repr w i % p₀).degree < p₀.degree := EuclideanDomain.mod_lt _ hp₀0
      have := Polynomial.natDegree_lt_natDegree h0 hlt
      show (b.repr w i % p₀).natDegree ≤ d
      omega
  · have key : w - ∑ i, (b.repr w i % p₀) • b i
        = algebraMap k[X] A p₀ * ∑ i, (b.repr w i / p₀) • b i := by
      set a := b.repr w with ha
      have hw : w = ∑ i, a i • b i := (b.sum_repr w).symm
      rw [hw, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, ← eq_sub_of_add_eq (EuclideanDomain.div_add_mod (a i) p₀), mul_smul,
        Algebra.smul_def]
    rw [key, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := algebraMap_norm_dvd_polyX b g
    refine ⟨c * ∑ i, (b.repr w i / p₀) • b i, ?_⟩
    rw [hp₀, map_mul, hc]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMulStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowDegree_coords_mod_mul : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  first | exact @GlobalTheory.exists_lowDegree_coords_mod | exact GlobalTheory.exists_lowDegree_coords_mod | (intros; apply GlobalTheory.exists_lowDegree_coords_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
open Polynomial

namespace GlobalTheory

namespace TaylorSubst

variable {k : Type} [Field k]

theorem subst_decomp (χ u : PowerSeries k) (hu : PowerSeries.constantCoeff u = 0) :
    (χ.subst u : PowerSeries k) =
      u * ((PowerSeries.mk fun p => PowerSeries.coeff (p + 1) χ).subst u : PowerSeries k)
        + PowerSeries.C (PowerSeries.constantCoeff χ) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const χ]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs,
    PowerSeries.subst_C]
  rfl

theorem constantCoeff_subst_eq (χ u : PowerSeries k) (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (χ.subst u : PowerSeries k) = PowerSeries.constantCoeff χ := by
  rw [subst_decomp χ u hu]
  simp [hu]

theorem X_pow_dvd_sub_trunc (χ : PowerSeries k) (n : ℕ) :
    (PowerSeries.X : PowerSeries k) ^ n ∣ χ - (PowerSeries.trunc n χ : PowerSeries k) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hi]

theorem X_pow_dvd_subst_sub (χ u v : PowerSeries k) (n : ℕ)
    (hu : PowerSeries.constantCoeff u = 0) (hv : PowerSeries.constantCoeff v = 0)
    (huv : (PowerSeries.X : PowerSeries k) ^ n ∣ u - v) :
    (PowerSeries.X : PowerSeries k) ^ n ∣
      (χ.subst u : PowerSeries k) - (χ.subst v : PowerSeries k) := by
  have hsu := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  have hsv := PowerSeries.HasSubst.of_constantCoeff_zero' hv
  obtain ⟨ρ, hρ⟩ := X_pow_dvd_sub_trunc χ n
  have hχ : χ = (PowerSeries.trunc n χ : PowerSeries k) + PowerSeries.X ^ n * ρ := by
    rw [← hρ]; ring
  rw [hχ, PowerSeries.subst_add hsu, PowerSeries.subst_add hsv, PowerSeries.subst_mul hsu,
    PowerSeries.subst_mul hsv, PowerSeries.subst_pow hsu, PowerSeries.subst_pow hsv,
    PowerSeries.subst_X hsu, PowerSeries.subst_X hsv, PowerSeries.subst_coe hsu,
    PowerSeries.subst_coe hsv]
  have hXu : (PowerSeries.X : PowerSeries k) ∣ u := PowerSeries.X_dvd_iff.mpr hu
  have hXv : (PowerSeries.X : PowerSeries k) ∣ v := PowerSeries.X_dvd_iff.mpr hv
  have h1 : (PowerSeries.X : PowerSeries k) ^ n ∣
      (Polynomial.aeval u (PowerSeries.trunc n χ) : PowerSeries k)
        - Polynomial.aeval v (PowerSeries.trunc n χ) := by
    refine dvd_trans huv ?_
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map]
    exact Polynomial.sub_dvd_eval_sub u v _
  have h2 : (PowerSeries.X : PowerSeries k) ^ n ∣
      u ^ n * (ρ.subst u : PowerSeries k) - v ^ n * (ρ.subst v : PowerSeries k) :=
    dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu n) _)
      (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXv n) _)
  have := dvd_add h1 h2
  convert this using 1
  ring

end TaylorSubst

theorem taylor_subst_first_order : ∀ (k : Type) [Field k] (φ a b : PowerSeries k) (m : ℕ), 1 ≤ m → PowerSeries.constantCoeff a = 0 →
 PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ ∧
 (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ (φ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - φ.subst a - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
  intro k _ φ a b m hm ha
  refine ⟨TaylorSubst.constantCoeff_subst_eq φ a ha, ?_⟩
  set ψ : PowerSeries k := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) φ with hψ
  have ha' : PowerSeries.constantCoeff (a + PowerSeries.X ^ m * b) = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [ha, pow_succ]
  rw [TaylorSubst.subst_decomp φ _ ha', TaylorSubst.subst_decomp φ _ ha]
  rw [← hψ]
  have hψ0 : PowerSeries.constantCoeff ψ = PowerSeries.coeff 1 φ := by
    rw [hψ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  have hA : (PowerSeries.X : PowerSeries k) ∣
      b * (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
        - PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_mul, TaylorSubst.constantCoeff_subst_eq ψ _ ha',
      hψ0, PowerSeries.constantCoeff_C, sub_self]
  have hB : (PowerSeries.X : PowerSeries k) ^ m ∣
      (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - ψ.subst a :=
    TaylorSubst.X_pow_dvd_subst_sub ψ _ a m ha' ha (by simp)
  have hXa : (PowerSeries.X : PowerSeries k) ∣ a := PowerSeries.X_dvd_iff.mpr ha
  have h := dvd_add (mul_dvd_mul_left ((PowerSeries.X : PowerSeries k) ^ m) hA)
    (mul_dvd_mul hB hXa)
  rw [← pow_succ] at h
  convert h using 1
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrderStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_taylor_subst_first_order : ∀ (k : Type) [Field k] (φ a b : PowerSeries k) (m : ℕ), 1 ≤ m → PowerSeries.constantCoeff a = 0 →
 PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ ∧
 (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ (φ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - φ.subst a - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
  first | exact @GlobalTheory.taylor_subst_first_order | exact GlobalTheory.taylor_subst_first_order | (intros; apply GlobalTheory.taylor_subst_first_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexMapMulLeftLatticeOfSqEqNeg
namespace GlobalTheory

theorem relIndex_map_mulLeft_lattice_of_sq_eq_neg :
    ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), 0 < N → α ^ 2 = -(N : ℂ) →
      (∀ l ∈ L.lattice, α * l ∈ L.lattice) →
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex L.lattice.toAddSubgroup
        = N := by
  intro L α N hN hα hL
  have hα0 : α ≠ 0 := by
    rintro rfl
    have : (N : ℂ) = 0 := by simpa using hα
    exact hN.ne' (by exact_mod_cast this)
  have hinj : Function.Injective (AddMonoidHom.mulLeft α) := mul_right_injective₀ hα0
  set A := L.lattice.toAddSubgroup with hA
  set f := AddMonoidHom.mulLeft α with hf
  have h1 : A.map f ≤ A := by
    rintro _ ⟨l, hl, rfl⟩
    exact hL l hl
  have h2 : (A.map f).map f ≤ A.map f := AddSubgroup.map_mono h1
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h2 h1
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at hmul
  have hr : Module.finrank ℤ L.lattice = 2 := by
    simpa using Module.finrank_eq_card_basis L.latticeBasis
  have hidx : ((A.map f).map f).relIndex A = N ^ 2 := by
    rw [← hr, ← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
      refine ⟨⟨-l, L.lattice.neg_mem hl⟩, Subtype.ext ?_⟩
      have hx' : α * (α * l) = (x : ℂ) := hx
      show N • (-l) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-l) * hα
    · rintro ⟨l, hx⟩
      have hx' : N • (l : ℂ) = (x : ℂ) := congrArg Subtype.val hx
      refine ⟨_, ⟨-(l : ℂ), L.lattice.neg_mem l.2, rfl⟩, ?_⟩
      show α * (α * -(l : ℂ)) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-(l : ℂ)) * hα
  rw [hidx, ← sq] at hmul
  exact Nat.pow_left_injective two_ne_zero hmul

end GlobalTheory
end
