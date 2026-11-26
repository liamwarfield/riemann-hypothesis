module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.Localization.LocalizeA
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem loc_weaklyLocallyCompact {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) : WeaklyLocallyCompactSpace M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨e, hx, -⟩ := hz x
  have ht : e x ∈ e.target := e.map_source hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) ht
  refine ⟨e.symm '' Metric.closedBall (e x) (r / 2), ?_, ?_⟩
  · exact (isCompact_closedBall _ _).image_of_continuousOn
      (e.continuousOn_symm.mono ((Metric.closedBall_subset_ball (by linarith)).trans hsub))
  · have h1 : e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2) ∈ 𝓝 x :=
      (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hx, Set.mem_preimage.mpr (Metric.mem_ball_self (by linarith))⟩
    refine Filter.mem_of_superset h1 ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨e y, Metric.ball_subset_closedBall hy2, e.left_inv hy1⟩

theorem loc_d_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    d n z j f x = d n z j g x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [d, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm he.2
      | (have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)
         rwa [e.left_inv he.2] at hc')
    have hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact ht.eventually h
    unfold wd
    rw [hfg.fderiv_eq]
  · simp only [d, dif_neg hc]

theorem loc_db_congr {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (x : M) (h : f =ᶠ[𝓝 x] g) :
    db n z j f x = db n z j g x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      first
      | exact e.tendsto_symm he.2
      | (have hc' : Tendsto e.symm (𝓝 (e x)) (𝓝 (e.symm (e x))) := e.continuousAt_symm (e.map_source he.2)
         rwa [e.left_inv he.2] at hc')
    have hfg : f ∘ e.symm =ᶠ[𝓝 (z x)] g ∘ e.symm := by
      rw [hzx]
      exact ht.eventually h
    unfold wdb
    rw [hfg.fderiv_eq]
  · simp only [db, dif_neg hc]

theorem loc_ck_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z k (f i)) :
    Ck n z k (fun x => ∑ i ∈ s, f i x) := by
  unfold Ck at hf ⊢
  intro e he
  exact (ContDiffOn.sum fun i _ => hf i e he :
    ContDiffOn ℝ _ (fun y => ∑ i ∈ s, (f i ∘ e.symm) y) e.target)

theorem loc_d_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z 1 (f i)) (j : Fin n) (x : M) :
    d n z j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, d n z j (f i) x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [d, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x) := by
      intro i _
      rw [he.1 he.2]
      exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt
        (by first | simp | norm_num | exact le_rfl)
    have hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y := rfl
    unfold wd
    (first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])
    have key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) - Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 =
        ∑ i ∈ s, (L i (bas n j) - Complex.I * L i (Complex.I • bas n j)) / 2 := by
      intro L
      simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact key _
  · simp only [d, dif_neg hc, Finset.sum_const_zero]

theorem loc_db_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z 1 (f i)) (j : Fin n) (x : M) :
    db n z j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, db n z j (f i) x := by
  by_cases hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · simp only [db, dif_pos hc]
    set e := Classical.choose hc with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hc
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ e.symm) (z x) := by
      intro i _
      rw [he.1 he.2]
      exact ((hf i e he.1).contDiffAt (e.open_target.mem_nhds (e.map_source he.2))).differentiableAt
        (by first | simp | norm_num | exact le_rfl)
    have hsum : ((fun y => ∑ i ∈ s, f i y) ∘ e.symm) = fun y => ∑ i ∈ s, (f i ∘ e.symm) y := rfl
    unfold wdb
    (first | rw [hsum, fderiv_fun_sum hdiff] | rw [hsum, ← Finset.sum_fn, fderiv_sum hdiff])
    have key : ∀ L : ι → (V n →L[ℝ] ℂ), ((∑ i ∈ s, L i) (bas n j) + Complex.I * (∑ i ∈ s, L i) (Complex.I • bas n j)) / 2 =
        ∑ i ∈ s, (L i (bas n j) + Complex.I * L i (Complex.I • bas n j)) / 2 := by
      intro L
      simp only [ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact key _
  · simp only [db, dif_neg hc, Finset.sum_const_zero]

theorem loc_norm_sum_sq {E : Type*} [SeminormedAddCommGroup E] {N : ℕ} (a : Fin N → E) :
    ‖∑ i, a i‖ ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖a i‖) ^ 2 ≤ N * ∑ i, ‖a i‖ ^ 2 := by
    first
    | (have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
       simpa using h3)
    | (have h3 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖)
       simpa using h3)
  calc ‖∑ i, a i‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 := by gcongr
    _ ≤ N * ∑ i, ‖a i‖ ^ 2 := h2

theorem two_form_sq_finset_sum_le {n N : ℕ} (σ : Fin N → Fin n → Fin n → ℂ) :
    sq2 n (fun j k => ∑ i, σ i j k) ≤ N * ∑ i, sq2 n (σ i) := by
  have h : ∀ j k, ‖∑ i, σ i j k‖ ^ 2 ≤ N * ∑ i, ‖σ i j k‖ ^ 2 := fun j k =>
    loc_norm_sum_sq (fun i => σ i j k)
  have hs : ∑ i, ∑ j, ∑ k, ‖σ i j k‖ ^ 2 = ∑ j, ∑ k, ∑ i, ‖σ i j k‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  simp only [sq2]
  rw [← Finset.sum_div, ← mul_div_assoc, hs, Finset.mul_sum]
  gcongr with j _
  rw [Finset.mul_sum]
  gcongr with k _
  exact h j k

theorem loc_memLp_iff {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E] (ν : Measure M)
    (f : M → E) (hf : AEStronglyMeasurable f ν) :
    MemLp f 2 ν ↔ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤ := by
  rw [memLp_iff]
  simpa [ENNReal.rpow_two] using
    eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top (p := 2) (by norm_num) (by norm_num) hf

theorem locL2_of_le_sum {M E F₁ F₂ : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] (μ : Measure M)
    (f : M → E) (g₁ : M → F₁) (g₂ : M → F₂) (c : ℝ) (h₁ : LocalL2Isometry μ g₁) (h₂ : LocalL2Isometry μ g₂)
    (hf : AEStronglyMeasurable f μ) (hle : ∀ x, ‖f x‖ ≤ c * (‖g₁ x‖ + ‖g₂ x‖)) : LocalL2Isometry μ f := by
  refine ⟨hf, fun C hC => ?_⟩
  have m1 : MemLp g₁ 2 (μ.restrict C) := (loc_memLp_iff _ _ h₁.1.restrict).mpr (h₁.2 C hC)
  have m2 : MemLp g₂ 2 (μ.restrict C) := (loc_memLp_iff _ _ h₂.1.restrict).mpr (h₂.2 C hC)
  have m3 : MemLp (fun x => c * (‖g₁ x‖ + ‖g₂ x‖)) 2 (μ.restrict C) := (m1.norm.add m2.norm).const_mul c
  have m4 : MemLp f 2 (μ.restrict C) := m3.of_le hf.restrict (Filter.Eventually.of_forall fun x => by
    show ‖f x‖ ≤ ‖c * (‖g₁ x‖ + ‖g₂ x‖)‖
    rw [Real.norm_eq_abs]
    exact (hle x).trans (le_abs_self _))
  exact (loc_memLp_iff _ _ hf.restrict).mp m4

def locG {M : Type*} {n : ℕ} (η : M → ℝ) (G : M → V n) : M → V n :=
  fun x => (η x : ℂ) • G x

def locD {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (G : M → V n)
    (D : M → ℂ) : M → ℂ :=
  fun x => (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j

def locS {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ) (G : M → V n)
    (S : M → Fin n → Fin n → ℂ) : M → Fin n → Fin n → ℂ :=
  fun x j k => (η x : ℂ) * S x j k +
    wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k

theorem loc_sum_apply {n N : ℕ} (a : Fin N → V n) (j : Fin n) :
    (∑ i, a i) j = ∑ i, a i j := by
  first
  | exact Finset.sum_apply j Finset.univ a
  | simp [Finset.sum_apply]
  | simp [WithLp.ofLp_sum]
  | exact map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ
  | simpa using map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ

theorem loc_tsupport_sub {M E : Type*} [TopologicalSpace M] [Zero E] (f : M → E) (T : Set M)
    (hT : IsClosed T) (h : ∀ x, x ∉ T → f x = 0) : tsupport f ⊆ T := by
  refine closure_minimal (fun x hx => ?_) hT
  by_contra hxT
  exact hx (h x hxT)

theorem loc_continuous_wedge (n : ℕ) :
    Continuous (fun p : (Fin n → ℂ) × (Fin n → ℂ) => wedge p.1 p.2) := by
  first
  | (unfold wedge; fun_prop)
  | (refine continuous_pi fun j => continuous_pi fun k => ?_
     unfold wedge
     fun_prop)
  | (refine continuous_pi fun j => continuous_pi fun k => ?_
     simp only [wedge]
     exact (((continuous_apply j).comp continuous_fst).mul ((continuous_apply k).comp continuous_snd)).sub
       (((continuous_apply k).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)))

theorem continuous_two_form_norm_sq (n : ℕ) : Continuous (sq2 n) := by
  show Continuous (fun σ : Fin n → Fin n → ℂ => (∑ j, ∑ k, ‖σ j k‖ ^ 2) / 2)
  first
  | fun_prop
  | exact (continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ =>
      (((continuous_apply k).comp (continuous_apply j)).norm.pow 2)).div_const 2

private theorem chart_symm_eventuallyEq_at_chart_point {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e') (y : M)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) : e'.symm =ᶠ[𝓝 (z y)] e.symm := by
  have hzy : z y = e y := he hy
  have hzy' : z y = e' y := he' hy'
  have h1 : ∀ᶠ w in 𝓝 (z y), w ∈ e.target := by
    rw [hzy]
    exact e.open_target.mem_nhds (e.map_source hy)
  have h2 : ∀ᶠ w in 𝓝 (z y), w ∈ e'.target := by
    rw [hzy']
    exact e'.open_target.mem_nhds (e'.map_source hy')
  have ht : Tendsto e'.symm (𝓝 (z y)) (𝓝 y) := by
    rw [hzy']
    first
    | exact e'.tendsto_symm hy'
    | (have hc' : Tendsto e'.symm (𝓝 (e' y)) (𝓝 (e'.symm (e' y))) := e'.continuousAt_symm (e'.map_source hy')
       rwa [e'.left_inv hy'] at hc')
  have h3 : ∀ᶠ w in 𝓝 (z y), e'.symm w ∈ e.source := ht.eventually (e.open_source.mem_nhds hy)
  filter_upwards [h1, h2, h3] with w hw hw' hw''
  refine e.injOn hw'' (e.map_target hw) ?_
  rw [e.right_inv hw, ← he hw'', he' (e'.map_target hw'), e'.right_inv hw']

private theorem d_eq_wd_at_chart_image {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M) (hy : y ∈ e.source) (j : Fin n) :
    d n z j g y = wd n j (g ∘ e.symm) (e y) := by
  have hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  simp only [d, dif_pos hc]
  have hs := Classical.choose_spec hc
  have hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm :=
    (chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g
  rw [← he hy]
  unfold wd
  rw [hfg.fderiv_eq]

private theorem db_eq_wdb_at_chart_image {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M) (hy : y ∈ e.source) (j : Fin n) :
    db n z j g y = wdb n j (g ∘ e.symm) (e y) := by
  have hc : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  simp only [db, dif_pos hc]
  have hs := Classical.choose_spec hc
  have hfg : g ∘ (Classical.choose hc).symm =ᶠ[𝓝 (z y)] g ∘ e.symm :=
    (chart_symm_eventuallyEq_at_chart_point n z e (Classical.choose hc) he hs.1 y hy hs.2).fun_comp g
  rw [← he hy]
  unfold wdb
  rw [hfg.fderiv_eq]

private theorem continuous_d_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) (j : Fin n) :
    Continuous (fun x => d n z j g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target :=
    (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)
  have h0 : ContinuousOn (fun w => wd n j (g ∘ e.symm) w) e.target := by
    unfold wd
    exact ((hF.clm_apply continuousOn_const).sub (continuousOn_const.mul
      (hF.clm_apply continuousOn_const))).div_const 2
  have hW : ContinuousOn (fun y => wd n j (g ∘ e.symm) (e y)) e.source :=
    h0.comp e.continuousOn (fun y hy => e.map_source hy)
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  have hEv : (fun y => wd n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => d n z j g y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (d_eq_wd_at_chart_image n z g e he y hy j).symm
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc

private theorem continuous_db_apply_of_smooth {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) (j : Fin n) :
    Continuous (fun x => db n z j g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hF : ContinuousOn (fun w => fderiv ℝ (g ∘ e.symm) w) e.target :=
    (hg e he).continuousOn_fderiv_of_isOpen e.open_target (by first | simp | exact_mod_cast le_top | norm_num)
  have h0 : ContinuousOn (fun w => wdb n j (g ∘ e.symm) w) e.target := by
    unfold wdb
    exact ((hF.clm_apply continuousOn_const).add (continuousOn_const.mul
      (hF.clm_apply continuousOn_const))).div_const 2
  have hW : ContinuousOn (fun y => wdb n j (g ∘ e.symm) (e y)) e.source :=
    h0.comp e.continuousOn (fun y hy => e.map_source hy)
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  have hEv : (fun y => wdb n j (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] fun y => db n z j g y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact (db_eq_wdb_at_chart_image n z g e he y hy j).symm
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc

private theorem continuous_of_smooth_localization {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Smooth n z g) : Continuous g := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => by rw [hze]
  have hW : ContinuousOn (fun y => (g ∘ e.symm) (e y)) e.source :=
    (hg e he).continuousOn.comp e.continuousOn (fun y hy => e.map_source hy)
  have hEv : (fun y => (g ∘ e.symm) (e y)) =ᶠ[𝓝 x] g := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hc := hW.continuousAt (e.open_source.mem_nhds hx)
  first
  | exact hc.congr hEv
  | exact hc.congr_of_eventuallyEq hEv.symm
  | exact (continuousAt_congr hEv).mp hc

theorem loc_piece {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (hMD : MultDivStatement n M) (hMS : MultSStatement n M) (η : M → ℝ) (hη : SmoothR n z η)
    (hηc : HasCompactSupport η) (T : Set M) (hT : tsupport η ⊆ T)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : LocalL2Isometry (vol n z) G) (hD : LocalL2Isometry (vol n z) D) (hS : LocalL2Isometry (vol n z) S)
    (hGD : IsWeakDiv n z G D) (hGS : IsWeakS n z G S) :
    LocalL2Isometry (vol n z) (locG η G) ∧ LocalL2Isometry (vol n z) (locD n z η G D) ∧
      LocalL2Isometry (vol n z) (locS n z η G S) ∧
      IsWeakDiv n z (locG η G) (locD n z η G D) ∧ IsWeakS n z (locG η G) (locS n z η G S) ∧
      HasCompactSupport (locG η G) ∧ HasCompactSupport (locD n z η G D) ∧
      HasCompactSupport (locS n z η G S) ∧
      tsupport (locG η G) ⊆ T ∧ tsupport (locD n z η G D) ⊆ T ∧
      tsupport (locS n z η G S) ⊆ T := by
  have hsm : Smooth n z (fun y => (η y : ℂ)) := hη
  have hCC : Continuous (fun y => (η y : ℂ)) := continuous_of_smooth_localization n z hz _ hsm
  have hz0 : ∀ x, x ∉ tsupport η → η x = 0 := fun x hx => by
    by_contra hne
    exact hx (subset_tsupport η hne)
  have hev : ∀ x, x ∉ tsupport η → (fun y => (η y : ℂ)) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    intro x hx
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    simp [hz0 y hy]
  have hd0 : ∀ j x, x ∉ tsupport η → d n z j (fun y => (η y : ℂ)) x = 0 := by
    intro j x hx
    rw [loc_d_congr n z hz j _ _ x (hev x hx)]
    unfold d wd
    split_ifs <;> simp [Function.comp_def]
  have hdb0 : ∀ j x, x ∉ tsupport η → db n z j (fun y => (η y : ℂ)) x = 0 := by
    intro j x hx
    rw [loc_db_congr n z hz j _ _ x (hev x hx)]
    unfold db wdb
    split_ifs <;> simp [Function.comp_def]
  have hdc : ∀ j, Continuous (fun x => d n z j (fun y => (η y : ℂ)) x) := fun j =>
    continuous_d_of_smooth n z hz _ hsm j
  have hdbc : ∀ j, Continuous (fun x => db n z j (fun y => (η y : ℂ)) x) := fun j =>
    continuous_db_apply_of_smooth n z hz _ hsm j
  have hbound : ∀ φ : M → ℂ, Continuous φ → (∀ x, x ∉ tsupport η → φ x = 0) →
      ∃ C, 0 ≤ C ∧ ∀ x, ‖φ x‖ ≤ C := by
    intro φ hφ h0
    have hsub : tsupport φ ⊆ tsupport η := loc_tsupport_sub φ _ (isClosed_tsupport η) h0
    have hcs : HasCompactSupport φ := IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsub
    have hex : ∃ C, ∀ x, ‖φ x‖ ≤ C := by
      first
      | exact hφ.bounded_above_of_compact_support hcs
      | (obtain ⟨C, hC⟩ := (hcs.isCompact_range hφ).isBounded.exists_norm_le
         exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩)
    obtain ⟨C, hC⟩ := hex
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  obtain ⟨Cη, hCη0, hCη⟩ := hbound _ hCC (fun x hx => by simp [hz0 x hx])
  obtain ⟨K, hK0, hKd, hKdb⟩ : ∃ K : ℝ, 0 ≤ K ∧ (∀ j x, ‖d n z j (fun y => (η y : ℂ)) x‖ ≤ K) ∧
      (∀ j x, ‖db n z j (fun y => (η y : ℂ)) x‖ ≤ K) := by
    choose C1 hC10 hC1 using fun j => hbound _ (hdc j) (hd0 j)
    choose C2 hC20 hC2 using fun j => hbound _ (hdbc j) (hdb0 j)
    refine ⟨∑ j, (C1 j + C2 j), Finset.sum_nonneg fun j _ => add_nonneg (hC10 j) (hC20 j), ?_, ?_⟩
    · intro j x
      have hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i) :=
        Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i))
          (Finset.mem_univ j)
      linarith [hC1 j x, hC20 j]
    · intro j x
      have hs : C1 j + C2 j ≤ ∑ i, (C1 i + C2 i) :=
        Finset.single_le_sum (f := fun i => C1 i + C2 i) (fun i _ => add_nonneg (hC10 i) (hC20 i))
          (Finset.mem_univ j)
      linarith [hC2 j x, hC10 j]
  have hcoord : ∀ (v : V n) (j : Fin n), ‖v j‖ ≤ ‖v‖ := by
    intro v j
    first
    | exact PiLp.norm_apply_le v j
    | exact PiLp.norm_apply_le_norm v j
    | (rw [EuclideanSpace.norm_eq]
       exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
         (fun i _ => sq_nonneg _) (Finset.mem_univ j))))
  have hcoordc : ∀ j : Fin n, Continuous (fun v : V n => v j) := by
    intro j
    first
    | fun_prop
    | exact (EuclideanSpace.proj (𝕜 := ℂ) j).continuous
    | exact PiLp.continuous_apply 2 _ j
    | continuity
  have hGj : ∀ j : Fin n, AEStronglyMeasurable (fun x => G x j) (vol n z) := fun j =>
    (hcoordc j).comp_aestronglyMeasurable hG.1
  have hGm : LocalL2Isometry (vol n z) (locG η G) := by
    refine locL2_of_le_sum (vol n z) (locG η G) G G Cη hG hG (hCC.aestronglyMeasurable.smul hG.1)
      fun x => ?_
    show ‖(η x : ℂ) • G x‖ ≤ Cη * (‖G x‖ + ‖G x‖)
    rw [norm_smul]
    have := mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg (G x))
    nlinarith [mul_nonneg hCη0 (norm_nonneg (G x))]
  have hDmeas : AEStronglyMeasurable (locD n z η G D) (vol n z) := by
    have h2 : AEStronglyMeasurable (fun x => ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j) (vol n z) := by
      first
      | exact Finset.aestronglyMeasurable_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
      | exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
      | exact Finset.aestronglyMeasurable_sum' _ fun j _ => (hdc j).aestronglyMeasurable.mul (hGj j)
    exact (hCC.aestronglyMeasurable.mul hD.1).add h2
  have hDm : LocalL2Isometry (vol n z) (locD n z η G D) := by
    refine locL2_of_le_sum (vol n z) (locD n z η G D) G D (Cη + (n : ℝ) * K) hG hD hDmeas fun x => ?_
    show ‖(η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤
      (Cη + (n : ℝ) * K) * (‖G x‖ + ‖D x‖)
    have e1 : ‖(η x : ℂ) * D x‖ ≤ Cη * ‖D x‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCη x) (norm_nonneg _)
    have e2 : ‖∑ j, d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ (n : ℝ) * K * ‖G x‖ := by
      refine (norm_sum_le _ _).trans ?_
      have hj : ∀ j ∈ Finset.univ, ‖d n z j (fun y => (η y : ℂ)) x * G x j‖ ≤ K * ‖G x‖ := by
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hKd j x) (hcoord (G x) j) (norm_nonneg _) hK0
      refine (Finset.sum_le_sum hj).trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg (Nat.cast_nonneg n) hK0
    refine (norm_add_le _ _).trans ?_
    nlinarith [norm_nonneg (G x), norm_nonneg (D x), mul_nonneg hCη0 (norm_nonneg (G x)),
      mul_nonneg hnK (norm_nonneg (D x))]
  have hSmeas : AEStronglyMeasurable (locS n z η G S) (vol n z) := by
    have h1 : AEStronglyMeasurable (fun x => fun l => db n z l (fun y => (η y : ℂ)) x) (vol n z) :=
      (continuous_pi fun l => hdbc l).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x => fun l => G x l) (vol n z) :=
      (continuous_pi fun l => hcoordc l).comp_aestronglyMeasurable hG.1
    have hpair : AEStronglyMeasurable
        (fun x => ((fun l => db n z l (fun y => (η y : ℂ)) x), (fun l => G x l))) (vol n z) := by
      first
      | exact h1.prodMk h2
      | exact h1.prod_mk h2
    have hW := (loc_continuous_wedge n).comp_aestronglyMeasurable hpair
    exact (hCC.aestronglyMeasurable.smul hS.1).add hW
  have hSm : LocalL2Isometry (vol n z) (locS n z η G S) := by
    refine locL2_of_le_sum (vol n z) (locS n z η G S) G S (Cη + 2 * K) hG hS hSmeas fun x => ?_
    have hc0 : 0 ≤ (Cη + 2 * K) * (‖G x‖ + ‖S x‖) :=
      mul_nonneg (by linarith) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (pi_norm_le_iff_of_nonneg hc0).mpr fun j => (pi_norm_le_iff_of_nonneg hc0).mpr fun k => ?_
    show ‖(η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ _
    have e1 : ‖(η x : ℂ) * S x j k‖ ≤ Cη * ‖S x‖ := by
      rw [norm_mul]
      exact mul_le_mul (hCη x) ((norm_le_pi_norm (S x j) k).trans (norm_le_pi_norm (S x) j))
        (norm_nonneg _) hCη0
    have e2 : ‖wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k‖ ≤ 2 * K * ‖G x‖ := by
      simp only [wedge]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have a1 := mul_le_mul (hKdb j x) (hcoord (G x) k) (norm_nonneg _) hK0
      have a2 := mul_le_mul (hKdb k x) (hcoord (G x) j) (norm_nonneg _) hK0
      linarith
    refine (norm_add_le _ _).trans ?_
    nlinarith [norm_nonneg (G x), norm_nonneg (S x), mul_nonneg hCη0 (norm_nonneg (G x)),
      mul_nonneg hK0 (norm_nonneg (S x))]
  have hsubG : tsupport (locG η G) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      show (η x : ℂ) • G x = 0
      simp [hz0 x hx]
  have hsubD : tsupport (locD n z η G D) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      show (η x : ℂ) * D x + ∑ j, d n z j (fun y => (η y : ℂ)) x * G x j = 0
      simp [hz0 x hx, fun j => hd0 j x hx]
  have hsubS : tsupport (locS n z η G S) ⊆ tsupport η :=
    loc_tsupport_sub _ _ (isClosed_tsupport η) fun x hx => by
      funext j k
      show (η x : ℂ) * S x j k + wedge (fun l => db n z l (fun y => (η y : ℂ)) x) (fun l => G x l) j k = 0
      simp [hz0 x hx, fun j => hdb0 j x hx, wedge]
  exact ⟨hGm, hDm, hSm, hMD z hz η G D hη hG hD hGD, hMS z hz η G S hη hG hS hGS,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubG,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubD,
    IsCompact.of_isClosed_subset hηc (isClosed_tsupport _) hsubS,
    hsubG.trans hT, hsubD.trans hT, hsubS.trans hT⟩

theorem two_form_norm_sq_nonneg (n : ℕ) (σ : Fin n → Fin n → ℂ) : 0 ≤ sq2 n σ := by
  unfold sq2
  first
  | positivity
  | exact div_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (by norm_num)

theorem loc_ofReal_le {N : ℕ} (b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) (a : ℝ)
    (h : a ≤ N * ∑ i, b i) : ENNReal.ofReal a ≤ N * ∑ i, ENNReal.ofReal (b i) := by
  calc ENNReal.ofReal a ≤ ENNReal.ofReal (N * ∑ i, b i) := ENNReal.ofReal_le_ofReal h
    _ = N * ∑ i, ENNReal.ofReal (b i) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => hb i),
        ENNReal.ofReal_natCast]

theorem loc_lintegral_sum_lt {M : Type*} [MeasurableSpace M] (μ : Measure M) {N : ℕ}
    (F : M → ℝ≥0∞) (f : Fin N → M → ℝ≥0∞) (hf : ∀ i, AEMeasurable (f i) μ)
    (hle : ∀ x, F x ≤ N * ∑ i, f i x) (δ' δ : ℝ≥0∞) (hi : ∀ i, ∫⁻ x, f i x ∂μ < δ')
    (hδ : δ' * (N * N) < δ) : ∫⁻ x, F x ∂μ < δ := by
  calc ∫⁻ x, F x ∂μ ≤ ∫⁻ x, N * ∑ i, f i x ∂μ := lintegral_mono hle
    _ = N * ∑ i, ∫⁻ x, f i x ∂μ := by
      rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N), MeasureTheory.lintegral_finsetSum' _ (fun i _ => hf i)]
    _ ≤ N * ∑ _i : Fin N, δ' := by
      gcongr with i
      exact (hi i).le
    _ = δ' * (N * N) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ < δ := hδ

theorem loc_aem {M E : Type*} [MeasurableSpace M] [NormedAddCommGroup E] (μ : Measure M)
    (a : M → E) (h : AEStronglyMeasurable a μ) :
    AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x))) μ := by
  simp only [neg_zero, Real.exp_zero, mul_one]
  exact ((continuous_norm.pow 2).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal

theorem aemeasurable_unweighted_two_form {M : Type*} [MeasurableSpace M] {n : ℕ} (μ : Measure M)
    (σ : M → Fin n → Fin n → ℂ) (h : AEStronglyMeasurable σ μ) :
    AEMeasurable (fun x => ENNReal.ofReal (sq2 n (σ x) * Real.exp (-(fun _ : M => (0 : ℝ)) x))) μ := by
  simp only [neg_zero, Real.exp_zero, mul_one]
  exact ((continuous_two_form_norm_sq n).comp_aestronglyMeasurable h).aemeasurable.ennreal_ofReal

end

end ReciprocityTheory.L2DbarEstimates.F
end

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem localize (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMD : MultDivStatement n M) (hMS : MultSStatement n M) :
    LocalizeStatement n M := by
  intro z hz H G D S hG hD hS hGD hGS hcG hcD hcS
  have := loc_weaklyLocallyCompact n z hz
  have hK : IsCompact (tsupport G ∪ tsupport D ∪ tsupport S) := (hcG.union hcD).union hcS
  set K := tsupport G ∪ tsupport D ∪ tsupport S with hKdef
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hK
  obtain ⟨N, e, χ, he, hχs, hχc, hχsub, -, -, hχK⟩ :=
    exists_chart_partition n z hz K' univ hK' isOpen_univ (subset_univ _)
  have hck : ∀ i, Ck n z 1 (fun y => (χ i y : ℂ)) := fun i => SmoothR.ckR n z 1 (χ i) (hχs i)
  have hoff : ∀ x, x ∉ K → G x = 0 ∧ D x = 0 ∧ S x = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inl h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inl (Or.inr h)),
     image_eq_zero_of_notMem_tsupport fun h => hx (Or.inr h)⟩
  have hone : ∀ x ∈ K, ∑ i, (χ i x : ℂ) = 1 := fun x hx => by
    rw [← Complex.ofReal_sum, hχK x (interior_subset (hKK' hx)), Complex.ofReal_one]
  have hev : ∀ x ∈ K, (fun y => ∑ i, (χ i y : ℂ)) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := fun x hx => by
    filter_upwards [isOpen_interior.mem_nhds (hKK' hx)] with y hy
    rw [← Complex.ofReal_sum, hχK y (interior_subset hy), Complex.ofReal_one]
  have hdz : ∀ x ∈ K, ∀ j, ∑ i, d n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_d_sum n z Finset.univ _ hck j x, loc_d_congr n z hz j _ _ x (hev x hx), d_const]
  have hdbz : ∀ x ∈ K, ∀ j, ∑ i, db n z j (fun y => (χ i y : ℂ)) x = 0 := fun x hx j => by
    rw [← loc_db_sum n z Finset.univ _ hck j x, loc_db_congr n z hz j _ _ x (hev x hx), db_const]
  have sG : ∀ x, G x = ∑ i, locG (χ i) G x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locG]; rw [← Finset.sum_smul, hone x hx, one_smul]
    · simp [locG, (hoff x hx).1]
  have sD : ∀ x, D x = ∑ i, locD n z (χ i) G D x := fun x => by
    by_cases hx : x ∈ K
    · simp only [locD, Finset.sum_add_distrib, ← Finset.sum_mul, hone x hx, one_mul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hdz x hx, zero_mul, Finset.sum_const_zero, add_zero]
    · simp [locD, (hoff x hx).1, (hoff x hx).2.1]
  have sS : ∀ x j k, S x j k = ∑ i, locS n z (χ i) G S x j k := fun x j k => by
    by_cases hx : x ∈ K
    · simp only [locS, wedge, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hone x hx, one_mul, hdbz x hx, zero_mul, sub_self, add_zero]
    · simp [locS, wedge, (hoff x hx).1, (hoff x hx).2.2]
  have hP := fun i => loc_piece n z hz hMD hMS (χ i) (hχs i) (hχc i) (e i).source
    ((hχsub i).trans inter_subset_left) G D S hG hD hS hGD hGS
  choose K0 hK0 happ using fun i => H (e i) _ _ _ (he i) (hP i).1 (hP i).2.1 (hP i).2.2.1
    (hP i).2.2.2.1 (hP i).2.2.2.2.1 (hP i).2.2.2.2.2.1 (hP i).2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.1 (hP i).2.2.2.2.2.2.2.2.2.1
    (hP i).2.2.2.2.2.2.2.2.2.2
  refine ⟨⋃ i, K0 i, isCompact_iUnion hK0, fun δ hδ => ?_⟩
  obtain ⟨δ', hδ'0, hδ'⟩ := ENNReal.exists_pos_mul_lt (a := (N : ℝ≥0∞) * N) (b := δ)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (ENNReal.natCast_ne_top N)) hδ.ne'
  choose g hgT hg0 hg1 hg2 hg3 using fun i => happ i δ' hδ'0
  have hgc : ∀ i j, Ck n z 2 (fun x => g i x j) := fun i j => (hgT i j).1
  have hgc1 : ∀ i j, Ck n z (0 + 1) (fun x => g i x j) := fun i j =>
    Ck.mono n z 1 2 (by norm_num) _ (hgc i j)
  have hfun : ∀ j, (fun x => (∑ i, g i x) j) = fun x => ∑ i, g i x j := fun j =>
    funext fun x => loc_sum_apply _ j
  have hvan : ∀ x, x ∉ ⋃ i, K0 i → ∑ i, g i x = 0 := fun x hx =>
    Finset.sum_eq_zero fun i _ => hg0 i x fun h => hx (mem_iUnion.2 ⟨i, h⟩)
  have hgcont : ∀ i, Continuous (g i) := fun i => by
    have : Continuous (fun x => WithLp.toLp 2 (fun j => g i x j)) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => Ck.continuous n z hz 2 _ (hgc i j))
    exact this
  have hdivc : ∀ i, Continuous (divF n z (g i)) := fun i => by
    unfold divF
    exact continuous_finsetSum _ fun j _ => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (hgc1 i j))
  have hsbc : ∀ i, Continuous (sbar n z (g i)) := fun i => by
    unfold sbar
    exact continuous_pi fun j => continuous_pi fun k =>
      (Ck.continuous n z hz 0 _ (Ck.db n z 0 j _ (hgc1 i k))).sub
        (Ck.continuous n z hz 0 _ (Ck.db n z 0 k _ (hgc1 i j)))
  have hdiv : ∀ x, divF n z (fun x => ∑ i, g i x) x = ∑ i, divF n z (g i) x := fun x => by
    simp only [divF]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfun j, loc_d_sum n z Finset.univ (fun i y => g i y j) (fun i => hgc1 i j) j x]
  have hsb : ∀ x j k, sbar n z (fun x => ∑ i, g i x) x j k = ∑ i, sbar n z (g i) x j k :=
    fun x j k => by
    simp only [sbar]
    rw [hfun k, hfun j, loc_db_sum n z _ (fun i y => g i y k) (fun i => hgc1 i k) j x,
      loc_db_sum n z _ (fun i y => g i y j) (fun i => hgc1 i j) k x, Finset.sum_sub_distrib]
  refine ⟨fun x => ∑ i, g i x, fun j => ⟨?_, ?_⟩, hvan, ?_, ?_, ?_⟩
  · rw [hfun j]; exact loc_ck_sum n z 2 _ _ fun i => hgc i j
  · refine HasCompactSupport.intro (isCompact_iUnion hK0) fun x hx => ?_
    show (∑ i, g i x) j = 0
    rw [hvan x hx]; rfl
  · unfold nV
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal (‖g i x - locG (χ i) G x‖ ^ 2 *
      Real.exp (-(fun _ : M => (0 : ℝ)) x))) (fun i => loc_aem _ _ ((hgcont i).aestronglyMeasurable.sub
      (hP i).1.1)) (fun x => ?_) δ' δ (fun i => hg1 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : (∑ i, g i x) - G x = ∑ i, (g i x - locG (χ i) G x) := by
      rw [Finset.sum_sub_distrib, ← sG x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold wint
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (‖divF n z (g i) x - locD n z (χ i) G D x‖ ^ 2 * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => loc_aem _ _ ((hdivc i).aestronglyMeasurable.sub (hP i).2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg2 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : divF n z (fun x => ∑ i, g i x) x - D x =
        ∑ i, (divF n z (g i) x - locD n z (χ i) G D x) := by
      rw [hdiv x, Finset.sum_sub_distrib, ← sD x]
    rw [this]
    exact loc_ofReal_le _ (fun i => by positivity) _ (loc_norm_sum_sq _)
  · unfold n2
    refine loc_lintegral_sum_lt (vol n z) _ (fun i x => ENNReal.ofReal
      (sq2 n (sbar n z (g i) x - locS n z (χ i) G S x) * Real.exp (-(fun _ : M => (0 : ℝ)) x)))
      (fun i => aemeasurable_unweighted_two_form _ _ ((hsbc i).aestronglyMeasurable.sub (hP i).2.2.1.1)) (fun x => ?_) δ' δ
      (fun i => hg3 i) hδ'
    simp only [neg_zero, Real.exp_zero, mul_one]
    have : sbar n z (fun x => ∑ i, g i x) x - S x =
        fun j k => ∑ i, (sbar n z (g i) x - locS n z (χ i) G S x) j k := by
      funext j k
      simp only [Pi.sub_apply]
      rw [hsb x j k, sS x j k, Finset.sum_sub_distrib]
    rw [this]
    exact loc_ofReal_le _ (fun i => two_form_norm_sq_nonneg _ _) _ (two_form_sq_finset_sum_le _)

end

end ReciprocityTheory.L2DbarEstimates.F
