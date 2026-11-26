module

public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
public import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedFDerivSubApply
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter

namespace GlobalTheory.CompanionTheory.SchwartzBaire

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_sub_apply' (f g : 𝓢(E, F)) (l : ℕ) (x : E) :
    iteratedFDeriv ℝ l (⇑(f - g)) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x := by
  have h : (⇑(f - g) : E → F) = ⇑f - ⇑g := by
    ext x
    simp
  rw [h]
  exact iteratedFDeriv_sub_apply (f.smooth l).contDiffAt (g.smooth l).contDiffAt

theorem cauchy_weighted (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) (k l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖ ≤ ε := by
  have h0 := hf.tendsto_uniformity
  rw [uniformity_eq_comap_nhds_zero 𝓢(E, F), tendsto_comap_iff] at h0
  have h1 := ((schwartz_withSeminorms ℝ E F).tendsto_nhds _ 0).1 h0 (k, l) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h1
  refine ⟨max N₁ N₂, fun m hm m' hm' x => ?_⟩
  have hmm := hN (m', m) ⟨le_trans (le_max_left _ _) hm', le_trans (le_max_right _ _) hm⟩
  simp only [Function.comp_apply, Prod.map_apply, sub_zero] at hmm
  rw [← iteratedFDeriv_sub_apply']
  exact (SchwartzMap.le_seminorm ℝ k l (f m - f m') x).trans hmm.le

theorem exists_tendsto [CompleteSpace F] (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) :
    ∃ g : 𝓢(E, F), Tendsto f atTop (𝓝 g) := by
  have hpt : ∀ l x, CauchySeq (fun n => iteratedFDeriv ℝ l (f n) x) := by
    intro l x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := cauchy_weighted f hf 0 l (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn N le_rfl x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm]
    linarith
  choose G hG using fun l x => cauchySeq_tendsto_of_complete (hpt l x)
  have hlim : ∀ k l {δ : ℝ}, 0 < δ → ∃ N, ∀ m ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖ ≤ δ := by
    intro k l δ hδ
    obtain ⟨N, hN⟩ := cauchy_weighted f hf k l hδ
    refine ⟨N, fun m hm x => ?_⟩
    have ht : Tendsto (fun m' => ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖)
        atTop (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (f m) x - G l x‖)) :=
      ((tendsto_const_nhds.sub (hG l x)).norm).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m' hm' => hN m hm m' hm' x⟩)
  have hunif : ∀ l, TendstoUniformly (fun n x => iteratedFDeriv ℝ l (f n) x) (G l) atTop := by
    intro l
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hlim 0 l (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have h := hN n hn x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm, norm_sub_rev]
    linarith
  let g₀ : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x l => G l x
  have hT : HasFTaylorSeriesUpTo ((⊤ : ℕ∞) : WithTop ℕ∞) g₀ p := by
    refine ⟨fun x => rfl, fun m _ x => ?_, fun m _ => ?_⟩
    · have hU : TendstoUniformly (fun n y => (iteratedFDeriv ℝ (m + 1) (f n) y).curryLeft)
          (fun y => (G (m + 1) y).curryLeft) atTop :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).isometry.uniformContinuous.comp_tendstoUniformly
          (hunif (m + 1))
      exact hasFDerivAt_of_tendstoUniformly (f := fun n y => iteratedFDeriv ℝ m (f n) y) hU
        (fun n y => ((f n).smooth ⊤).ftaylorSeries.fderiv m (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m)) y)
        (fun y => hG m y) x
    · exact (hunif m).continuous (Frequently.of_forall fun n => ((f n).smooth m).continuous_iteratedFDeriv le_rfl)
  have hg : ∀ l x, iteratedFDeriv ℝ l g₀ x = G l x := fun l x =>
    (hT.eq_iteratedFDeriv (WithTop.coe_le_coe.2 le_top) x).symm
  have hdecay : ∀ k l : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l g₀ x‖ ≤ C := by
    intro k l
    obtain ⟨N, hN⟩ := hlim k l one_pos
    refine ⟨1 + SchwartzMap.seminorm ℝ k l (f N), fun x => ?_⟩
    rw [hg]
    have h1 := hN N le_rfl x
    have h2 := SchwartzMap.le_seminorm ℝ k l (f N) x
    have h3 : ‖G l x‖ ≤ ‖iteratedFDeriv ℝ l (f N) x‖ + ‖iteratedFDeriv ℝ l (f N) x - G l x‖ := by
      calc ‖G l x‖ = ‖iteratedFDeriv ℝ l (f N) x - (iteratedFDeriv ℝ l (f N) x - G l x)‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hxk : 0 ≤ ‖x‖ ^ k := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hxk]
  let g : 𝓢(E, F) := ⟨g₀, hT.contDiff, hdecay⟩
  have hcoe : (⇑g : E → F) = g₀ := rfl
  refine ⟨g, ?_⟩
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds _ _]
  intro i ε hε
  obtain ⟨N, hN⟩ := hlim i.1 i.2 (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with m hm
  have hb : SchwartzMap.seminorm ℝ i.1 i.2 (f m - g) ≤ ε / 2 :=
    SchwartzMap.seminorm_le_bound ℝ i.1 i.2 _ (by positivity) fun x => by
      rw [iteratedFDeriv_sub_apply', hcoe, hg]
      exact hN m hm x
  exact lt_of_le_of_lt hb (half_lt_self hε)

theorem completeSpace [CompleteSpace F] : CompleteSpace 𝓢(E, F) := by
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.complete_of_cauchySeq_tendsto fun f hf => exists_tendsto f hf

theorem baireSpace [CompleteSpace F] : BaireSpace 𝓢(E, F) := by
  have : CompleteSpace 𝓢(E, F) := completeSpace
  have : (𝓤 𝓢(E, F)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end GlobalTheory.CompanionTheory.SchwartzBaire
end

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceLine
section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceAn
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal

section General

variable {S : Type} [AddCommGroup S] [Module ℂ S]

theorem norming (q : Seminorm ℂ S) (g : S) : ∃ T : S →ₗ[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg], fun x => by simp⟩
  let f : Module.Dual ℂ (Submodule.span ℂ {g}) := (q g : ℂ) • (LinearEquiv.coord ℂ S g hg).toLinearMap
  have hf : ∀ x : Submodule.span ℂ {g}, ‖f x‖ ≤ q x := fun x => by
    have h := LinearEquiv.coord_apply_smul ℂ S g hg x
    have : q x = ‖LinearEquiv.coord ℂ S g hg x‖ * q g := by rw [← map_smul_eq_mul, h]
    rw [this]
    simp [f, mul_comm, abs_of_nonneg (apply_nonneg q g)]
  obtain ⟨T, hT, hle⟩ := Module.Dual.exists_extension_of_le_seminorm _ f hf
  refine ⟨T, ?_, hle⟩
  have := hT ⟨g, Submodule.mem_span_singleton_self g⟩
  simp only at this
  rw [this]
  simp [f, abs_of_nonneg (apply_nonneg q g), LinearEquiv.coord_self]

variable [TopologicalSpace S] [IsTopologicalAddGroup S]

def toCLM (q : Seminorm ℂ S) (hq : Continuous q) (T : S →ₗ[ℂ] ℂ) (C : ℝ) (h : ∀ x, ‖T x‖ ≤ C * q x) : S →L[ℂ] ℂ :=
  ⟨T, continuous_of_continuousAt_zero T (by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm h ?_
    have := (hq.tendsto 0).const_mul C
    simpa using this)⟩

theorem norming' (q : Seminorm ℂ S) (hq : Continuous q) (g : S) : ∃ T : S →L[ℂ] ℂ, ‖T g‖ = q g ∧ ∀ x, ‖T x‖ ≤ q x := by
  obtain ⟨T, h1, h2⟩ := norming q g
  exact ⟨toCLM q hq T 1 (by simpa using h2), h1, h2⟩

def Sy (_ : Seminorm ℂ S) : Type := S

instance (q : Seminorm ℂ S) : AddCommGroup (Sy q) := inferInstanceAs (AddCommGroup S)
instance (q : Seminorm ℂ S) : Module ℂ (Sy q) := inferInstanceAs (Module ℂ S)
instance (q : Seminorm ℂ S) : SeminormedAddCommGroup (Sy q) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := Sy q) q.toAddGroupSeminorm
instance (q : Seminorm ℂ S) : NormedSpace ℂ (Sy q) := ⟨fun a x => (map_smul_eq_mul q a x).le⟩

theorem weak_bounded {ι : Type} (g : ι → S) (h : ∀ T : S →L[ℂ] ℂ, ∃ C, ∀ i, ‖T (g i)‖ ≤ C) (q : Seminorm ℂ S) (hq : Continuous q) :
    ∃ C, ∀ i, q (g i) ≤ C := by
  let e : ι → (Sy q →L[ℂ] ℂ) →L[ℂ] ℂ := fun i => ContinuousLinearMap.apply ℂ ℂ (g i : Sy q)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := e) fun f =>
    h (toCLM q hq (f : Sy q →ₗ[ℂ] ℂ) ‖f‖ fun x => f.le_opNorm x)
  refine ⟨max C 0, fun i => ?_⟩
  obtain ⟨T, h1, h2⟩ := norming q (g i)
  let f : Sy q →L[ℂ] ℂ := LinearMap.mkContinuous (E := Sy q) T 1 fun x => by rw [one_mul]; exact h2 x
  have hf : ‖f‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc q (g i) = ‖e i f‖ := h1.symm
    _ ≤ ‖e i‖ * ‖f‖ := (e i).le_opNorm f
    _ ≤ max C 0 * 1 := mul_le_mul ((hC i).trans (le_max_left _ _)) hf (norm_nonneg _) (le_max_right _ _)
    _ = _ := mul_one _

end General

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

theorem equicont {ι : Type} (T : ι → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ)) (q : Seminorm ℂ 𝓢(V₁, ℂ)) (hq : Continuous q)
    (h : ∀ f, ∃ C, ∀ i, q (T i f) ≤ C) : ∃ p : Seminorm ℂ 𝓢(V, ℂ), Continuous p ∧ ∀ i f, q (T i f) ≤ p f := by
  haveI := GlobalTheory.CompanionTheory.SchwartzBaire.baireSpace (E := V) (F := ℂ)
  have hb : BddAbove (range fun i => q.comp (T i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f
    obtain ⟨C, hC⟩ := h f
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩
  refine ⟨⨆ i, q.comp (T i).toLinearMap, ?_, fun i f => ?_⟩
  · rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup (fun i => q.comp (T i).toLinearMap) (fun i => hq.comp (T i).continuous) hb
  exact (le_ciSup hb i : q.comp (T i).toLinearMap ≤ _) f

theorem cont_seminorm (k n : ℕ) : Continuous (SchwartzMap.seminorm ℂ k n : 𝓢(V, ℂ) → ℝ) :=
  (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)

def derAt (n : ℕ) (x : V) : 𝓢(V, ℂ) →L[ℂ] (V [×n]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => iteratedFDeriv ℝ n f x)
    (fun f g => by
      have hf : ContDiff ℝ n f := f.smooth'.of_le (by exact_mod_cast le_top)
      have hg : ContDiff ℝ n g := g.smooth'.of_le (by exact_mod_cast le_top)
      exact iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt)
    (fun a f => by
      have hf : ContDiff ℝ n f := f.smooth'.of_le (by exact_mod_cast le_top)
      exact iteratedFDeriv_const_smul_apply hf.contDiffAt)
    ⟨{(0, n)}, 1, zero_le_one, fun f => by simpa using f.norm_iteratedFDeriv_le_seminorm ℂ n x⟩

theorem strong_of_weak [FiniteDimensional ℝ V] {K : Type} [TopologicalSpace K] (g : K → 𝓢(V, ℂ))
    (hw : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, Continuous fun k => T (g k))
    (hb : ∀ q : Seminorm ℂ 𝓢(V, ℂ), Continuous q → ∃ C, ∀ k, q (g k) ≤ C) : Continuous g := by
  have hd : ∀ n x, Continuous fun k => iteratedFDeriv ℝ n (g k) x := fun n x => by
    haveI : Module.Finite ℝ (V [×n]→L[ℝ] ℂ) :=
      Module.Finite.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
        ContinuousMultilinearMap.toMultilinearMap_injective
    haveI : Module.Finite ℂ (V [×n]→L[ℝ] ℂ) := Module.Finite.of_restrictScalars_finite ℝ ℂ _
    let b := (Module.finBasis ℂ (V [×n]→L[ℝ] ℂ)).equivFunL
    have : Continuous fun k => b (derAt n x (g k)) := continuous_pi fun i =>
      hw ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ => ℂ) i).comp (b.toContinuousLinearMap.comp (derAt n x)))
    refine (b.symm.continuous.comp this).congr fun k => ?_
    exact b.symm_apply_apply _
  refine continuous_iff_continuousAt.2 fun k₀ => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ V ℂ).tendsto_nhds]
  rintro ⟨j, n⟩ ε hε
  obtain ⟨C₁, h₁⟩ := hb _ (cont_seminorm (j + 1) n)
  obtain ⟨C₂, h₂⟩ := hb _ (cont_seminorm 0 (n + 1))
  have c₁ : 0 ≤ C₁ := (apply_nonneg _ _).trans (h₁ k₀)
  have c₂ : 0 ≤ C₂ := (apply_nonneg _ _).trans (h₂ k₀)
  set R : ℝ := 4 * C₁ / ε + 1 with hR
  have R1 : 1 ≤ R := by have : 0 ≤ 4 * C₁ / ε := by positivity
                        linarith
  set η : ℝ := ε / 4 / R ^ j with hη
  have η0 : 0 < η := by positivity
  set δ : ℝ := η / (2 * C₂ + 1) with hδ
  have δ0 : 0 < δ := by positivity
  obtain ⟨t, -, tf, ht⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : V) R) δ0
  have hev : ∀ᶠ k in 𝓝 k₀, ∀ x ∈ t, ‖iteratedFDeriv ℝ n (g k - g k₀) x‖ < η := by
    rw [eventually_all_finite tf]
    intro x _
    have := ((hd n x).tendsto k₀).eventually (Metric.ball_mem_nhds _ η0)
    filter_upwards [this] with k hk
    have e := GlobalTheory.CompanionTheory.SchwartzBaire.iteratedFDeriv_sub_apply' (g k) (g k₀) n x
    rw [e, ← dist_eq_norm]
    exact hk
  filter_upwards [hev] with k hk
  refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ j n _ (half_pos hε).le fun x => ?_) (half_lt_self hε)
  have s1 : ∀ a b, SchwartzMap.seminorm ℂ a b (g k - g k₀) ≤
      SchwartzMap.seminorm ℂ a b (g k) + SchwartzMap.seminorm ℂ a b (g k₀) := fun a b => map_sub_le_add _ _ _
  by_cases hx : ‖x‖ ≤ R
  · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_closedBall_zero_iff.2 hx))
    have hs : ContDiff ℝ (n + 1 : ℕ) (g k - g k₀ : 𝓢(V, ℂ)) := (g k - g k₀).smooth'.of_le (by exact_mod_cast le_top)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ))) :=
      hs.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n)
    have hl := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (C := 2 * C₂)
      (fun z _ => hdiff z) (fun z _ => by
        rw [norm_fderiv_iteratedFDeriv]
        have := (g k - g k₀).norm_iteratedFDeriv_le_seminorm ℂ (n + 1) z
        linarith [s1 0 (n + 1), h₂ k, h₂ k₀]) convex_univ (mem_univ y) (mem_univ x)
    have hd' : ‖x - y‖ ≤ δ := by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hxy).le
    have e1 : 2 * C₂ * ‖x - y‖ ≤ η := by
      calc 2 * C₂ * ‖x - y‖ ≤ (2 * C₂ + 1) * δ := by gcongr; linarith
        _ = η := by rw [hδ]; field_simp
    have e2 : ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖ ≤ 2 * η := by
      have := norm_le_insert' (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x) (iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) y)
      have h3 : ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) y‖ < η := hk y hy
      linarith
    calc ‖x‖ ^ j * ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖ ≤ R ^ j * (2 * η) := by gcongr
      _ = ε / 2 := by rw [hη]; field_simp; ring
  · push Not at hx
    have h4 := (g k - g k₀).le_seminorm ℂ (j + 1) n x
    have h5 : ‖x‖ * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (g k - g k₀ : 𝓢(V, ℂ)) x‖) ≤ 2 * C₁ := by
      rw [← mul_assoc, ← pow_succ']
      linarith [s1 (j + 1) n, h₁ k, h₁ k₀]
    have h6 : 2 * C₁ ≤ ‖x‖ * (ε / 2) := by
      have : 4 * C₁ / ε ≤ ‖x‖ := by linarith
      rw [div_le_iff₀ hε] at this
      linarith
    exact le_of_mul_le_mul_left (h5.trans h6) (by linarith)

def evAt (x : V) : 𝓢(V, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f x) (fun _ _ => rfl) (fun _ _ => rfl)
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by simpa using f.norm_le_seminorm ℂ x⟩

theorem evAt_apply (x : V) (f : 𝓢(V, ℂ)) : evAt x f = f x := rfl

theorem eq_of_weak {f g : 𝓢(V, ℂ)} (h : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, T f = T g) : f = g :=
  SchwartzMap.ext fun x => h (evAt x)

theorem weak_op {α : Type} [MeasurableSpace α] (μ : Measure α) (G : α → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ))
    (hex : ∀ f, ∃ g : 𝓢(V₁, ℂ), ∀ T : 𝓢(V₁, ℂ) →L[ℂ] ℂ, Integrable (fun a => T (G a f)) μ ∧ T g = ∫ a, T (G a f) ∂μ)
    (hb : ∀ k j : ℕ, ∃ (p : Seminorm ℂ 𝓢(V, ℂ)) (h : α → ℝ), Continuous p ∧ Integrable h μ ∧
      ∀ a f, SchwartzMap.seminorm ℂ k j (G a f) ≤ p f * h a) :
    ∃ L : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ), ∀ f (T : 𝓢(V₁, ℂ) →L[ℂ] ℂ), Integrable (fun a => T (G a f)) μ ∧ T (L f) = ∫ a, T (G a f) ∂μ := by
  choose g hg using hex
  let L : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V₁, ℂ) :=
    { toFun := g
      map_add' := fun a b => eq_of_weak fun T => by
        rw [map_add (f := _), (hg _ T).2, (hg _ T).2, (hg _ T).2, ← integral_add (hg _ T).1 (hg _ T).1]
        simp
      map_smul' := fun c a => eq_of_weak fun T => by
        rw [map_smul, (hg _ T).2, (hg _ T).2, ← integral_smul]
        simp }
  refine ⟨⟨L, ?_⟩, hg⟩
  refine (schwartz_withSeminorms ℂ V₁ ℂ).continuous_of_continuous_comp L fun i => ?_
  obtain ⟨p, h, hp, hh, hle⟩ := hb i.1 i.2
  refine Seminorm.continuous_of_le (p := (schwartzSeminormFamily ℂ V₁ ℂ i).comp L) (q := (∫ a, h a ∂μ).toNNReal • p)
    (hp.const_smul _) fun f => ?_
  obtain ⟨T, h1, h2⟩ := norming' _ (cont_seminorm (V := V₁) i.1 i.2) (g f)
  change SchwartzMap.seminorm ℂ i.1 i.2 (g f) ≤ ((∫ a, h a ∂μ).toNNReal : ℝ) * p f
  rw [← h1, (hg f T).2]
  calc ‖∫ a, T (G a f) ∂μ‖ ≤ ∫ a, p f * h a ∂μ :=
        norm_integral_le_of_norm_le (hh.const_mul _) (Eventually.of_forall fun a => (h2 _).trans (hle a f))
    _ = (∫ a, h a ∂μ) * p f := by rw [integral_const_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (apply_nonneg _ _)

end PositivityTheory.ThKG.Loc.Bump

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKCT PositivityTheory.ThKF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Basic

variable {κ : Type} [Fintype κ]

theorem rest_fin (f : SInf F κ) {ψ : (κ → Af F) → ℂ} (hψ : ψ ∈ SB (κ → Af F)) :
    Rest (evI F) f fun x => ψ fun i => (x i).2 := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, ψ, hψ, rfl⟩⟩
  have key : ∀ i, (z i).2 = 0 := fun i => by
    have h := congrFun (hz ((0, 1) : AF F) (evI_eq_zero.2 rfl)) i
    exact (one_mul _).symm.trans (congrArg Prod.snd h)
  refine congrArg ψ (funext fun i => ?_)
  show (x i).2 + (z i).2 = _
  rw [key, add_zero]

theorem acts_pureA {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : Acts (evI F) S f f₁)
    {ψ : (κ → Af F) → ℂ} (hψ : ψ ∈ SB (κ → Af F)) : S (pureA F f ψ) = pureA F f₁ ψ := h _ (rest_fin f hψ)

theorem opI_eq (hU : ArchUniq) {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ} (h : Acts (evI F) S f f₁) :
    opI S f = f₁ := by
  have e : ∃ f₁ : SInf F κ, Acts (evI F) S f f₁ := ⟨f₁, h⟩
  rw [opI, dite_eq_left e]
  exact (hU F κ f _ _).1 S e.choose_spec h

def ptA (y : κ → mixedEmbedding.mixedSpace F) (a : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), a i)

theorem pureA_ptA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y a) :
    pureA F f g (ptA y a) = f y * g a := by
  simp only [pureA, ptA, RingEquiv.apply_symm_apply]

theorem norm_ext (h : IsCMExt F E σ) (w : InfinitePlace F) (a : AF F) :
    ‖InfinitePlace.Completion.extensionEmbedding w (a.1 w)‖ = mixedEmbedding.normAtPlace w (evI F a) := by
  have := h.1
  have hw := IsTotallyReal.isReal w
  rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    Complex.norm_real]
  rfl

end Basic

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem vac_fin {M : Model σ X W} (hM : M.IsGood B.ψ) : ∃ ψ ∈ SB (Fin n × Fin d → Af F), (∃ a, ψ a ≠ 0) ∧
    ∀ f : SInf F (Fin n × Fin d), pure f M.vac = pureA F f ψ := by
  obtain ⟨ψ, h1, h2⟩ := (pureAct F _ B.v₁ id 0 M.vac (fun v => (hM.vac v).1) hM.std).1
  refine ⟨ψ, h1, ?_, h2⟩
  obtain ⟨f, hf⟩ : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    classical
    let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := default
    have hcs : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    refine ⟨hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), fun h => ?_⟩
    have : ((b 0 : ℝ) : ℂ) = 0 := congrArg (fun g : SInf F (Fin n × Fin d) => g 0) h
    simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)] at this
  by_contra hc
  push Not at hc
  refine pure_ne_zero f hf M.vac (fun v => (hM.vac v).2.1) hM.std ?_
  rw [h2]
  funext x
  simp [pureA, hc]

theorem hTens_vec {R : Type} [CommRing R] [Algebra (AF F) R] (c : R →ₐ[AF F] R) (JA : Matrix (Fin n) (Fin n) R)
    (JB : Matrix (Fin d) (Fin d) R) (s t : R) (a a' : Fin n → R) (b b' : Fin d → R) :
    hTens c JA JB (s • Matrix.vecMulVec a b) (t • Matrix.vecMulVec a' b') =
      s * c t * (PositivityTheory.Mix.bf c.toRingHom JA a a' * PositivityTheory.Mix.bf c.toRingHom JB b b') := by
  simp only [hTens, PositivityTheory.Mix.bf, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul,
    Finset.sum_mul, Finset.mul_sum, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have e : ∀ (g : Fin n → Fin d → Fin n → Fin d → R), ∑ i, ∑ j, ∑ k, ∑ l, g i j k l = ∑ j, ∑ l, ∑ i, ∑ k, g i j k l := fun g => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_comm (f := fun i l => ∑ k, g i j k l)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [e]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem incM_smul_vec (s : E) (x : Fin n → E) (y : Fin d → E) :
    incM F (s • Matrix.vecMulVec x y) = inclR (F := F) (AF F) s • Matrix.vecMulVec (incV F x) (incV F y) := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply]

theorem exists_dual (hB : B.IsGood σ) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (x x' : Fin n → E) (y y' : Fin d → E)
    (hI : ∀ a : AE F E, a • Matrix.vecMulVec (incV F x') (incV F y') ∈ I) (h0 : form σ X.J x' x * form σ W.J y' y ≠ 0) :
    ∃ (m : ℕ) (u z : Fin m → Matrix (Fin n) (Fin d) E) (b : Fin m → E) (Y : Fin m → AE F E →ₗ[AF F] AF F),
      Dual σ X W I u z ∧ (∀ a, ∑ j, Y j a • inclR (F := F) (AF F) (b j) = a) ∧
      ∀ a, lin u (fun j => Y j a) = a • Matrix.vecMulVec (incV F x) (incV F y) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set t : E := -(form σ X.J x' x * form σ W.J y' y) with ht
  have t0 : t ≠ 0 := neg_ne_zero.2 h0
  let b' := Module.finBasis F E
  let b : Fin _ → E := fun j => σ (t⁻¹ * b' j)
  let Y : Fin _ → AE F E →ₗ[AF F] AF F := fun j => (Algebra.trace (AF F) (AE F E)) ∘ₗ
    (LinearMap.mulLeft (AF F) (inclR (F := F) (AF F) (b'.traceDual j * t))) ∘ₗ (cA σ).toLinearMap
  have tr1 : ∀ a : E, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) a) = algebraMap F (AF F) (Algebra.trace F E a) :=
    fun a => (trace_tmul 1 a).trans (one_mul _)
  have hY : ∀ a, ∑ j, Y j a • inclR (F := F) (AF F) (b j) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, hp, hq]
    | tmul r x =>
      have e : (r ⊗ₜ[F] x : AE F E) = r • inclR (F := F) (AF F) x := by
        change _ = r • ((1 : AF F) ⊗ₜ[F] x); rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e1 : ∀ j, Y j (inclR (F := F) (AF F) x) = algebraMap F (AF F) (Algebra.trace F E (b'.traceDual j * t * σ x)) := fun j => by
        rw [← tr1, map_mul (inclR (F := F) (AF F)) _ (σ x)]; rfl
      have e2 : ∑ j, Algebra.trace F E (b'.traceDual j * t * σ x) • b j = x := by
        have h1 := b'.sum_repr (t * σ x)
        have h2 : ∀ j, b'.repr (t * σ x) j = Algebra.trace F E (b'.traceDual j * t * σ x) := fun j => by
          have := b'.traceDual.traceDual_repr_apply (t * σ x) j
          rw [Module.Basis.traceDual_traceDual] at this
          rw [this, Algebra.traceForm_apply, mul_comm, mul_assoc]
        have h3 : σ (t⁻¹ * (t * σ x)) = x := by rw [inv_mul_cancel_left₀ t0, PositivityTheory.Mix.conj_conj hB]
        conv_rhs => rw [← h3, ← h1]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [h2, Finset.mul_sum, map_sum, mul_smul_comm, b]
        exact Finset.sum_congr rfl fun j _ => (σ.toLinearMap.map_smul _ _).symm
      rw [e]
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, e1]
      congr 1
      conv_rhs => rw [← e2]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change _ = (1 : AF F) ⊗ₜ[F] (_ • b j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]; rfl
  refine ⟨_, fun j => b j • Matrix.vecMulVec x y, fun j => b'.traceDual j • Matrix.vecMulVec x' y', b, Y, ⟨fun j a => ?_, fun i j => ?_⟩,
    hY, fun a => ?_⟩
  · rw [incM_smul_vec, ← smul_assoc]; exact hI _
  · change Algebra.trace _ _ _ = _
    rw [incM_smul_vec, incM_smul_vec, hTens_vec, PositivityTheory.Mix.bf_inc, PositivityTheory.Mix.bf_inc, PositivityTheory.Mix.cA_inc, PositivityTheory.Mix.conj_conj hB,
      ← map_mul, ← map_mul, ← map_mul, neg_one_mul, ← map_neg, tr1]
    have : -(b'.traceDual i * (t⁻¹ * b' j) * (form σ X.J x' x * form σ W.J y' y)) = b'.traceDual i * b' j := by
      have : form σ X.J x' x * form σ W.J y' y = -t := by rw [ht, neg_neg]
      rw [this]; field_simp
    rw [this, Module.Basis.trace_traceDual_mul]
    by_cases h : i = j <;> simp [h, eq_comm]
  · conv_rhs => rw [← hY a]
    simp only [lin, incM_smul_vec, Finset.sum_smul, smul_assoc]

theorem form_ne (hB : B.IsGood σ) {k : ℕ} {H : Plane E n k} {ε : AE F E}
    (h : PositivityTheory.Mix.PlaneOK (cA σ).toRingHom (incM F X.J) ε (incV F H.x) (incV F H.y) (incM F H.ι)) : form σ X.J H.y H.x ≠ 0 := by
  intro h0
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h1 := h.yx
  rw [PositivityTheory.Mix.bf_inc, h0, map_zero] at h1
  have := congrArg (piInf (B.emb w)) h.ee
  rw [← h1] at this
  simp at this

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
  {u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)} {ei ev}

theorem at_smul {a : AE F E} (ha : At (evI F) a) (v : Matrix (Fin n) (Fin d) (AE F E)) : At (evI F) (a • v) :=
  fun s hs => by rw [← smul_assoc, ha s hs, zero_smul]

theorem ev_op (hH : ArchHeis) (hU : ArchUniq) (hB : B.IsGood σ) (hl : IsEvLoc M M₁ e ei ev) {ψ ψ₁} (hψ : ψ ∈ SB (Fin n × Fin d → Af F))
    (hM : M.IsGood B.ψ) (h : ∀ f : SInf F (Fin n × Fin d), pure f M.vac = pureA F f ψ)
    (h₁ : ∀ f : SInf F (Fin n₁ × Fin d₁), pure f M₁.vac = pureA F f ψ₁) {s} (hs : At (evI F) s) (f : SInf F (Fin n × Fin d)) :
    e (M.co.rho B.ψ s (pureA F f ψ)) = pureA F (ei (opI (M.co.rho B.ψ s) f)) ψ₁ := by
  obtain ⟨f₁, hf⟩ := (hH F E σ B n d X W M hB).2 s hs f
  rw [opI_eq hU hf, acts_pureA hf hψ, ← h, hl.pure f₁ M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl), ← h₁]
  congr 1
  funext v
  exact (hl.vac v).1

theorem line_ex (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hc : Cfg B M M₁ H H' e u) (hl : IsEvLoc M M₁ e ei ev) {lift}
    (hL : IsLift σ B lift) : ∃ A : (InfinitePlace F → ℂ) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      (∀ f, Continuous fun c => A c f) ∧ (∀ c f, A c f = ei (opI (M.co.rho B.ψ (lift c • u 1)) f)) ∧
      ∀ (q : Seminorm ℂ (SInf F (Fin n₁ × Fin d₁))) (N : ℕ), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)),
        Continuous p ∧ ∀ c f, q (A c f) * (1 + ‖c‖) ^ N ≤ p f := by
  have hB := hc.base
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨r', s', hW⟩ := hc.skew
  obtain ⟨i, j, hP⟩ := hc.hH
  obtain ⟨i', j', hP'⟩ := hc.hH'
  obtain ⟨ε, oX⟩ := PositivityTheory.Mix.planeOK_herm hB hP hX
  obtain ⟨ε', oW⟩ := PositivityTheory.Mix.planeOK_skew hB hP' hW
  obtain ⟨I, hI, m, uu, z, b, Y, hD, hY, hlin⟩ : ∃ I, IsEv B M M₁ H.ι H'.ι I e ∧
      ∃ (m : ℕ) (uu z : Fin m → Matrix (Fin n) (Fin d) E) (b : Fin m → E) (Y : Fin m → AE F E →ₗ[AF F] AF F),
      Dual σ X W I uu z ∧ (∀ a, ∑ j, Y j a • inclR (F := F) (AF F) (b j) = a) ∧ ∀ a, lin uu (fun j => Y j a) = a • u 1 := by
    rcases hc.ev with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · refine ⟨_, h, ?_⟩
      have := exists_dual (X := X) (W := W) hB (isoA H H') H.x H.y H'.y H'.x
        (fun a => Or.inl ⟨a • incV F H.y, by rw [Matrix.smul_vecMulVec]⟩) (by rw [hP'.xy, mul_one]; exact form_ne hB oX)
      simpa only [shiftA, Units.val_one, one_smul] using this
    · refine ⟨_, h, ?_⟩
      have := exists_dual (X := X) (W := W) hB (isoB H H') H.y H.x H'.x H'.y
        (fun a => Or.inl ⟨a • incV F H'.y, by rw [Matrix.vecMulVec_smul]⟩) (by rw [hP.xy, one_mul]; exact form_ne hB oW)
      simpa only [shiftB, Units.val_one, map_one, one_smul] using this
  obtain ⟨ψ, hψ, -, hp⟩ := vac_fin hc.good
  obtain ⟨ψ₁, -, ⟨a, ha⟩, hp₁⟩ := vac_fin hc.good₁
  obtain ⟨k, φ₁, C, A, -, -, hcont, hid, -, hdec⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hc.good hc.good₁ _ _ I e hI m uu z hD ψ hψ
  have hlc : Continuous lift := by
    have : lift = lft hB.cm B.emb := funext fun c => by
      apply ext_at hB.cm B.emb
      · intro v; rw [fin_of_at (hL.supp c), fin_lft]
      · intro w; rw [hL.pi, pi_lft]
    rw [this]; exact cont_lft _ _
  have hYc : Continuous fun c j => Y j (lift c) :=
    continuous_pi fun j => (IsModuleTopology.continuous_of_linearMap (Y j)).comp hlc
  refine ⟨fun c => ∑ i, (φ₁ i a / ψ₁ a) • A i fun j => Y j (lift c), fun f => ?_, fun c f => ?_, fun q N hq => ?_⟩
  · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    exact continuous_finsetSum _ fun i _ => ((hcont i f).comp hYc).const_smul (φ₁ i a / ψ₁ a)
  · have h1 := hid (fun j => Y j (lift c)) f
    rw [hlin, ev_op hH hU hB hl hψ hc.good hp hp₁ (at_smul (hL.supp c) _)] at h1
    refine SchwartzMap.ext fun y => ?_
    have h2 := congrFun h1 (ptA y a)
    simp only [Finset.sum_apply, pureA_ptA] at h2
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply,
      smul_eq_mul]
    rw [eq_div_of_mul_eq ha h2, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  · obtain ⟨p, hp', hq'⟩ := hdec q N hq
    set K : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ with hK
    have K1 : 1 ≤ K := le_add_of_nonneg_right (by positivity)
    refine ⟨(NNReal.mk ((∑ i, ‖φ₁ i a / ψ₁ a‖) * K ^ N) (by positivity)) • p, hp'.const_smul _, fun c f => ?_⟩
    set Sg : ℝ := ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (Y j (lift c))) with hSg
    have S0 : 0 ≤ Sg := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
    have hn : ‖c‖ ≤ K * Sg := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hL.pi c w, ← hY (lift c), map_sum, hSg, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      have e1 : Y j (lift c) • inclR (F := F) (AF F) (b j) = (Y j (lift c) ⊗ₜ[F] b j : AE F E) := by
        change _ • ((1 : AF F) ⊗ₜ[F] b j) = _; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, pi_tmul, norm_mul, norm_ext hB.cm, mul_comm]
      refine mul_le_mul ?_ (Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (Y j (lift c))))
        (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)) (mixedEmbedding.normAtPlace_nonneg _ _) (by linarith)
      have h1 : ‖(B.emb w).1 (b j)‖ ≤ ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ :=
        Finset.single_le_sum (f := fun w => ‖(B.emb w).1 (b j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      have h2 : ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ ≤ ∑ j, ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖ :=
        Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, ‖(B.emb w).1 (b j)‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      linarith
    have hw : (1 + ‖c‖) ^ N ≤ K ^ N * (1 + Sg) ^ N := by
      rw [← mul_pow]; gcongr; nlinarith
    have hs : q ((∑ i, (φ₁ i a / ψ₁ a) • A i fun j => Y j (lift c)) f) ≤ ∑ i, ‖φ₁ i a / ψ₁ a‖ * q (A i (fun j => Y j (lift c)) f) := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans (le_of_eq ?_)
      simp only [map_smul_eq_mul]
    change _ ≤ (∑ i, ‖φ₁ i a / ψ₁ a‖) * K ^ N * p f
    calc _ ≤ (∑ i, ‖φ₁ i a / ψ₁ a‖ * q (A i (fun j => Y j (lift c)) f)) * (K ^ N * (1 + Sg) ^ N) :=
          mul_le_mul hs hw (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg _ _))
      _ = ∑ i, ‖φ₁ i a / ψ₁ a‖ * K ^ N * (q (A i (fun j => Y j (lift c)) f) * (1 + Sg) ^ N) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, ‖φ₁ i a / ψ₁ a‖ * K ^ N * p f := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq' i _ f) (by positivity)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end PositivityTheory.ThKG.Loc.Bump

end
end

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKCT PositivityTheory.ThKF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pureA_mem' {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem exists_admissible_functional_adelic {κ : Type} [Fintype κ] (L : SInf F κ →L[ℂ] ℂ) (a : κ → Af F) : ∃ l ∈ (adeleClass F).adm κ,
    ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), l (pureA F f g) = g a * L f := by
  have ex : ∀ Φ : schA F κ, ∃ f : SInf F κ, ∀ y, f y = Φ.1 (ptA y a) := by
    rintro ⟨Φ, hΦ⟩
    induction hΦ using Submodule.span_induction with
    | mem _ h => obtain ⟨f, g, -, rfl⟩ := h; exact ⟨g a • f, fun y => (mul_comm _ _).trans (pureA_ptA f g y a).symm⟩
    | zero => exact ⟨0, fun _ => rfl⟩
    | add _ _ _ _ p q => obtain ⟨p, hp⟩ := p; obtain ⟨q, hq⟩ := q; exact ⟨p + q, fun y => by rw [SchwartzMap.add_apply, hp, hq]; rfl⟩
    | smul c _ _ p => obtain ⟨p, hp⟩ := p; exact ⟨c • p, fun y => by rw [SchwartzMap.smul_apply, hp]; rfl⟩
  choose s hs using ex
  let s' : schA F κ →ₗ[ℂ] SInf F κ :=
    { toFun := s
      map_add' := fun a b => SchwartzMap.ext fun z => by rw [SchwartzMap.add_apply, hs, hs, hs]; rfl
      map_smul' := fun c a => SchwartzMap.ext fun z => by rw [SchwartzMap.smul_apply, hs, hs]; rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (L.toLinearMap ∘ₗ s')
  have h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), l (pureA F f g) = g a * L f := fun f g hg => by
    have h1 := LinearMap.congr_fun hl ⟨_, pureA_mem' f hg⟩
    have h2 : s ⟨_, pureA_mem' f hg⟩ = g a • f := SchwartzMap.ext fun z => by
      rw [hs]; exact (pureA_ptA f g z a).trans (mul_comm _ _)
    refine h1.trans ?_
    show L (s _) = _
    rw [h2, map_smul, smul_eq_mul]
  exact ⟨l, fun g hg => ⟨g a • L, fun f => h f g hg⟩, h⟩

theorem joint_cont {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
    {K C : Type} [TopologicalSpace K] [TopologicalSpace C] (A : C → SchwartzMap V ℂ →L[ℂ] SchwartzMap V₁ ℂ)
    (hA : ∀ g, Continuous fun c => A c g)
    (hb : ∀ q : Seminorm ℂ (SchwartzMap V₁ ℂ), Continuous q → ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ c g, q (A c g) ≤ p g)
    (g : K → SchwartzMap V ℂ) (hg : Continuous g) : Continuous fun x : K × C => A x.2 (g x.1) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ V₁ ℂ).tendsto_nhds]
  intro i ε hε
  have hq := (schwartz_withSeminorms ℂ V₁ ℂ).continuous_seminorm i
  obtain ⟨p, hp, hle⟩ := hb _ hq
  have c1 : Continuous fun x : K × C => p (g x.1 - g x₀.1) + schwartzSeminormFamily ℂ V₁ ℂ i (A x.2 (g x₀.1) - A x₀.2 (g x₀.1)) :=
    (hp.comp ((hg.comp continuous_fst).sub continuous_const)).add (hq.comp (((hA _).comp continuous_snd).sub continuous_const))
  have := (c1.tendsto x₀).eventually (gt_mem_nhds (a := ε) (by simpa using hε))
  filter_upwards [this] with x hx
  refine lt_of_le_of_lt ?_ hx
  have e : A x.2 (g x.1) - A x₀.2 (g x₀.1) = A x.2 (g x.1 - g x₀.1) + (A x.2 (g x₀.1) - A x₀.2 (g x₀.1)) := by
    rw [map_sub]; abel
  rw [e]
  exact (map_add_le_add _ _ _).trans (add_le_add_left (hle _ _) _)

theorem dom_int {ι : Type} [Fintype ι] (z : ℕ) : ∃ N : ℕ,
    Integrable (fun c : ι → ℂ => (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ N) ∧ 0 < ∫ c : ι → ℂ, (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ N := by
  set a := 2 * Fintype.card ι * z
  set b := Module.finrank ℝ (ι → ℂ) + 1
  have hc : Continuous fun c : ι → ℂ => (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ (a + b) :=
    Continuous.div₀ (by fun_prop) (by fun_prop) fun c => by positivity
  have hi : Integrable fun c : ι → ℂ => (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ (a + b) := by
    refine (integrable_one_add_norm (μ := volume) (r := b) (by simp [b])).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, pow_add, ← div_div,
      div_eq_mul_inv]
    refine mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).2 ?_)
    have : ∏ w, ‖c w‖ ^ 2 ≤ ∏ _w : ι, (1 + ‖c‖) ^ 2 :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => by
        have := norm_le_pi_norm c w
        gcongr; linarith
    calc _ ≤ (∏ _w : ι, (1 + ‖c‖) ^ 2) ^ z := by gcongr
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul, ← pow_mul, ← mul_assoc]
  exact ⟨a + b, hi, integral_pos_of_integrable_nonneg_nonzero (x := 1) hc hi (fun c => by positivity) (by simp; positivity)⟩

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem xi_int {lift} (hL : IsLift σ B lift) (x : @Measure (idAt E (evI F)) (borel _))
    (hx : @Measure.IsHaarMeasure _ _ _ (borel _) x) (z : ℕ) (hz : 1 ≤ z) : ∃ N : ℕ, @Integrable _ _ _ _ (borel _)
      (fun t : idAt E (evI F) => (∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2) ^ z / (1 + ‖fun w => piInf (B.emb w) (t.1 : AE F E)‖) ^ N) x := by
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le' hz
  obtain ⟨N, hi, hp⟩ := dom_int (ι := InfinitePlace F) z
  obtain ⟨κ, hκ, h⟩ := hL.haar x hx
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  refine ⟨N, ?_⟩
  have h1 := h fun c => (((∏ w, ‖c w‖ ^ 2) ^ (z + 1) / (1 + ‖c‖) ^ N : ℝ) : ℂ)
  have h2 : ∫ c : InfinitePlace F → ℂ, (((∏ w, ‖c w‖ ^ 2) ^ (z + 1) / (1 + ‖c‖) ^ N : ℝ) : ℂ) * ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ)⁻¹ =
      ((∫ c : InfinitePlace F → ℂ, (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ N : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun w => Measure.ae_eval_ne (fun _ : InfinitePlace F => (volume : Measure ℂ)) w 0] with c hc
    have : (∏ w, ‖c w‖ ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc w))
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [pow_succ]
    field_simp
  rw [h2, integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj] at h1
  exact Integrable.of_integral_ne_zero (by rw [h1]; positivity)

theorem mem_kAt {K : Subgroup (UA σ X.J)} {k} : k ∈ kAt K (evI F) ↔ k ∈ K ∧ k ∈ UAt σ X (evI F) := by
  have : Subgroup.closure (UAt σ X (evI F)) = atGrp σ X (evI F) := Subgroup.closure_eq (atGrp σ X (evI F))
  rw [kAt, this]; rfl

theorem kAt_cpt (hS : StabEx) (hB : B.IsGood σ) {r s} (hX : X.IsHerm σ B r s) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) :
    IsCompact (kAt K (evI F) : Set (UA σ X.J)) := by
  obtain ⟨K', -, -, h1, h2, -⟩ := hS F E σ B n X r s hB hX
  obtain rfl : K' = K := Subgroup.ext fun g => (h1 g).trans (hK g).symm
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g - 1 := (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  have hc : IsClosed {g : UA σ X.J | realAd F 1 • (mat g - 1) = mat g - 1} := by
    refine isClosed_eq ?_ hm
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.smul_apply, Algebra.smul_def]
    exact continuous_const.mul (hm.matrix_elem i j)
  have : (kAt K' (evI F) : Set (UA σ X.J)) = (K' : Set (UA σ X.J)) ∩ {g : UA σ X.J | realAd F 1 • (mat g - 1) = mat g - 1} :=
    Set.ext fun g => mem_kAt.trans (and_congr_right fun _ => at_iff)
  rw [this]
  exact h2.inter_right hc

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
  {u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)} {ei ev}

theorem k_ops (hS : StabEx) (hO : ArchOp) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {χX χW om r s r' s'}
    (hP : IsPair B M χX χW om r s r' s') : ∃ T : kAt K (evI F) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d),
      (∀ k, IsArchOp om (k.1, 1) (T k)) ∧ (∀ k, ∀ f ∈ M.Pol B.ψ B.emb, T k f ∈ M.Pol B.ψ B.emb) ∧ (∀ f, Continuous fun k => T k f) ∧
      ∀ q : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
        ∀ k f, q (T k f) ≤ p f := by
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := (atGrp σ W (evI F)).one_mem
  choose T hT hPol using fun k : kAt K (evI F) => hO F E σ B n d X W M χX χW om r s r' s' hP k.1 (mem_kAt.1 k.2).2 1 h1
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 (kAt_cpt hS hP.base hP.herm hK)
  obtain ⟨g₀, hg, ⟨a, ha⟩, -⟩ := vac_fin hP.good
  have hw : ∀ f (l : SInf F (Fin n × Fin d) →L[ℂ] ℂ), Continuous fun k => l (T k f) := fun f l => by
    obtain ⟨l', hl, hl'⟩ := exists_admissible_functional_adelic ((g₀ a)⁻¹ • l) a
    have hc := (IsUWeilPair.isUSplitting hP.weil).cont l' hl _ (pureA_mem' f hg)
    refine (hc.comp (continuous_subtype_val.prodMk (continuous_const (y := (1 : UA σ W.J))))).congr fun k => ?_
    have := (hT k).1 f g₀ hg
    exact (congrArg l' this).trans (by
      rw [hl' _ _ hg]
      exact mul_inv_cancel_left₀ ha _)
  have hb : ∀ f (q : Seminorm ℂ (SInf F (Fin n × Fin d))), Continuous q → ∃ C, ∀ k, q (T k f) ≤ C := fun f q hq =>
    weak_bounded (fun k => T k f) (fun l => by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hw f l).continuousOn
      exact ⟨C, fun k => hC k trivial⟩) q hq
  refine ⟨T, hT, fun k => hPol k ⟨(mem_kAt.1 k.2).2, ((hK _).1 (mem_kAt.1 k.2).1).1⟩ ⟨h1, fun w => ?_⟩,
    fun f => strong_of_weak _ (hw f) (hb f), fun q hq => equicont T q hq fun f => hb f q hq⟩
  rw [mat_one', Matrix.map_one _ (map_zero _) (map_one _)]
  exact Commute.one_left _

theorem op_comp (hH : ArchHeis) (hU : ArchUniq) {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') {k T}
    (hT : IsArchOp om (k, 1) T) {w} (hw : At (evI F) w) (f : SInf F (Fin n × Fin d)) :
    opI (fun Φ => M.co.rho B.ψ w (om (k, 1) Φ)) f = opI (M.co.rho B.ψ w) (T f) := by
  obtain ⟨f₁, hf⟩ := (hH F E σ B n d X W M hP.base).2 w hw (T f)
  rw [opI_eq hU hf]
  refine opI_eq hU fun r hr => ?_
  have h1 := hT.2 f r hr
  show M.co.rho B.ψ w (om (k, 1) _) = _
  rw [h1]
  exact hf r ⟨hr.1, h1 ▸ (IsUWeilPair.isUSplitting hP.weil).pres _ _ hr.2⟩

theorem shift_eq (hc : Cfg B M M₁ H H' e u) {lift} (hL : IsLift σ B lift) : ∃ cc : (AE F E)ˣ → InfinitePlace F → ℂ, Continuous cc ∧
    (∀ t w, ‖cc t w‖ = ‖piInf (B.emb w) (t : AE F E)‖) ∧ ∀ t, realAd F 1 • u t = lift (cc t) • u 1 := by
  have key : ∀ a : AE F E, lift (fun w => piInf (B.emb w) a) = realAd F 1 • a := fun a => by
    rw [← hL.inv _ (hL.part a).1]; congr 1; funext w; exact ((hL.part a).2 w).symm
  rcases hc.ev with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨fun t w => piInf (B.emb w) (t : AE F E), continuous_pi fun w => (hL.cont w).comp Units.continuous_val,
      fun _ _ => rfl, fun t => ?_⟩
    simp only [key, shiftA, Units.val_one, one_smul, smul_assoc]
  · refine ⟨fun t w => piInf (B.emb w) (cA σ (t : AE F E)), continuous_pi fun w => ?_, fun t w => ?_, fun t => ?_⟩
    · simp only [hL.conj]; exact Complex.continuous_conj.comp ((hL.cont w).comp Units.continuous_val)
    · simp only [hL.conj, Complex.norm_conj]
    · simp only [key, shiftB, Units.val_one, map_one, one_smul, smul_assoc]

theorem cone_core (hSt : StabEx) (hO : ArchOp) (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hI : SchInt)
    (hc : Cfg B M M₁ H H' e u) (hl : IsEvLoc M M₁ e ei ev) {lift} (hL : IsLift σ B lift) {K : Subgroup (UA σ X.J)} {m : LocMeas K}
    (hK : IsStab B K) (hm : m.Is) {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (ν : Chr F E) (z : ℕ)
    (hν : Continuous ν) (hz : 1 ≤ z) : ∃ L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      ∀ f (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ),
        (∀ k : kAt K (evI F), @Integrable _ _ _ _ (borel _) (fun t : idAt E (evI F) =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1) m.xi) ∧
        (Integrable (fun k : kAt K (evI F) => @integral _ _ _ _ (borel _) m.xi fun t =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1) m.ki) ∧
        l (L f) = ∫ k, @integral _ _ _ _ (borel _) m.xi (fun t =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1) ∂m.ki := by
  obtain ⟨A, hA, hAe, hAd⟩ := line_ex hS hH hU hc hl hL
  obtain ⟨T, hT, -, hTc, hTb⟩ := k_ops hSt hO hK hP
  obtain ⟨cc, hcc, hcn, hce⟩ := shift_eq hc hL
  obtain ⟨N, hN⟩ := xi_int hL m.xi hm.xi z hz
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  haveI : BorelSpace (idAt E (evI F)) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨-, h2, -⟩ := PositivityTheory.ThKEst.lcsc_UA σ X.J
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 (kAt_cpt hSt hP.base hP.herm hK)
  haveI := hm.ki
  haveI := hm.xi
  haveI : IsFiniteMeasure m.ki := ⟨isCompact_univ.measure_lt_top⟩
  haveI : SigmaFinite m.ki := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite m.ki := MeasureTheory.instSFiniteOfSigmaFinite
  have hpos : ∀ t : idAt E (evI F), 0 < (∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2) ^ z / (1 + ‖fun w => piInf (B.emb w) (t.1 : AE F E)‖) ^ N :=
    fun t => div_pos (pow_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (pi_ne _ _)) 2) _) (by positivity)
  haveI : SigmaFinite m.xi := by
    have h := hN.aefinStronglyMeasurable
    have h1 : m.xi.restrict h.sigmaFiniteSet = m.xi := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      have h2 := h.ae_eq_zero_compl
      rw [Filter.EventuallyEq, ae_restrict_iff' h.measurableSet.compl] at h2
      filter_upwards [h2] with t ht
      by_contra hn
      exact (hpos t).ne' (ht hn)
    rw [← h1]
    infer_instance
  have hab : ∀ t : idAt E (evI F), (absE F E t.1 : ℝ) = ∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2 :=
    fun t => hL.abs _ ((hL.idAt _).1 t.2)
  have hwc : Continuous fun t : idAt E (evI F) => wt ν z t.1 := by
    simp only [wt, hab]
    refine (continuous_subtype_val.comp (hν.comp continuous_subtype_val)).mul (Continuous.pow (Complex.continuous_ofReal.comp ?_) _)
    exact continuous_finsetProd _ fun w _ => ((hL.cont w).comp (Units.continuous_val.comp continuous_subtype_val)).norm.pow 2
  have hwn : ∀ t : idAt E (evI F), ‖wt ν z t.1‖ = (∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2) ^ z := fun t => by
    rw [wt, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, hab, Real.norm_of_nonneg (by positivity)]
  let G : kAt K (evI F) × idAt E (evI F) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) :=
    fun x => wt ν z x.2.1 • (A (cc x.2.1)).comp (T x.1)
  have hGc : ∀ f, Continuous fun x => G x f := fun f => by
    have h1 := joint_cont (fun t : idAt E (evI F) => A (cc t.1)) (fun g => (hA g).comp (hcc.comp continuous_subtype_val))
      (fun q hq => by
        obtain ⟨p, hp, h⟩ := hAd q 0 hq
        exact ⟨p, hp, fun c g => by simpa using h _ g⟩) _ (hTc f)
    exact (hwc.comp continuous_snd).smul h1
  have hGb : ∀ q : Seminorm ℂ (SInf F (Fin n₁ × Fin d₁)), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
      ∀ x f, q (G x f) ≤ p f * ((∏ w, ‖piInf (B.emb w) (x.2.1 : AE F E)‖ ^ 2) ^ z /
        (1 + ‖fun w => piInf (B.emb w) (x.2.1 : AE F E)‖) ^ N) := fun q hq => by
    obtain ⟨p, hp, h⟩ := hAd q N hq
    obtain ⟨p', hp', h'⟩ := hTb p hp
    refine ⟨p', hp', fun x f => ?_⟩
    have e1 : ‖cc x.2.1‖ = ‖fun w => piInf (B.emb w) (x.2.1 : AE F E)‖ := by
      simp only [Pi.norm_def]
      congr 2
      funext w
      exact NNReal.eq (hcn _ w)
    have h3 := (h (cc x.2.1) (T x.1 f)).trans (h' x.1 f)
    rw [e1, ← le_div_iff₀ (by positivity)] at h3
    change q (wt ν z x.2.1 • A (cc x.2.1) (T x.1 f)) ≤ _
    rw [map_smul_eq_mul, hwn]
    refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans (le_of_eq ?_)
    ring
  have hD : Integrable (fun x : kAt K (evI F) × idAt E (evI F) => (∏ w, ‖piInf (B.emb w) (x.2.1 : AE F E)‖ ^ 2) ^ z /
      (1 + ‖fun w => piInf (B.emb w) (x.2.1 : AE F E)‖) ^ N) (m.ki.prod m.xi) := by
    simpa using (integrable_const (μ := m.ki) (1 : ℝ)).mul_prod hN
  obtain ⟨L, hL'⟩ := weak_op (m.ki.prod m.xi) G (fun f => hI _ _ _ _ (hGc f) fun k j => by
      obtain ⟨p, -, h⟩ := hGb _ (cont_seminorm k j)
      exact (hD.const_mul (p f)).mono' ((cont_seminorm k j).comp (hGc f)).aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (apply_nonneg _ _)]; exact h x f))
    fun k j => by
      obtain ⟨p, hp, h⟩ := hGb _ (cont_seminorm k j)
      exact ⟨p, _, hp, hD, h⟩
  have hGe : ∀ f (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ) (k : kAt K (evI F)) (t : idAt E (evI F)),
      l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1 = l (G (k, t) f) := fun f l k t => by
    rw [hce, op_comp hH hU hP (hT k) (at_smul (hL.supp _) _), ← hAe, mul_comm]
    exact (map_smul l _ _).symm
  refine ⟨L, fun f l => ?_⟩
  simp only [hGe]
  refine ⟨fun k => ?_, (hL' f l).1.integral_prod_left, (hL' f l).2.trans (integral_prod _ (hL' f l).1)⟩
  obtain ⟨p, -, h⟩ := hGb ((normSeminorm ℂ ℂ).comp l.toLinearMap) l.continuous.norm
  exact (hN.const_mul (p f)).mono' (l.continuous.comp ((hGc f).comp (Continuous.prodMk_right k))).aestronglyMeasurable
    (Eventually.of_forall fun t => h (k, t) f)

theorem archSlice_of (hSt : StabEx) (hO : ArchOp) (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hI : SchInt) : ArchSlice := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hc hl lift hL K m hK hm χX χW om r s r' s' hP
  refine ⟨kAt_cpt hSt hP.base hP.herm hK, fun k hk => ⟨(mem_kAt.1 hk).2, ((hK _).1 (mem_kAt.1 hk).1).1⟩, fun f l => ?_⟩
  obtain ⟨A, hA, hAe, hAd⟩ := line_ex hS hH hU hc hl hL
  obtain ⟨T, hT, -, hTc, hTb⟩ := k_ops hSt hO hK hP
  have e1 : ∀ (k : kAt K (evI F)) c, ei (opI (fun Φ => M.co.rho B.ψ (lift c • u 1) (om (k.1, 1) Φ)) f) = A c (T k f) := fun k c => by
    rw [op_comp hH hU hP (hT k) (at_smul (hL.supp _) _), ← hAe]
  simp only [e1]
  refine ⟨l.continuous.comp (joint_cont A hA (fun q hq => ?_) _ (hTc f)), fun N => ?_, fun ν z hν hz L hLc => ?_⟩
  · obtain ⟨p, hp, h⟩ := hAd q 0 hq
    exact ⟨p, hp, fun c g => by simpa using h _ g⟩
  · obtain ⟨p, hp, h⟩ := hAd ((normSeminorm ℂ ℂ).comp l.toLinearMap) N l.continuous.norm
    obtain ⟨p', -, h'⟩ := hTb p hp
    exact ⟨p' f, fun k c => (h c _).trans (h' k f)⟩
  · obtain ⟨L', h⟩ := cone_core hSt hO hS hH hU hI hc hl hL hK hm hP ν z hν hz
    have : L f = L' f := SchwartzMap.ext fun y => by
      rw [hLc f y, ← evAt_apply y (L' f), (h f (evAt y)).2.2]
      simp only [evAt_apply, wt, mul_assoc]
    rw [this, (h f l).2.2]
    simp only [wt, mul_assoc]

end PositivityTheory.ThKG.Loc.Bump

end
