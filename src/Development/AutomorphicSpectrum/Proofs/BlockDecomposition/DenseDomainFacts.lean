module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal

namespace GlobalTheory.CompanionTheory.DenseCpt

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

theorem val_emb (n : ℕ) : IsOpenEmbedding (Units.val : G n → Mat n) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℂ) (α := ℂ)
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem continuous_extend {n : ℕ} {V : Type} [NormedAddCommGroup V] {b : G n → V} (hb : Continuous b)
    (hs : HasCompactSupport b) : Continuous (Function.extend (Units.val : G n → Mat n) b 0) := by
  have he := val_emb n
  refine continuous_of_tsupport fun x h => ?_
  obtain ⟨u, -, rfl⟩ := hs.tsupport_extend_zero_subset he.continuous h
  rw [← he.continuousAt_iff]
  have : Function.extend (Units.val : G n → Mat n) b 0 ∘ Units.val = b :=
    funext fun y => he.injective.extend_apply _ _ _
  rw [this]
  exact hb.continuousAt

theorem exists_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : G n → V}
    (hb : Continuous b) (hs : HasCompactSupport b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : Mat n → V, ContDiff ℝ ∞ f ∧ (∀ y : G n, dist (b y) (f y.val) ≤ δ) ∧
      ∀ y, y ∉ (Units.val : G n → Mat n) '' tsupport b → f y = 0 := by
  have he := val_emb n
  obtain ⟨f, hf, hd, hsu⟩ := (continuous_extend hb hs).exists_contDiff_approx ⊤ (ε := fun _ => δ)
    continuous_const fun _ => hδ
  refine ⟨f, hf, fun y => ?_, fun y hy => ?_⟩
  · have := hd y.val
    rw [show Function.extend (Units.val : G n → Mat n) b 0 y.val = b y from he.injective.extend_apply _ _ _] at this
    rw [dist_comm]; exact this.le
  · by_contra hne
    have h1 := hsu (Function.mem_support.2 hne)
    exact hy (hs.tsupport_extend_zero_subset he.continuous (subset_tsupport _ h1))

theorem cpt_of {n : ℕ} {V : Type} [Zero V] (hL : LgFacts) {K : Set (G n)} (hK : IsCompact K) {f : Mat n → V}
    (hf : ∀ y, y ∉ (Units.val : G n → Mat n) '' K → f y = 0) : Cpt f := by
  have he := val_emb n
  have hc : IsCompact ((Units.val : G n → Mat n) '' K) := hK.image he.continuous
  have hsub : (Units.val : G n → Mat n) '' K ⊆ GLs n := by
    rintro _ ⟨u, -, rfl⟩; exact val_mem u
  have hcont : ContinuousOn (lg : Mat n → ℝ) ((Units.val : G n → Mat n) '' K) :=
    ((hL n).2.2.2.1.continuousOn).mono hsub
  obtain ⟨R, hR⟩ := (hc.image_of_continuousOn hcont).bddAbove
  refine ⟨R, fun y _ hy => hf y fun hm => ?_⟩
  exact absurd (hR ⟨y, hm, rfl⟩) (not_le.2 hy)

theorem denseD : DenseD := by
  intro n _ _ μ _ V _ _ hL
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (G n) := (val_emb n).isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (G n) := (val_emb n).locallyCompactSpace
  intro x
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  have hp : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨b, hbs, hbd, hbc, hbm⟩ := (Lp.memLp x).exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε2)
  set K := tsupport b with hKdef
  have hKc : IsCompact K := hbs
  set m : ℝ≥0∞ := μ K ^ (1 / (2 : ℝ≥0∞).toReal) with hm
  have hmt : m ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hKc.measure_lt_top.ne
  set c : ℝ := (ε / 2) / (m.toReal + 1) with hc
  have hm0 : 0 ≤ m.toReal := ENNReal.toReal_nonneg
  have hcpos : 0 < c := by positivity
  obtain ⟨f, hf, hd, hz⟩ := exists_smooth hbc hbs hcpos
  have hcf : Continuous fun y : G n => f y.val := hf.continuous.comp Units.continuous_val
  have hsupp : Function.support (fun y : G n => f y.val) ⊆ K := by
    intro y hy
    by_contra hyK
    exact hy (hz _ fun ⟨u, hu, he⟩ => hyK (Units.ext he ▸ hu))
  have hcs : HasCompactSupport fun y : G n => f y.val :=
    HasCompactSupport.of_support_subset_isCompact hKc hsupp
  have hg : MemLp (fun y : G n => f y.val) 2 μ := hcf.memLp_of_hasCompactSupport hcs
  have hbg : eLpNorm (b - fun y : G n => f y.val) 2 μ ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_sub_le_of_dist_bdd μ hp hKc.measurableSet.nullMeasurableSet hcpos.le
      (hbm.aestronglyMeasurable.sub hg.aestronglyMeasurable) hd (subset_tsupport b) hsupp).trans ?_
    change ENNReal.ofReal c * m ≤ _
    conv_lhs => rw [← ENNReal.ofReal_toReal hmt]
    rw [← ENNReal.ofReal_mul hcpos.le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨hg.toLp _, ⟨f, hf.contDiffOn, cpt_of hL hKc hz, ?_⟩, ?_⟩
  · simp only [cls]; rw [dite_eq_left hg]
  · rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
      ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp x).sub (Lp.memLp (hg.toLp _))).eLpNorm_ne_top hε.le]
    have h1 : eLpNorm (⇑x - ⇑(hg.toLp _)) 2 μ = eLpNorm (⇑x - fun y : G n => f y.val) 2 μ :=
      eLpNorm_congr_ae (by filter_upwards [hg.coeFn_toLp] with y hy; simp [hy])
    rw [h1]
    have h2 : (⇑x - fun y : G n => f y.val) = (⇑x - b) + (b - fun y : G n => f y.val) := by
      ext y; simp
    rw [h2]
    refine (eLpNorm_add_le (p := 2) (by norm_num)).trans ?_
    calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hbd hbg
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le]; congr 1; ring

end GlobalTheory.CompanionTheory.DenseCpt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_domain_facts : PositivityTheory.RgBcC.Fc.DenseD := by
  first | exact @GlobalTheory.CompanionTheory.DenseCpt.denseD | exact GlobalTheory.CompanionTheory.DenseCpt.denseD | (intros; apply GlobalTheory.CompanionTheory.DenseCpt.denseD <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FriedrichsFc

open UniformSpace (Completion)

theorem exists_extension {E F : Type} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f : E →ₗ[ℂ] F) (hf : ∀ u, ‖f u‖ ≤ ‖u‖) :
    ∃ g : Completion E →L[ℂ] F, (∀ u : E, g (u : Completion E) = f u) ∧ ‖g‖ ≤ 1 := by
  let f' : E →L[ℂ] F := f.mkContinuous 1 (by simpa using hf)
  let e : E →L[ℂ] Completion E := UniformSpace.Completion.toComplL
  have hd : DenseRange e := UniformSpace.Completion.denseRange_coe
  have hu : IsUniformInducing e := UniformSpace.Completion.isUniformInducing_coe E
  have he : ∀ u : E, (f'.extend e) (u : Completion E) = f u := fun u => f'.extend_eq hd hu u
  refine ⟨f'.extend e, he, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [he, UniformSpace.Completion.norm_coe, one_mul]
    exact hf u

theorem norm_map_le {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ)
    (V V' : H →L[ℂ] H) (V₀ : E →ₗ[ℂ] E) (h1 : V' * V = 1)
    (hadj : ∀ u v, ⟪V u, v⟫_ℂ = ⟪u, V' v⟫_ℂ)
    (hι : ∀ u, V (ι u) = ι (V₀ u)) (hBV : ∀ u, B (V₀ u) = V (B u)) (u : E) :
    ‖V₀ u‖ ≤ ‖u‖ := by
  have key : ⟪V₀ u, V₀ u⟫_ℂ = ⟪u, u⟫_ℂ := by
    have h2 : V' (V (ι u)) = ι u := by
      have := congrArg (fun W : H →L[ℂ] H => W (ι u)) h1
      simpa using this
    rw [← hB, hBV, ← hι, hadj, h2, hB]
  have : ‖V₀ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  exact le_of_eq ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this)

theorem exists_inverse_of_form {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι B : E →ₗ[ℂ] H) (hB : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪u, v⟫_ℂ) (hι : ∀ u, ‖ι u‖ ≤ ‖u‖) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : E →ₗ[ℂ] E), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  obtain ⟨g, hg, hgn⟩ := exists_extension ι hι
  let S : H →L[ℂ] Completion E := ContinuousLinearMap.adjoint g
  have hSi : ∀ h c, ⟪S h, c⟫_ℂ = ⟪h, g c⟫_ℂ := fun h c =>
    ContinuousLinearMap.adjoint_inner_left g c h
  have hS : ∀ u : E, S (B u) = (u : Completion E) := by
    intro u
    refine ext_inner_right ℂ fun c => ?_
    rw [hSi]
    induction c using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih v => rw [hg, hB, UniformSpace.Completion.inner_coe]
  have hSn : ‖S‖ ≤ 1 := by
    have : ‖S‖ = ‖g‖ := by simp [S]
    rw [this]; exact hgn
  have hTpos : (g ∘L S).IsPositive := ContinuousLinearMap.isPositive_self_comp_adjoint g
  refine ⟨g ∘L S, hTpos.isSelfAdjoint, ?_, ?_, ?_⟩
  · calc ‖g ∘L S‖ ≤ ‖g‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · intro u
    simp only [ContinuousLinearMap.comp_apply]
    rw [hS, hg]
  · intro U U' U₀ U₀' hUU' hU'U hadj hι₀ hι₀' hB₀ hB₀'
    have hadj' : ∀ u v, ⟪U' u, v⟫_ℂ = ⟪u, U v⟫_ℂ := fun u v => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    let c : E →ₗ[ℂ] Completion E :=
      (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := E)).toLinearMap
    have hc : ∀ u : E, c u = (u : Completion E) := fun _ => rfl
    obtain ⟨U₁, hU₁, -⟩ := exists_extension (c ∘ₗ U₀) (fun u => by
      simpa [hc] using norm_map_le ι B hB U U' U₀ hU'U hadj hι₀ hB₀ u)
    obtain ⟨U₁', hU₁', -⟩ := exists_extension (c ∘ₗ U₀') (fun u => by
      simpa [hc] using norm_map_le ι B hB U' U U₀' hUU' hadj' hι₀' hB₀' u)
    have h1 : ∀ x, g (U₁ x) = U (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁, LinearMap.comp_apply, hc, hg, hg, hι₀]
    have h1' : ∀ x, g (U₁' x) = U' (g x) := by
      intro x
      induction x using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u => rw [hU₁', LinearMap.comp_apply, hc, hg, hg, hι₀']
    have h3 : ∀ a x, ⟪U₁ a, x⟫_ℂ = ⟪a, U₁' x⟫_ℂ := by
      intro a x
      induction a using UniformSpace.Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih u =>
        induction x using UniformSpace.Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih v =>
          rw [hU₁, hU₁', LinearMap.comp_apply, LinearMap.comp_apply, hc, hc,
            UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe,
            ← hB, hB₀, hadj, hι₀', hB]
    have h4 : ∀ h, S (U h) = U₁ (S h) := by
      intro h
      refine ext_inner_right ℂ fun x => ?_
      rw [hSi, hadj, ← h1', ← hSi, h3]
    ext h
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [h4, h1]

theorem exists_inverse_of_coercive {H D : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [AddCommGroup D] [Module ℂ D] (ι B : D →ₗ[ℂ] H)
    (hsym : ∀ u v, ⟪B u, ι v⟫_ℂ = ⟪ι u, B v⟫_ℂ)
    (hpos : ∀ u, ‖ι u‖ ^ 2 ≤ (⟪B u, ι u⟫_ℂ).re) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ ‖T‖ ≤ 1 ∧ (∀ u, T (B u) = ι u) ∧
      ∀ (U U' : H →L[ℂ] H) (U₀ U₀' : D →ₗ[ℂ] D), U * U' = 1 → U' * U = 1 →
        (∀ u v, ⟪U u, v⟫_ℂ = ⟪u, U' v⟫_ℂ) → (∀ u, U (ι u) = ι (U₀ u)) →
        (∀ u, U' (ι u) = ι (U₀' u)) → (∀ u, B (U₀ u) = U (B u)) →
        (∀ u, B (U₀' u) = U' (B u)) → U * T = T * U := by
  letI core : PreInnerProductSpace.Core ℂ D :=
    { inner := fun u v => ⟪B u, ι v⟫_ℂ
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) ⟪B y, ι x⟫_ℂ = ⟪B x, ι y⟫_ℂ
        rw [inner_conj_symm, hsym]
      re_inner_nonneg := fun x => le_trans (sq_nonneg _) (hpos x)
      add_left := fun x y z => by
        show ⟪B (x + y), ι z⟫_ℂ = ⟪B x, ι z⟫_ℂ + ⟪B y, ι z⟫_ℂ
        rw [map_add (f := _), inner_add_left]
      smul_left := fun x y r => by
        show ⟪B (r • x), ι y⟫_ℂ = (starRingEnd ℂ) r * ⟪B x, ι y⟫_ℂ
        rw [map_smul, inner_smul_left] }
  letI sn : SeminormedAddCommGroup D := InnerProductSpace.Core.toSeminormedAddCommGroup (c := core)
  letI ips : InnerProductSpace ℂ D := InnerProductSpace.ofCore core
  have hι : ∀ u : D, ‖ι u‖ ≤ ‖u‖ := fun u => by
    have h : ‖u‖ ^ 2 = (⟪B u, ι u⟫_ℂ).re := @norm_sq_eq_re_inner ℂ D _ sn ips u
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h ▸ hpos u)
  exact exists_inverse_of_form ι B (fun _ _ => rfl) hι

theorem friedrichs : PositivityTheory.RgBcC.Fc.Friedrichs := by
  intro H _ _ _ D A hsym hpos
  obtain ⟨R, hR, hRn, hRA, hRU⟩ := exists_inverse_of_coercive (D := D) D.subtype A
    (fun x y => hsym x y) (fun x => hpos x)
  refine ⟨R, hR, hRn, fun x => hRA x, ?_⟩
  intro U hU1 hU2 hD hD'
  have lift : ∀ (V : H →L[ℂ] H), (∀ x : D, ∃ y : D, (y : H) = V x ∧ A y = V (A x)) →
      ∃ V₀ : D →ₗ[ℂ] D, (∀ u, V (D.subtype u) = D.subtype (V₀ u)) ∧ ∀ u, A (V₀ u) = V (A u) := by
    intro V hV
    have hmem : ∀ x : D, (V.toLinearMap ∘ₗ D.subtype) x ∈ D := fun x => by
      obtain ⟨y, hy, -⟩ := hV x
      simpa [← hy] using y.2
    refine ⟨LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem, fun u => rfl, fun u => ?_⟩
    obtain ⟨y, hy, hAy⟩ := hV u
    have : LinearMap.codRestrict D (V.toLinearMap ∘ₗ D.subtype) hmem u = y :=
      Subtype.ext (by simp [hy])
    rw [this, hAy]
  obtain ⟨U₀, h1, h2⟩ := lift U hD
  obtain ⟨U₀', h1', h2'⟩ := lift (ContinuousLinearMap.adjoint U) hD'
  exact hRU U (ContinuousLinearMap.adjoint U) U₀ U₀' hU2 hU1
    (fun u v => (ContinuousLinearMap.adjoint_inner_right U u v).symm) h1 h1' h2 h2'

end GlobalTheory.CompanionTheory.FriedrichsFc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.friedrichs_extension_facts : PositivityTheory.RgBcC.Fc.Friedrichs := by
  first | exact @GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs | exact GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs | (intros; apply GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs <;> assumption)
end
end
