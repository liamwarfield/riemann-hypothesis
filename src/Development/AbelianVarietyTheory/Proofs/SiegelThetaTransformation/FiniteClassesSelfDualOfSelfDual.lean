module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClassesSelfDualOfSelfDual
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace SelfDualClasses

open ShortVectors

noncomputable def hermRat (n : ℕ) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] E :=
  LinearMap.mk₂ ℚ (fun x y => herm 1 x y)
    (fun x x' y => by simp [DualFamily.herm_one_eq, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [DualFamily.herm_one_eq, Finset.smul_sum])
    (fun x y y' => by simp [DualFamily.herm_one_eq, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [DualFamily.herm_one_eq, Finset.smul_sum, cc, Rat.smul_def, mul_left_comm])

theorem hermRat_apply {n : ℕ} (x y : Fin n → E) : hermRat n x y = herm 1 x y := rfl

theorem exists_isometry {n : ℕ} {ι : Type} (b b' : Basis ι ℚ (Fin n → E))
    (h : ∀ i j, herm 1 (b' i) (b' j) = herm 1 (b i) (b j)) :
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧
      ∀ i, γ (b i) = b' i := by
  let g : (Fin n → E) ≃ₗ[ℚ] (Fin n → E) := b.equiv b' (Equiv.refl ι)
  have hg : ∀ x y, herm 1 (g x) (g y) = herm 1 x y := by
    have : (hermRat n).compl₁₂ g.toLinearMap g.toLinearMap = hermRat (E := E) n :=
      LinearMap.ext_basis b b fun i j => by simp [g, hermRat_apply, h]
    intro x y
    exact LinearMap.congr_fun₂ this x y
  have hs : ∀ (c : E) x, g (c • x) = c • g x := by
    intro c x
    rw [← sub_eq_zero]
    refine (traceHerm_nondegenerate n).1 _ fun z => ?_
    obtain ⟨y, rfl⟩ := g.surjective z
    rw [map_sub, LinearMap.sub_apply, traceHerm_apply, traceHerm_apply, hg,
      TraceDualMin.herm_smul_left, TraceDualMin.herm_smul_left, hg, sub_self]
  exact ⟨{ g.toAddEquiv with map_smul' := hs }, hg, fun i => by simp [g]⟩

theorem finite_integral_of_basis {n : ℕ} {ι : Type} [Fintype ι] (b : Basis ι ℚ (Fin n → E)) :
    {Λ : Submodule (𝓞 E) (Fin n → E) | (∀ i, b i ∈ Λ) ∧
      ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)}.Finite := by
  classical
  let L₀ : Submodule ℤ (Fin n → E) := span ℤ (Set.range b)
  let L₁ : Submodule ℤ (Fin n → E) := (traceHerm n).dualSubmodule L₀
  have hfg : L₁.FG := by
    simp only [L₁, L₀]
    rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ (traceHerm_nondegenerate n)]
    exact fg_span (Set.finite_range _)
  have : Module.Finite ℤ L₁ := Module.Finite.iff_fg.mpr hfg
  have : Finite (L₁ ⧸ L₀.submoduleOf L₁) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : (x : Fin n → E) ∈ span ℚ (Set.range b) := b.mem_span _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors ℤ) ℚ _ _ hx
    refine ⟨t, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ht
  have h0 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) → ∀ x ∈ L₀, x ∈ Λ := by
    intro Λ hΛ
    have : L₀ ≤ Λ.restrictScalars ℤ := span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hΛ i)
    exact this
  have h1 : ∀ Λ : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → ∀ x ∈ Λ, x ∈ L₁ := by
    intro Λ hΛ hint x hx y hy
    have := Algebra.isIntegral_trace (L := ℚ) (hint x hx y (h0 Λ hΛ y hy))
    rw [Submodule.mem_one]
    exact IsIntegrallyClosed.isIntegral_iff.mp this
  let F : Submodule (𝓞 E) (Fin n → E) → Set (L₁ ⧸ L₀.submoduleOf L₁) :=
    fun Λ => {q | ∃ x : L₁, (x : Fin n → E) ∈ Λ ∧ Submodule.Quotient.mk x = q}
  have key : ∀ Λ Λ' : Submodule (𝓞 E) (Fin n → E), (∀ i, b i ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → (∀ i, b i ∈ Λ') → F Λ = F Λ' → Λ ≤ Λ' := by
    intro Λ Λ' hΛ hint hΛ' hF x hx
    have : Submodule.Quotient.mk ⟨x, h1 Λ hΛ hint x hx⟩ ∈ F Λ := ⟨_, hx, rfl⟩
    rw [hF] at this
    obtain ⟨y, hy, hq⟩ := this
    rw [Submodule.Quotient.eq] at hq
    have h2 : (y : Fin n → E) - x ∈ Λ' := h0 Λ' hΛ' _ hq
    simpa using Λ'.sub_mem hy h2
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro Λ ⟨hΛ, hi⟩ Λ' ⟨hΛ', hi'⟩ hF
  exact le_antisymm (key _ _ hΛ hi hΛ' hF) (key _ _ hΛ' hi' hΛ hF.symm)

theorem norm_herm_le {n : ℕ} (τ : E →+* ℂ) (x y : Fin n → E) (C : ℝ)
    (hx : ∑ k, ‖τ (x k)‖ ^ 2 ≤ C) (hy : ∑ k, ‖τ (y k)‖ ^ 2 ≤ C) : ‖τ (herm 1 x y)‖ ≤ C := by
  have h : ‖τ (herm 1 x y)‖ ≤ ∑ k, (‖τ (x k)‖ ^ 2 + ‖τ (y k)‖ ^ 2) / 2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [DualFamily.herm_one_eq, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have : ‖τ (cc (y k))‖ = ‖τ (y k)‖ := by
      simp [cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, norm_mul, this]
    nlinarith [sq_nonneg (‖τ (x k)‖ - ‖τ (y k)‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h
  linarith

theorem finite_linearMap {R M T : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup T] [Module R T] [Module.Finite R M] [Finite T] : Finite (M →ₗ[R] T) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' R M
  refine Finite.of_injective
    (fun (g : M →ₗ[R] T) (i : Fin m) => g (f (Pi.basisFun R (Fin m) i))) fun g g' h => ?_
  rw [← LinearMap.cancel_right hf]
  exact (Pi.basisFun R (Fin m)).ext fun i => congrFun h i

end SelfDualClasses


open SelfDualClasses in
theorem finite_classes_selfDual_of_selfDual (n : ℕ) :
    ∃ S : Finset (Submodule (𝓞 E) (Fin n → E)),
    (∀ Λ ∈ S, Λ.FG ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∃ Λ₀ ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∀ x, x ∈ Λ₀ ↔ γ x ∈ Λ := by
  classical
  set C : ℝ := (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) ^ 2 with hC
  let ι := Fin (2 * fdeg E * n)
  let A : Set E := {x | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C}
  have hA : A.Finite := Embeddings.finite_of_norm_le E ℂ C
  let gram : Basis ι ℚ (Fin n → E) → ι → ι → E := fun b i j => herm 1 (b i) (b j)
  let B : Set (Basis ι ℚ (Fin n → E)) := {b | ∀ i j, gram b i j ∈ A}
  have hG : (gram '' B).Finite := by
    refine (Set.Finite.pi' fun _ : ι => Set.Finite.pi' fun _ : ι => hA).subset ?_
    rintro _ ⟨b, hb, rfl⟩
    exact hb
  obtain ⟨B₀, -, hB₀fin, hB₀⟩ := Set.exists_subset_image_finite_and.mp
    (⟨gram '' B, subset_rfl, hG, rfl⟩ : ∃ t ⊆ gram '' B, t.Finite ∧ t = gram '' B)
  have hS : {Λ : Submodule (𝓞 E) (Fin n → E) | (∃ b ∈ B₀, ∀ i, b i ∈ Λ) ∧ Λ.FG ∧
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ}.Finite := by
    refine (hB₀fin.biUnion fun b _ => finite_integral_of_basis b).subset ?_
    rintro Λ ⟨⟨b, hb, hbΛ⟩, -, hi, -⟩
    exact Set.mem_biUnion hb ⟨hbΛ, hi⟩
  refine ⟨hS.toFinset, fun Λ hΛ => (hS.mem_toFinset.mp hΛ).2, fun Λ hfg hint hdual => ?_⟩
  obtain ⟨v, hv, hli, hsp, hle⟩ := exists_short_vectors Λ hfg hint hdual
  let b : Basis ι ℚ (Fin n → E) := Basis.mk hli hsp.ge
  have hb : ∀ i, b i = v i := fun i => Basis.mk_apply _ _ i
  have hbB : gram b ∈ gram '' B₀ := by
    rw [hB₀]
    refine ⟨b, fun i j => ?_, rfl⟩
    simp only [gram, hb]
    exact ⟨hint _ (hv i) _ (hv j), fun φ => norm_herm_le φ _ _ C (hle i φ) (hle j φ)⟩
  obtain ⟨b₀, hb₀, hgram⟩ := hbB
  obtain ⟨γ, hγ, hγb⟩ := exists_isometry b₀ b fun i j => (congrFun₂ hgram i j).symm
  let γ' : (Fin n → E) ≃ₗ[𝓞 E] (Fin n → E) := γ.restrictScalars (𝓞 E)
  refine ⟨Λ.comap γ'.toLinearMap, hS.mem_toFinset.mpr ⟨⟨b₀, hb₀, fun i => ?_⟩, ?_, ?_, ?_⟩,
    γ, hγ, fun x => Iff.rfl⟩
  · change γ (b₀ i) ∈ Λ
    rw [hγb, hb]
    exact hv i
  · rw [Submodule.comap_equiv_eq_map_symm]
    exact hfg.map _
  · intro x hx y hy
    rw [← hγ]
    exact hint _ hx _ hy
  · intro x hx
    refine hdual (γ x) fun y hy => ?_
    obtain ⟨z, rfl⟩ := γ.surjective y
    rw [hγ]
    exact hx z hy

theorem finite_classes_selfDual_pairs (n : ℕ) (T : Type) [AddCommGroup T] [Module (𝓞 E) T]
    [Finite T] :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) → ∀ f : Λ →ₗ[𝓞 E] T,
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  classical
  obtain ⟨S, hS, hcl⟩ := finite_classes_selfDual_of_selfDual (E := E) n
  have hfin : {P : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T | P.1 ∈ S}.Finite := by
    refine (S.finite_toSet.biUnion (t := fun Λ => Set.range
      fun f : Λ →ₗ[𝓞 E] T => (⟨Λ, f⟩ : Σ Λ : Submodule (𝓞 E) (Fin n → E), Λ →ₗ[𝓞 E] T))
      fun Λ hΛ => ?_).subset ?_
    · have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr (hS Λ hΛ).1
      have : Finite (Λ →ₗ[𝓞 E] T) := SelfDualClasses.finite_linearMap
      exact Set.finite_range _
    · rintro ⟨Λ, f⟩ h
      exact Set.mem_biUnion h ⟨f, rfl⟩
  refine ⟨hfin.toFinset, fun P hP => hS _ (hfin.mem_toFinset.mp hP), fun Λ h1 h2 h3 f => ?_⟩
  obtain ⟨Λ₀, hΛ₀, γ, hγ, h⟩ := hcl Λ h1 h2 h3
  exact ⟨⟨Λ₀, f ∘ₗ (γ.restrictScalars (𝓞 E)).toLinearMap.restrict fun x hx => (h x).mp hx⟩,
    hfin.mem_toFinset.mpr hΛ₀, γ, hγ, h, fun x => rfl⟩

theorem finite_classes_selfDual_level (n N : ℕ) (hN : N ≠ 0) :
    ∃ S : Finset (Σ Λ : Submodule (𝓞 E) (Fin n → E),
      Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})),
    (∀ P ∈ S, P.1.FG ∧ (∀ x ∈ P.1, ∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ P.1, IsIntegral ℤ (herm 1 x y)) → x ∈ P.1) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∀ f : Λ →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}),
    ∃ P ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∃ h : ∀ x, x ∈ P.1 ↔ γ x ∈ Λ,
        ∀ x : P.1, P.2 x = f ⟨γ x, (h x).mp x.2⟩ := by
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  exact finite_classes_selfDual_pairs n _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LeftInvOfUnitary
noncomputable section

open MeasureTheory Topology Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.VolPairExists

theorem exists_haar_image {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G))
    {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [ν.IsHaarMeasure] (ψ : G →* R) (hψ : Continuous ψ)
    (hs : ∀ t, ∃ h ∈ H, ψ h = t)
    (hf : ∀ t, ∃ W ∈ 𝓝 t, ∃ K : Set G, IsCompact K ∧ (H : Set G) ∩ ψ ⁻¹' W ⊆ K) :
    ∃ μ : Measure G, μ.IsHaarMeasure ∧ ∀ s, MeasurableSet s → μ (ψ ⁻¹' s ∩ H) = ν s := by
  classical
  have hψm : Measurable ψ := hψ.measurable
  set μ₀ : Measure G := Measure.haar
  set ρ : Measure R := (μ₀.restrict (H : Set G)).map ψ with hρdef
  have hρ : ∀ s, MeasurableSet s → ρ s = μ₀ (ψ ⁻¹' s ∩ H) := by
    intro s hsm
    rw [hρdef, Measure.map_apply hψm hsm, Measure.restrict_apply (hψm hsm)]
  have : ρ.IsMulLeftInvariant := by
    refine ⟨fun r => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hs r
    refine Measure.ext fun s hsm => ?_
    have hpre : ψ ⁻¹' ((fun x => ψ h * x) ⁻¹' s) ∩ H = (fun x => h * x) ⁻¹' (ψ ⁻¹' s ∩ H) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe]
      rw [Subgroup.mul_mem_cancel_left H hh]
    rw [Measure.map_apply (measurable_const_mul _) hsm, hρ _ ((measurable_const_mul _) hsm), hρ _ hsm,
      hpre, measure_preimage_mul]
  have : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun C hC => ?_⟩
    choose W hW K hK hWK using hf
    obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun x => interior (W x))
      (fun x _ => interior_mem_nhds.2 (hW x))
    have hUo : IsOpen (⋃ x ∈ t, interior (W x)) := isOpen_biUnion fun x _ => isOpen_interior
    calc ρ C ≤ ρ (⋃ x ∈ t, interior (W x)) := measure_mono ht
      _ = μ₀ (ψ ⁻¹' (⋃ x ∈ t, interior (W x)) ∩ H) := hρ _ hUo.measurableSet
      _ ≤ μ₀ (⋃ x ∈ t, K x) := by
          apply measure_mono
          rintro y ⟨hy1, hy2⟩
          simp only [Set.mem_preimage, Set.mem_iUnion] at hy1 ⊢
          obtain ⟨x, hx, hyx⟩ := hy1
          exact ⟨x, hx, hWK x ⟨hy2, show ψ y ∈ W x from interior_subset hyx⟩⟩
      _ ≤ ∑ x ∈ t, μ₀ (K x) := measure_biUnion_finset_le t K
      _ < ⊤ := ENNReal.sum_lt_top.2 fun x _ => (hK x).measure_lt_top
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have h1 := hρ Set.univ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.preimage_univ, Set.univ_inter] at h1
    exact (hH.measure_pos μ₀ ⟨1, H.one_mem⟩).ne' h1.symm
  have hc := Measure.isMulLeftInvariant_eq_smul ρ ν
  set c := Measure.haarScalarFactor ρ ν
  have hc0 : c ≠ 0 := by
    intro h0
    apply hρ0
    rw [hc, h0, zero_smul]
  have : (c⁻¹ • μ₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc0)
  refine ⟨c⁻¹ • μ₀, inferInstance, fun s hsm => ?_⟩
  have h1 := hρ s hsm
  rw [hc] at h1
  rw [Measure.smul_apply, ← h1, Measure.smul_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul]

variable {P Q : ℕ}

theorem jpq_mul_self : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem left_inv_of_unitary {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  calc Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q * (uᴴ * Formalism.UG.Jpq P Q * u) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, jpq_mul_self]

def mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) :
    UpqT P Q :=
  (⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv_of_unitary h),
    left_inv_of_unitary h⟩, h⟩ : Formalism.UG.Upq P Q)

theorem mat_mkU (u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (h) : UpqT.mat (mkU u h) = u := rfl

theorem mat_injective : Function.Injective (UpqT.mat (P := P) (Q := Q)) := by
  intro a b h
  let a' : Formalism.UG.Upq P Q := a
  let b' : Formalism.UG.Upq P Q := b
  have h' : a'.1 = b'.1 := Units.ext h
  exact (Subtype.ext h' : a' = b')

theorem mat_mul (b c : UpqT P Q) : UpqT.mat (b * c) = UpqT.mat b * UpqT.mat c := rfl

theorem mat_one : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := by
  have hb := (b : Formalism.UG.Upq P Q).2
  exact hb

theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) := by
  exact Units.continuous_val.comp continuous_subtype_val

theorem continuous_mkU {X : Type} [TopologicalSpace X] (f : X → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
    (hf : Continuous f) (h : ∀ x, (f x)ᴴ * Formalism.UG.Jpq P Q * f x = Formalism.UG.Jpq P Q) :
    Continuous fun x => mkU (f x) (h x) := by
  have hinv : Continuous fun x => Formalism.UG.Jpq P Q * (f x)ᴴ * Formalism.UG.Jpq P Q :=
    (continuous_const.matrix_mul hf.matrix_conjTranspose).matrix_mul continuous_const
  unfold mkU
  refine (Units.continuous_iff.2 ⟨?_, ?_⟩).subtype_mk _
  · exact hf
  · exact hinv

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}

theorem exists_frame (h : Formalism.UG.HasSignature G P Q) :
    ∃ (A : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ) (L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ),
      Aᴴ * Formalism.UG.Jpq P Q * A = G ∧ L * A = 1 ∧ A * L = 1 := by
  unfold Formalism.UG.HasSignature at h
  obtain ⟨e, g, hg⟩ := h
  have hg' : (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Matrix.reindex e e G * g = Formalism.UG.Jpq P Q := hg
  have key : Matrix.reindex e e G =
      ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᴴ * Formalism.UG.Jpq P Q *
        ((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    set u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := g.val
    set v : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := (g⁻¹).val
    have huv : u * v = 1 := Units.mul_inv g
    calc Matrix.reindex e e G = (u * v)ᴴ * Matrix.reindex e e G * (u * v) := by
          rw [huv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = vᴴ * (uᴴ * Matrix.reindex e e G * u) * v := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = vᴴ * Formalism.UG.Jpq P Q * v := by rw [hg']
  refine ⟨((g⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix id e,
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (Formalism.UG.Jpq P Q),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← key]
    ext i j
    simp [Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Units.mul_inv, Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_id_id]

variable {A A' : Matrix (Fin P ⊕ Fin Q) (Fin n) ℂ} {L : Matrix (Fin n) (Fin P ⊕ Fin Q) ℂ}

theorem conj_frame (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) : Lᴴ * G * L = Formalism.UG.Jpq P Q := by
  rw [← hA]
  have h1 : Lᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * L = (A * L)ᴴ * Formalism.UG.Jpq P Q * (A * L) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, hr, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem change_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (hA' : A'ᴴ * Formalism.UG.Jpq P Q * A' = G) :
    (A' * L)ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul]
  have h1 : Lᴴ * A'ᴴ * Formalism.UG.Jpq P Q * (A' * L) = Lᴴ * (A'ᴴ * Formalism.UG.Jpq P Q * A') * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA', conj_frame hA hr]

theorem conj_unitary (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : gᴴ * G * g = G) : (A * g * L)ᴴ * Formalism.UG.Jpq P Q * (A * g * L) = Formalism.UG.Jpq P Q := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Lᴴ * (gᴴ * Aᴴ) * Formalism.UG.Jpq P Q * (A * g * L) =
      Lᴴ * (gᴴ * (Aᴴ * Formalism.UG.Jpq P Q * A) * g) * L := by
    simp only [Matrix.mul_assoc]
  rw [h1, hA, hg, conj_frame hA hr]

theorem conj_unitary_back (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hr : A * L = 1) (b : UpqT P Q) :
    (L * UpqT.mat b * A)ᴴ * G * (L * UpqT.mat b * A) = G := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have h1 : Aᴴ * ((UpqT.mat b)ᴴ * Lᴴ) * G * (L * UpqT.mat b * A) =
      Aᴴ * ((UpqT.mat b)ᴴ * (Lᴴ * G * L) * UpqT.mat b) * A := by
    simp only [Matrix.mul_assoc]
  rw [h1, conj_frame hA hr, mat_unitary, hA]

theorem exists_hom {Γ : Type} [Group Γ] [TopologicalSpace Γ] (m : Γ → Matrix (Fin n) (Fin n) ℂ)
    (hm : Continuous m) (hmul : ∀ g h, m (g * h) = m g * m h) (hu : ∀ h, (m h)ᴴ * G * m h = G)
    (hA : Aᴴ * Formalism.UG.Jpq P Q * A = G) (hl : L * A = 1) (hr : A * L = 1) :
    ∃ ψ : Γ →* UpqT P Q, Continuous ψ ∧ ∀ h, UpqT.mat (ψ h) = A * m h * L := by
  let f : Γ → UpqT P Q := fun x => mkU (A * m x * L) (conj_unitary hA hr (hu x))
  have hf : ∀ x, UpqT.mat (f x) = A * m x * L := fun x => mat_mkU _ _
  refine ⟨MonoidHom.mk' f fun x y => mat_injective ?_, ?_, fun x => hf x⟩
  · rw [mat_mul, hf, hf, hf, hmul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L, hl, Matrix.one_mul]
  · show Continuous f
    exact continuous_mkU (fun x => A * m x * L) ((continuous_const.matrix_mul hm).matrix_mul continuous_const)
      (fun x => conj_unitary hA hr (hu x))

theorem read_iff (hl : L * A = 1) (hr : A * L = 1) (u : UpqT P Q) (hu : UpqT.mat u = A' * L)
    {g : Matrix (Fin n) (Fin n) ℂ} (t : UpqT P Q) (ht : UpqT.mat t = A * g * L) (B : Set (UpqT P Q)) :
    (∃ b ∈ B, UpqT.mat b * A' = A' * g) ↔ t ∈ (fun b => b * u⁻¹) ⁻¹' ((fun b => u * b) ⁻¹' B) := by
  have hA' : A' = UpqT.mat u * A := by rw [hu, Matrix.mul_assoc, hl, Matrix.mul_one]
  have hinv : UpqT.mat u⁻¹ * UpqT.mat u = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
  have key : ∀ b : UpqT P Q, UpqT.mat b * A' = A' * g ↔ b = u * (t * u⁻¹) := by
    intro b
    constructor
    · intro h
      have h2 : UpqT.mat (b * u) = UpqT.mat (u * t) := by
        rw [mat_mul, mat_mul, ht]
        calc UpqT.mat b * UpqT.mat u = UpqT.mat b * A' * L := by rw [hu, Matrix.mul_assoc]
          _ = A' * g * L := by rw [h]
          _ = UpqT.mat u * (A * g * L) := by rw [hA']; simp only [Matrix.mul_assoc]
      have h3 := mat_injective h2
      rw [← mul_assoc, ← h3, mul_inv_cancel_right]
    · rintro rfl
      rw [mat_mul, mat_mul, ht, hA']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UpqT.mat u⁻¹), hinv, Matrix.one_mul, hl, Matrix.mul_one]
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨b, hb, h⟩
    rwa [(key b).1 h] at hb
  · intro h
    exact ⟨_, h, (key _).2 rfl⟩

end GlobalTheory.VolPairExists
end
end
