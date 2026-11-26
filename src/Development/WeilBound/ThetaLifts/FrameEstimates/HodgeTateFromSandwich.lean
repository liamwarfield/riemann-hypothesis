module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DomU {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)) : Prop :=
  ∃ k : ℕ, ∀ φ ∈ 𝓕, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (G : UA σ X.J → ℝ≥0∞), Continuous p ∧ Measurable G ∧
    ∫⁻ g in M.dom, G g ∂M.μ < ⊤ ∧ ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * G g

def DomWeilU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (d + 2 * min r s < 2 * n ∨ min r s = 0) → DomU M om {φ | φ ∈ SB _}

def SoSemiU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ N : ℕ, ∃ k : ℕ, ∀ φ ∈ soFin B M, ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
    ∀ (f : SInf F (Fin n × Fin d)) g h, ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ p f * (ht h : ℝ) ^ k

def DomSoU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → DomU M om (soFin B M)

theorem domWeil_of_U (h : DomWeilU) : DomWeil := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hd φ hφ
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP hd
  obtain ⟨p, G, hp, hG, hint, hb⟩ := hk φ hφ
  exact ⟨p, k, G, hp, hG, hint, hb⟩

theorem soSemi_of_U (h : SoSemiU) : SoSemi := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ N
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP N
  obtain ⟨p, hp, hb⟩ := hk φ hφ
  exact ⟨p, k, hp, hb⟩

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
noncomputable section

namespace PositivityTheory.ThKEst

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace SignatureOfHermitianForm

theorem sig_sq {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : r + s = n) (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ)
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) :
    M.det ≠ 0 ∧ Function.Surjective A.mulVec := by
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr h.symm).trans finSumFinEquiv.symm
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e
  have h1 : A'ᵀ * M * A'.map star
      = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e e := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have h2 : A'.det * M.det * (A'.map star).det ≠ 0 := by
    rw [← Matrix.det_transpose A', ← Matrix.det_mul, ← Matrix.det_mul, h1, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  have h3 : A'.det ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h2)
  refine ⟨right_ne_zero_of_mul (left_ne_zero_of_mul h2), fun x => ?_⟩
  have hu : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').2 (Ne.isUnit h3)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu x
  refine ⟨u ∘ e.symm, ?_⟩
  rw [← hu]
  ext i
  simp only [A', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp]
  rw [← e.sum_comp]
  simp

theorem block_form {r s : ℕ} (w : Fin r ⊕ Fin s → ℂ) :
    w ⬝ᵥ (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) *ᵥ star w
      = ((∑ i, Complex.normSq (w (Sum.inl i)) - ∑ j, Complex.normSq (w (Sum.inr j)) : ℝ) : ℂ) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem sig_index {n r s k : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (c : ℂ) (hc : c ≠ 0)
    (x y : Fin k → Fin n → ℂ) (hxx : ∀ i j, x i ⬝ᵥ M *ᵥ star (x j) = 0)
    (hxy : ∀ i j, x i ⬝ᵥ M *ᵥ star (y j) = if i = j then c else 0) : k ≤ min r s := by
  obtain ⟨h, A, hA⟩ := h
  choose u hu using fun i => (sig_sq h A hA).2 (x i)
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin r ⊕ Fin s → ℂ) := Fintype.linearCombination ℂ u
  have hL : ∀ v, A *ᵥ L v = ∑ i, v i • x i := by
    intro v
    simp only [L, Fintype.linearCombination_apply, Matrix.mulVec_sum, Matrix.mulVec_smul, hu]
  have hinj : ∀ v, L v = 0 → v = 0 := by
    intro v hv
    have h0 := hL v
    rw [hv, Matrix.mulVec_zero] at h0
    ext j
    have h1 := congrArg (fun z => z ⬝ᵥ M *ᵥ star (y j)) h0
    simp only [zero_dotProduct, sum_dotProduct, smul_dotProduct, hxy, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_right hc
  have hiso : ∀ v, ∑ i, Complex.normSq (L v (Sum.inl i)) = ∑ j, Complex.normSq (L v (Sum.inr j)) := by
    intro v
    have h1 := block_form (L v)
    have h2 : (A *ᵥ L v) ⬝ᵥ M *ᵥ star (A *ᵥ L v) = 0 := by
      rw [hL]
      simp only [star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, smul_dotProduct,
        dotProduct_sum, dotProduct_smul, hxx, smul_zero, Finset.sum_const_zero]
    have h3 : star (A *ᵥ L v) = A.map star *ᵥ star (L v) := by
      ext i
      simp [Matrix.mulVec, dotProduct]
    rw [h3, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hA, h1] at h2
    exact sub_eq_zero.1 (Complex.ofReal_eq_zero.1 h2)
  have hz : ∀ {m : ℕ} (f : Fin m → ℂ), ∑ i, Complex.normSq (f i) = 0 → ∀ i, f i = 0 := by
    intro m f hf i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (f i)).1 hf i (Finset.mem_univ i))
  refine le_min ?_ ?_
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inl) ∘ₗ L) (by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inl i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inr j)) (by rw [← hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h1 i
      · exact h2 j)
    simpa using this
  · have := LinearMap.finrank_le_finrank_of_injective (f := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ L) (by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : ∀ i, L v (Sum.inr i) = 0 := fun i => congrFun hv i
      have h2 := hz (fun j => L v (Sum.inl j)) (by rw [hiso]; simp [h1])
      apply hinj
      ext (i | j)
      · exact h2 i
      · exact h1 j)
    simpa using this

theorem form_map {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (x y : Fin n → E) :
    (fun i => τ (x i)) ⬝ᵥ (c • J.map τ) *ᵥ star (fun i => τ (y i)) = c * τ (x ⬝ᵥ J *ᵥ fun i => σ (y i)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp [dotProduct, Matrix.mulVec, hτ]

theorem of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = star (τ x)) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : HasSig (c • J.map τ) r s) :
    J.det ≠ 0 ∧ r + s = n ∧ ∀ fr : Frame σ J, fr.IsGood → fr.r ≤ min r s := by
  refine ⟨?_, h.1, fun fr hfr => ?_⟩
  · obtain ⟨h, A, hA⟩ := h
    intro h0
    apply (sig_sq h A hA).1
    have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [Matrix.det_smul, this, h0, map_zero, mul_zero]
  · refine sig_index h c hc (fun i l => τ (fr.x i l)) (fun i l => τ (fr.y i l)) (fun i j => ?_) (fun i j => ?_)
    · have := hfr.xx i j
      unfold form at this
      rw [form_map σ τ hτ, this, map_zero, mul_zero]
    · have := hfr.xy i j
      unfold form at this
      rw [form_map σ τ hτ, this]
      split_ifs <;> simp

end SignatureOfHermitianForm

theorem epsOf_of : EpsOf := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩

end PositivityTheory.ThKEst
end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem countable_numberField' (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Countable (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  have := countable_numberField' K
  have : Countable (NumberField.RingOfIntegers K) :=
    Function.Injective.countable (NumberField.RingOfIntegers.coe_injective (K := K))
  have hI : Countable (Ideal (NumberField.RingOfIntegers K)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (NumberField.RingOfIntegers K) => Ideal.span (s : Set (NumberField.RingOfIntegers K))) ?_
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact Function.Injective.countable
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) => v.asIdeal)
    (fun v w h => IsDedekindDomain.HeightOneSpectrum.ext h)

private theorem univ_le_preimage_inf_of_univ_le (K : Type) [Field K] [NumberField K] :
    T2Space (NumberField.InfiniteAdeleRing K) ∧ SecondCountableTopology (NumberField.InfiniteAdeleRing K) := by
  have h : ∀ v : NumberField.InfinitePlace K, SecondCountableTopology v.Completion := fun v =>
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact ⟨inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion)),
    inferInstanceAs (SecondCountableTopology ((v : NumberField.InfinitePlace K) → v.Completion))⟩

private theorem fin_lemma_4 (K : Type) [Field K] [NumberField K] :
    T2Space (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) ∧
      SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) := by
  have := countable_numberField' K
  have := countable_heightOneSpectrum_ringOfIntegers K
  have hsep : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      SecondCountableTopology (v.adicCompletion K) := by
    intro v
    have : TopologicalSpace.SeparableSpace (v.adicCompletion K) :=
      ⟨⟨_, Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v⟩⟩
    exact UniformSpace.secondCountable_of_separable _
  have hopen : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    Valued.isOpen_valuationSubring _
  unfold IsDedekindDomain.FiniteAdeleRing
  constructor
  · exact T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  · have hS : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (Filter.cofinite : Filter (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) ≤
          Filter.principal ((s : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ) :=
      fun s => Filter.le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have hemb : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        Topology.IsOpenEmbedding (RestrictedProduct.inclusion (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (hS s)) := fun s =>
      RestrictedProduct.isOpenEmbedding_inclusion_principal hopen (hS s)
    have hsc : ∀ s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        SecondCountableTopology (Set.range (RestrictedProduct.inclusion (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) (hS s))) := by
      intro s
      have : SecondCountableTopology (RestrictedProduct (fun v => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
          (Filter.principal ((s : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ))) :=
        RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
      exact (hemb s).isEmbedding.toHomeomorph.symm.secondCountableTopology
    refine @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ _ hsc (fun s => (hemb s).isOpen_range) ?_
    refine Set.eq_univ_of_forall fun x => ?_
    have hx := Filter.eventually_cofinite.mp x.2
    refine Set.mem_iUnion.mpr ⟨hx.toFinset, ⟨x.1, ?_⟩, rfl⟩
    exact Filter.eventually_principal.mpr fun v hv => by simpa using hv

private theorem AF_t2_secondCountable (K : Type) [Field K] [NumberField K] :
    T2Space (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) ∧ SecondCountableTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) := by
  obtain ⟨h1, h2⟩ := univ_le_preimage_inf_of_univ_le K
  obtain ⟨h3, h4⟩ := fin_lemma_4 K
  exact ⟨inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)),
    inferInstanceAs (SecondCountableTopology (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))⟩

private theorem AE_t2_secondCountable_locallyCompact (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    T2Space (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) ∧ SecondCountableTopology (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) ∧
      LocallyCompactSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) := by
  obtain ⟨h1, h2⟩ := AF_t2_secondCountable K
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := K) (E := L)
  have : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) := inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K))
  have : ContinuousAdd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L)) :=
    IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L))
  let b := Module.finBasis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L))
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hc' : Continuous b.equivFun.symm := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  let h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := K) (E := L) ≃ₜ (Fin _ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF K) :=
    { toEquiv := b.equivFun.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  exact ⟨h.isEmbedding.t2Space, h.isEmbedding.secondCountableTopology, h.isClosedEmbedding.locallyCompactSpace⟩

private theorem GL_t2_secondCountable_locallyCompact (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [SecondCountableTopology R] [LocallyCompactSpace R] (n : ℕ) :
    T2Space (GL (Fin n) R) ∧ SecondCountableTopology (GL (Fin n) R) ∧ LocallyCompactSpace (GL (Fin n) R) := by
  have : T2Space (Matrix (Fin n) (Fin n) R) := inferInstanceAs (T2Space (Fin n → Fin n → R))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  let ι : GL (Fin n) R → Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R := fun g => (↑g, ↑g⁻¹)
  have he : Topology.IsEmbedding ι := by
    exact ((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp Units.isEmbedding_embedProduct
  have hr : Set.range ι = {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.mul_inv, g.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨p.1, p.2, h1, h2⟩, rfl⟩
  have hcl : IsClosed (Set.range ι) := by
    rw [hr]
    exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
      (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
  have hce : Topology.IsClosedEmbedding ι := ⟨he, hcl⟩
  exact ⟨he.t2Space, he.secondCountableTopology, hce.locallyCompactSpace⟩

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  obtain ⟨h1, h2⟩ := AF_t2_secondCountable F
  have := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop (F := F) (E := E)
  have : IsTopologicalRing (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
  obtain ⟨a1, a2, a3⟩ := AE_t2_secondCountable_locallyCompact F E
  obtain ⟨g1, g2, g3⟩ := GL_t2_secondCountable_locallyCompact (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) n
  have : T2Space (Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (T2Space (Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    IsModuleTopology.continuous_of_linearMap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ).toLinearMap
  have hcl : IsClosed (GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) :
      Set (GL (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) :=
    isClosed_eq (((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul
      (Units.continuous_val.matrix_map hc)) continuous_const
  have hlc := hcl.locallyCompactSpace
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA
  exact ⟨hlc, Topology.IsEmbedding.subtypeVal.secondCountableTopology, inferInstance⟩

theorem continuous_ht (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (ht : UA σ J → ℝ≥0) := by
  exact (GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val

theorem grpTop_of : GrpTop := by
  unfold GrpTop
  intro F E _ _ _ _ _ σ _ n J _
  have hE : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hM : Countable (Matrix (Fin n) (Fin n) E) := by
    unfold Matrix
    infer_instance
  have hG : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) (fun a b hab => Units.ext hab)
  let f := Matrix.GeneralLinearGroup.map (n := Fin n)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F))
  have hR : Countable (Set.range f) := (Set.countable_range f).to_subtype
  refine ⟨(lcsc_UA σ J).1, (lcsc_UA σ J).2.1, (lcsc_UA σ J).2.2, ?_,
    GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J,
    Units.continuous_val.comp continuous_subtype_val, ?_, ?_⟩
  · have key : ∀ x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J,
        ((x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) : GL (Fin n) _) ∈ Set.range f :=
      fun x => MonoidHom.mem_range.mp x.2
    refine Function.Injective.countable
      (f := fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ J => (⟨_, key x⟩ : Set.range f)) ?_
    intro x y h
    have h0 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h0)
  · intro g h
    rfl
  · intro Ω hΩ
    obtain ⟨C, hC⟩ := (hΩ.image (continuous_ht σ J)).bddAbove
    exact ⟨C, fun g hg => hC ⟨g, hg, rfl⟩⟩

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fv_exists_skew (hσ : IsCMExt F E σ) : ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  obtain ⟨-, hE, -, hc⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hss : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hc, hc, star_star])
  by_contra hn
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have hx : x - σ x = 0 := by
    by_contra h
    exact hn ⟨_, h, by rw [map_sub, hss, neg_sub]⟩
  have h2 := hc τ x
  rw [← sub_eq_zero.1 hx] at h2
  exact h2.symm

theorem fv_exists_herm (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : EpsHerm σ J) :
    ∃ c : E, c ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (c • J)ᵀ := by
  have hd : ∀ c : E, c ≠ 0 → ((c • J)ᵀ).det ≠ 0 := fun c hc => by
    rw [Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hJ.2
  rcases hJ.1 with h | h
  · exact ⟨1, one_ne_zero, fun i j => by simpa using h j i, hd 1 one_ne_zero⟩
  · obtain ⟨c, hc, hs⟩ := fv_exists_skew hσ
    refine ⟨c, hc, fun i j => ?_, hd c hc⟩
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs, h j i]
    ring

omit [NumberField E] in
theorem fv_HR_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    UG (cA σ) (incM F J) = HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (c • J)ᵀ := by
  have hu : IsUnit (inclR (F := F) (AF F) c) := (IsUnit.mk0 c hc).map _
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ = (inclR (F := F) (AF F) c • incM F J)ᵀ := by
    ext i j
    exact map_mul (inclR (F := F) (AF F)) c (J j i)
  ext g
  show g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J ↔
    (g.1.map (cA σ))ᵀ * HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ * g.1 = HeckeCharacterZeroLocus.SiegelWeilU.JR (F := F) (AF F) (c • J)ᵀ
  rw [hJ]
  have e : (g.1.map (cA σ))ᵀ * (inclR (F := F) (AF F) c • incM F J)ᵀ * g.1 =
      (inclR (F := F) (AF F) c • (g.1ᵀ * incM F J * g.1.map (cA σ)))ᵀ := by
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc]
  rw [e, Matrix.transpose_inj, hu.smul_left_cancel]

omit [NumberField E] in
theorem fv_rat_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))).range.subgroupOf (HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ J) =
      HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F)
  ext g
  rw [HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have h : ((γ.1.map (inclR (F := F) (AF F))).map (sigR (AF F) σ))ᵀ * J.map (inclR (F := F) (AF F)) *
        γ.1.map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F)) := by
      have h0 := g.2
      rw [← hγ] at h0
      exact h0
    show (γ.1.map (σ : E →+* E))ᵀ * J * γ.1 = J
    refine Matrix.map_injective hinj ?_
    show ((γ.1.map (σ : E →+* E))ᵀ * J * γ.1).map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F))
    rw [Matrix.map_mul, Matrix.map_mul]
    exact h
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩

theorem fundamental_domain_finite_volume (hσ : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (S : Subgroup (GL (Fin n) (AE F E))) (hS : S = HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ J) :
    letI : MeasurableSpace S := borel S
    ∀ (μ : Measure S) (D : Set S), μ.IsHaarMeasure →
      IsFundamentalDomain ((Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))).range.subgroupOf S) D μ →
        μ D < ⊤ := by
  subst hS
  rw [fv_rat_eq]
  intro μ D hμ hD
  exact ((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hσ n J hJ).2 μ hμ).2 D hD

theorem finVolU : FinVolU := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  obtain ⟨c, hc, h⟩ := fv_exists_herm hσ hJ
  exact fundamental_domain_finite_volume hσ _ h _ (fv_HR_eq J hc)

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.Parity
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ParityOfCoefficients

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem neg_mem_schA {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) : (fun x => Φ (-x)) ∈ schA F κ := by
  classical
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f,
      fun y => g (-y), ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩, ?_⟩
    funext x
    simp only [pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.neg_apply]
    congr 2
    funext i
    exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem exists_haar : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure ∧
    ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ := by
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (κ → AF F)) := inferInstance
  exact ⟨Measure.addHaarMeasure K, inferInstance, fun f => integral_neg_eq_self f _⟩

theorem coef_neg (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F))
    (hμ : ∀ f : (κ → AF F) → ℂ, ∫ x, f (-x) ∂μ = ∫ x, f x ∂μ) (Φ₁ Φ₂ : (κ → AF F) → ℂ)
    (w : (κ → AF F) × (κ → AF F)) :
    coef F ψ μ Φ₁ Φ₂ (-w) = coef F ψ μ (fun x => Φ₁ (-x)) (fun x => Φ₂ (-x)) w := by
  unfold coef
  rw [← hμ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [schr, Prod.fst_neg, Prod.snd_neg, neg_dotProduct_neg, neg_add]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

def negOne (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J :=
  ⟨-1, by
    change ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F J *
      ((-1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F J
    rw [Units.val_neg, Units.val_one, Matrix.map_neg _ (map_neg (cA σ)),
      Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]
    simp⟩

theorem mat_negOne_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (negOne σ J)⁻¹ = -1 := rfl

theorem mat_one_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mat (1 : UA σ J)⁻¹ = 1 := rfl

end ParityOfCoefficients


open ParityOfCoefficients in
theorem parity_of (hC : CoefEq) (hF : FourierInj) : Parity := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨μ, hμ, hneg⟩ := exists_haar (F := F) (κ := Fin n × Fin d)
  have pres : ∀ Φ ∈ schA F (Fin n × Fin d), om (negOne σ X.J, 1) Φ ∈ schA F (Fin n × Fin d) :=
    fun Φ hΦ => (IsUWeilPair.isUSplitting hp.weil).pres _ Φ hΦ
  have key : ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ x u,
      om (negOne σ X.J, 1) Φ₁ x * (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₂ u) =
        Φ₁ (-x) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro Φ₁ h₁ Φ₂ h₂
    refine hF F _ B.ψ hp.base.std μ hμ _ (pres _ h₁) _ (pres _ h₂) _ (neg_mem_schA h₁) _ (neg_mem_schA h₂) ?_
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂, ← coef_neg B.ψ μ hneg, mat_negOne_inv,
      mat_one_inv, Matrix.transpose_one, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul, map_neg]
  by_cases h0 : ∃ Φ₀ ∈ schA F (Fin n × Fin d), ∃ u, Φ₀ (-u) ≠ 0
  · obtain ⟨Φ₀, hΦ₀, u, hu⟩ := h0
    have h1 := congrArg norm (key Φ₀ hΦ₀ Φ₀ hΦ₀ u u)
    simp only [norm_mul, Complex.norm_conj] at h1
    have h2 : ‖om (negOne σ X.J, 1) Φ₀ u‖ = ‖Φ₀ (-u)‖ :=
      (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp h1
    have h3 : ‖Φ₀ (-u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h4 : (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u) ≠ 0 := by
      rw [← norm_ne_zero_iff, Complex.norm_conj, h2]; exact h3
    refine ⟨negOne σ X.J, (starRingEnd ℂ) (Φ₀ (-u)) / (starRingEnd ℂ) (om (negOne σ X.J, 1) Φ₀ u), rfl, ?_,
      fun Φ hΦ => funext fun x => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, h2, div_self h3]
    · rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key Φ hΦ Φ₀ hΦ₀, mul_comm]
  · refine ⟨negOne σ X.J, 1, rfl, norm_one, fun Φ hΦ => ?_⟩
    have z : ∀ Ψ ∈ schA F (Fin n × Fin d), Ψ = 0 := fun Ψ hΨ => funext fun x => by
      by_contra hx
      exact h0 ⟨Ψ, hΨ, -x, by rwa [neg_neg]⟩
    rw [z _ (pres Φ hΦ), one_smul, z _ (neg_mem_schA hΦ)]

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientMeasure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def e0 : AF F := ((0 : Ainf F), (1 : Af F))

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evI F) z ↔ e0 F • z = 0 := by
  constructor
  · intro h
    apply h
    show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  · intro h u hu
    have hu1 : u.1 = 0 := by
      have hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)
    have hue : u = u * e0 F := by
      refine Prod.ext ?_ ?_
      · show u.1 = u.1 * (0 : Ainf F)
        rw [hu1, zero_mul]
      · show u.2 = u.2 * (1 : Af F)
        rw [mul_one]
    rw [hue, mul_smul, h, smul_zero]

variable (F) in
theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  haveI : T2Space (NumberField.InfiniteAdeleRing F) :=
    show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance
  show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  infer_instance

variable (F E) in
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI := t2Space_adeleRing_of_numberField F
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)

variable (F E) in
theorem ring_AE : IsTopologicalRing (AE F E) := by
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

omit [NumberField E] in
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  let φ : AF F →+* ℂ := (NumberField.InfinitePlace.Completion.extensionEmbedding w).comp
    (GlobalTheory.AdelicU.evInf F w).toRingHom
  have hφ : Continuous φ :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
  letI : Module (AF F) ℂ := Module.compHom ℂ φ
  haveI : ContinuousSMul (AF F) ℂ := ⟨(hφ.comp continuous_fst).mul continuous_snd⟩
  have hpt : ∀ (b : AF F) (e : E), piInf τ (b ⊗ₜ[F] e) = φ b * (τ.1 e) := fun b e => rfl
  let Lm : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := by
        intro a x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b e =>
          rw [TensorProduct.smul_tmul', hpt, hpt, smul_eq_mul, map_mul]
          show φ a * φ b * τ.1 e = φ a * (φ b * τ.1 e)
          ring
        | add x y hx hy =>
          rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add] }
  exact IsModuleTopology.continuous_of_linearMap Lm

variable {n d : ℕ}

theorem continuous_sz (τ : ∀ w : InfinitePlace F, EmbOver E w) : Continuous (sz τ : Ten F E n d → ℝ) := by
  exact continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm

theorem isClosed_supp {C : Set (Ten F E n d)} (hC : IsCompact C) :
    IsClosed {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} := by
  haveI := t2Space_cm_host_adeles F E
  have hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} =
      (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]
    constructor
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
  rw [hset]
  exact (hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))

theorem measurable_maj {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {C : Set (Ten F E n d)} (hC : IsCompact C) (N : ℕ)
    {f : G → Ten F E n d} (hf : Continuous f) : Measurable fun g => maj τ C N (f g) := by
  have hcl := isClosed_supp (F := F) (E := E) (n := n) (d := d) hC
  delta maj
  refine Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const
  exact ((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv

omit [NumberField E] in
theorem continuous_mat_inv {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g⁻¹ := by
  exact Units.continuous_coe_inv.comp continuous_subtype_val

end LatticeQuotientMeasure


open LatticeQuotientMeasure in
theorem latMeas : LatMeas := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h
  haveI := ring_AE F E
  haveI := t2Space_cm_host_adeles F E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩
  delta latSum
  refine Measurable.tsum fun x => ENNReal.measurable_ofReal.comp ?_
  exact measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)

end PositivityTheory.ThKEst

end
end
