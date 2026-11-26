module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.SiegelWeilFormula

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelRadTop

theorem nA_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (AE F E), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  intro F E _ _ _ _ _ σ n Y b ε h
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have hc : Continuous (cA σ) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hS : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) =
      {β | βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0} := Set.ext h
  have hC : IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hS]
    have h1 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => β.map (cA σ) := continuous_id.matrix_map hc
    have h2 : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => ((ε : ℤ) : AE F E) • β.map (cA σ) :=
      (continuous_const_smul (((ε : ℤ) : AE F E))).comp h1
    exact isClosed_eq (continuous_id.matrix_transpose.add h2) continuous_const
  haveI : LocallyCompactSpace (nA σ Y b) := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (nA σ Y b) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨hC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.SiegelRadTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroupStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.SiegelWeilFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_skew_matrices_locally_compact_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | exact GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | (intros; apply GlobalTheory.CompanionTheory.SiegelRadTop.nA_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequence
open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.FiberInt

variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']

noncomputable def periodized (π : A →+ A') (Γ' : AddSubgroup A') (lam : Measure A) (𝓖 : Set A) :
    Measure A' :=
  Measure.sum fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)

theorem lintegral_periodized {π : A →+ A'} (hπ : Measurable π) {Γ' : AddSubgroup A'} [Countable Γ']
    (lam : Measure A) (𝓖 : Set A) {f : A' → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(periodized π Γ' lam 𝓖) = ∫⁻ x in 𝓖, ∑' γ : Γ', f ((γ : A') + π x) ∂lam := by
  rw [show periodized π Γ' lam 𝓖 = Measure.sum (fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)) from rfl, lintegral_sum_measure,
    lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    rw [lintegral_map hf (measurable_const_add _), lintegral_map _ hπ]
    exact hf.comp (measurable_const_add _)
  · intro γ
    exact (hf.comp ((measurable_const_add _).comp hπ)).aemeasurable

theorem periodized_invariant {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} [lam.IsAddHaarMeasure] {𝓖 : Set A}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) :
    (periodized π Γ' lam 𝓖).IsAddLeftInvariant := by
  constructor
  intro c
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_const_add c),
    lintegral_periodized hπ lam 𝓖 (f := fun y => f (c + y)) (hf.comp (measurable_const_add c)),
    lintegral_periodized hπ lam 𝓖 hf]
  have key : ∀ x : A, ∑' γ : Γ', f (c + ((γ : A') + π x)) = ∑' γ : Γ', f ((γ : A') + π (s c + x)) := by
    intro x
    refine tsum_congr fun γ => ?_
    rw [map_add (f := _), hs]
    congr 1
    abel
  simp_rw [key]
  have hemb : MeasurableEmbedding (fun x : A => s c + x) :=
    (MeasurableEquiv.addLeft (s c)).measurableEmbedding
  rw [(measurePreserving_add_left lam (s c)).setLIntegral_comp_emb hemb
    (fun x => ∑' γ : Γ', f ((γ : A') + π x)) 𝓖]
  have hG' : IsAddFundamentalDomain Γ ((fun x : A => s c + x) '' 𝓖) lam := hG.vadd_of_comm (s c)
  refine hG'.setLIntegral_eq hG _ ?_
  intro g x
  show ∑' γ : Γ', f ((γ : A') + π ((g : A) + x)) = ∑' γ : Γ', f ((γ : A') + π x)
  rw [← (Equiv.addRight (⟨π g, hΓ g g.2⟩ : Γ')).tsum_eq (fun γ : Γ' => f ((γ : A') + π x))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add, map_add (f := _), add_assoc]

instance {π : A →+ A'} {Γ' : AddSubgroup A'} [Countable Γ'] {lam : Measure A} [SFinite lam]
    {𝓖 : Set A} : SFinite (periodized π Γ' lam 𝓖) := by
  unfold periodized; infer_instance

theorem measure_preimage_inter_eq {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} {lam' : Measure A'} [lam.IsAddHaarMeasure]
    [lam'.IsAddHaarMeasure] {𝓖 : Set A} {𝓖' : Set A'}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (hG' : IsAddFundamentalDomain Γ' 𝓖' lam') (h1' : lam' 𝓖' = 1)
    {S : Set A'} (hS : MeasurableSet S) (hinv : ∀ γ ∈ Γ', ∀ x, γ + x ∈ S ↔ x ∈ S) :
    lam (π ⁻¹' S ∩ 𝓖) = lam' (S ∩ 𝓖') := by
  obtain ⟨P, hPdef⟩ : ∃ P, P = periodized π Γ' lam 𝓖 := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = Measure.map π (lam.restrict 𝓖) := ⟨_, rfl⟩
  have hPsum : P = Measure.sum fun γ : Γ' => ν.map ((γ : A') + ·) := by rw [hPdef, hνdef]; rfl
  have : P.IsAddLeftInvariant := by rw [hPdef]; exact periodized_invariant hπ hs hΓ hG
  have : SFinite P := by rw [hPdef]; infer_instance
  have : lam'.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam'
  have : lam'.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lam'
  obtain ⟨M, hMdef⟩ : ∃ M, M = toMeasurable lam' 𝓖' := ⟨_, rfl⟩
  have hMm : MeasurableSet M := by rw [hMdef]; exact measurableSet_toMeasurable lam' 𝓖'
  have hMae : M =ᵐ[lam'] 𝓖' := by rw [hMdef]; exact hG'.nullMeasurableSet.toMeasurable_ae_eq
  have hM1 : lam' M = 1 := by rw [hMdef, measure_toMeasurable, h1']
  have hne : lam' ≠ 0 := fun h => by simp [h] at h1'
  have hPac : P ≪ lam' := absolutelyContinuous_of_isAddLeftInvariant P lam' hne
  have hνP : ν ≤ P := by
    have h0 := Measure.le_sum (fun γ : Γ' => Measure.map (fun y : A' => (γ : A') + y) ν) 0
    simp only [AddSubgroup.coe_zero, zero_add, Measure.map_id'] at h0
    rw [hPsum]
    exact h0
  have hνac : ν ≪ lam' := by
    intro t ht
    exact le_antisymm ((Measure.le_iff'.1 hνP t).trans (hPac ht).le) zero_le
  have claim : ∀ T : Set A', MeasurableSet T → (∀ γ ∈ Γ', ∀ x, γ + x ∈ T ↔ x ∈ T) →
      lam (π ⁻¹' T ∩ 𝓖) = P (T ∩ M) := by
    intro T hT hTinv
    have e1 : lam (π ⁻¹' T ∩ 𝓖) = ν T := by
      rw [hνdef, Measure.map_apply hπ hT, Measure.restrict_apply (hπ hT)]
    rw [e1, hG'.measure_eq_tsum_of_ac hνac T, hPsum, Measure.sum_apply _ (hT.inter hMm)]
    conv_lhs => rw [← (Equiv.neg Γ').tsum_eq]
    refine tsum_congr fun γ => ?_
    rw [Measure.map_apply (measurable_const_add _) (hT.inter hMm)]
    have hpre : (fun x => (γ : A') + x) ⁻¹' (T ∩ M) = T ∩ (fun x => (γ : A') + x) ⁻¹' M := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, hTinv γ γ.2 x]
    have hset : (fun x => (γ : A') + x) ⁻¹' 𝓖' = (Equiv.neg Γ') γ +ᵥ 𝓖' := by
      ext x
      rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
      simp [AddSubgroup.vadd_def]
    have hae : (fun x => (γ : A') + x) ⁻¹' M =ᵐ[lam'] (fun x => (γ : A') + x) ⁻¹' 𝓖' :=
      (measurePreserving_add_left lam' (γ : A')).quasiMeasurePreserving.preimage_ae_eq hMae
    rw [hpre, ← hset]
    exact measure_congr (.inter .rfl (hae.filter_mono hνac.ae_le).symm)
  have hPt : ∀ t, MeasurableSet t → P t = P M * lam' t := by
    intro t ht
    have h := measure_add_lintegral_eq lam' P hMm (t.indicator 1) (measurable_one.indicator ht)
    rw [hM1, one_mul, lintegral_indicator_one ht] at h
    rw [h]
    have hc : ∀ x : A', P ((fun z => z + x) ⁻¹' M) = P M := fun x => by
      simp_rw [add_comm _ x]
      exact measure_preimage_add P x M
    simp_rw [hc]
    rw [lintegral_const_mul (P M) (f := fun x => t.indicator 1 (-x))
      ((measurable_one.indicator ht).comp measurable_neg),
      lintegral_neg_eq_self (t.indicator 1), lintegral_indicator_one ht]
  have hU := claim Set.univ MeasurableSet.univ (fun _ _ _ => by simp)
  rw [Set.preimage_univ, Set.univ_inter, h1, Set.univ_inter] at hU
  rw [claim S hS hinv, hPt _ (hS.inter hMm), ← hU, one_mul]
  exact measure_congr (.inter .rfl hMae)

theorem integral_comp_eq : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by
  intro A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π s hπc _ hs Γ Γ' hΓc hΓ'c hΓ _ lam lam' hlam hlam' 𝓖 𝓖' hG h1 hG' h1' G hGc hGinv
  have := hΓc
  have := hΓ'c
  have := hlam
  have := hlam'
  have hπ : Measurable π := hπc.measurable
  have hGm : Measurable G := hGc.measurable
  have key : Measure.map G (Measure.map π (lam.restrict 𝓖)) = Measure.map G (lam'.restrict 𝓖') := by
    ext B hB
    have hinvB : ∀ γ ∈ Γ', ∀ x, γ + x ∈ G ⁻¹' B ↔ x ∈ G ⁻¹' B := fun γ hγ x => by
      simp only [Set.mem_preimage, hGinv γ hγ x]
    rw [Measure.map_apply hGm hB, Measure.map_apply hGm hB, Measure.map_apply hπ (hGm hB),
      Measure.restrict_apply (hπ (hGm hB)), Measure.restrict_apply (hGm hB)]
    exact measure_preimage_inter_eq hπ hs hΓ hG h1 hG' h1' (hGm hB) hinvB
  calc ∫ x in 𝓖, G (π x) ∂lam = ∫ y, G y ∂(Measure.map π (lam.restrict 𝓖)) :=
        (integral_map hπ.aemeasurable hGc.aestronglyMeasurable).symm
    _ = ∫ z, z ∂(Measure.map G (Measure.map π (lam.restrict 𝓖))) :=
        (integral_map hGm.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ z, z ∂(Measure.map G (lam'.restrict 𝓖')) := by rw [key]
    _ = ∫ x in 𝓖', G x ∂lam' := integral_map hGm.aemeasurable aestronglyMeasurable_id

end GlobalTheory.CompanionTheory.FiberInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequenceStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_split_exact_sequence : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by
  first | exact @GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq | exact GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq | (intros; apply GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq <;> assumption)
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def pad0 (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0

theorem pad_zero_embedding_alt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : pad0 L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [pad0, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]

theorem pad_zero_outside_range (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : pad0 L β i k = 0 := by
  simp only [pad0, dif_neg h]

theorem pad_zero_symm_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (pad0 L β i k) (pad0 L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pad_zero_embedding_alt, pad_zero_embedding_alt]
    exact h1 a c
  · rw [pad_zero_outside_range L β i k h, pad_zero_outside_range L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0

theorem eps_common : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩

theorem pad_zero_mem_nilradical (β : nA σ L.Y L.b) : pad0 L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine pad_zero_symm_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this

def padN : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨pad0 L β.1, pad_zero_mem_nilradical L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine pad_zero_symm_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_embedding_alt]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_outside_range L _ i k h, add_zero]

theorem prj_padN (β : nA σ L.Y L.b) : prj L (padN L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [prj_val, Matrix.submatrix_apply]
  exact pad_zero_embedding_alt L β.1 a c

theorem continuous_padN : Continuous (padN L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [pad_zero_embedding_alt]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [pad_zero_outside_range L _ i k h]
    exact continuous_const

theorem countable_nF (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) : Countable (nF σ Y b) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  refine Function.Injective.countable (f := fun ν : nF σ Y b => Classical.choose (kunf.mem_nF_iff.1 ν.2)) ?_
  intro ν ν' h
  have h1 := Classical.choose_spec (kunf.mem_nF_iff.1 ν.2)
  have h2 := Classical.choose_spec (kunf.mem_nF_iff.1 ν'.2)
  apply Subtype.ext; apply Subtype.ext
  rw [h1, h2]
  exact congrArg _ h

theorem prj_nF {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : prj L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [prj_val, hT]
  rfl

theorem padN_nF {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : padN L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show pad0 L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [pad0, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [pad0, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]

theorem nA_inst (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    LocallyCompactSpace (nA σ Y b) ∧ T2Space (nA σ Y b) := by
  have h := GlobalTheory.T.adelic_skew_matrices_locally_compact_group F E σ n Y b ε (fun β => by
    rw [kunf.mem_nA_iff hε, ← sub_eq_zero, sub_neg_eq_add])
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

theorem fiber {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (prj L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact GlobalTheory.T.haar_measure_split_exact_sequence (prj L) (padN L) (continuous_prj L) (continuous_padN L) (prj_padN L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => prj_nF L hγ)
    (fun γ hγ => padN_nF L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)

end PositivityTheory.SiegelWeilFormula.Act.C4

end
