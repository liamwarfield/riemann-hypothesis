module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import GroundTheory.GlobalFields.InfiniteNormIndex.LocalSymbol
public import GroundTheory.GlobalFields.Adele.IdeleBasis

@[expose] public section

section -- merged from GroundTheory.GlobalFields.NormResidueSymbol.Infinite
namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding
open scoped NumberField.LiesOver ComplexConjugate

noncomputable section

section Conj

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isConj_iff_forall {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} :
    IsConj φ σ ↔ ∀ x, φ (σ x) = star (φ x) :=
  ⟨fun h ↦ h.eq, fun h ↦ RingHom.ext fun x ↦ by
    rw [RingHom.comp_apply, conjugate_coe_eq, starRingEnd_apply]
    exact (h x).symm⟩

theorem isConj_conjugate_iff {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} :
    IsConj (conjugate φ) σ ↔ IsConj φ σ := by
  simp only [isConj_iff_forall, conjugate_coe_eq, starRingEnd_apply]
  constructor
  · intro h x
    simpa using congrArg star (h x)
  · intro h x
    rw [h x]

theorem isConj_iff_of_mk_eq {φ ψ : L →+* ℂ} (h : mk φ = mk ψ) (σ : L ≃ₐ[K] L) :
    IsConj φ σ ↔ IsConj ψ σ := by
  rcases mk_eq_iff.1 h with rfl | rfl
  · rfl
  · exact isConj_conjugate_iff.symm

theorem isConj_comp_iff [IsMulCommutative (L ≃ₐ[K] L)] {φ : L →+* ℂ} {σ ν : L ≃ₐ[K] L} :
    IsConj (φ.comp (ν : L →+* L)) σ ↔ IsConj φ σ := by
  have hc : ∀ y, ν (σ y) = σ (ν y) := fun y ↦ by
    rw [← AlgEquiv.mul_apply, mul_comm' ν σ, AlgEquiv.mul_apply]
  have hν : ∀ y, (ν : L →+* L) y = ν y := fun _ ↦ rfl
  simp only [isConj_iff_forall, RingHom.comp_apply, hν]
  constructor
  · intro h y
    have := h (ν.symm y)
    rwa [hc, AlgEquiv.apply_symm_apply] at this
  · intro h y
    rw [hc]
    exact h (ν y)


open scoped Classical in
def conjOfEmbedding (φ : L →+* ℂ) : L ≃ₐ[K] L :=
  if h : ∃ σ : L ≃ₐ[K] L, IsConj φ σ then h.choose else 1

theorem conjOfEmbedding_eq {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} (hσ : IsConj φ σ) :
    conjOfEmbedding φ = σ := by
  have h : ∃ σ : L ≃ₐ[K] L, IsConj φ σ := ⟨σ, hσ⟩
  rw [conjOfEmbedding, dite_eq_left h]
  exact h.choose_spec.ext hσ

theorem conjOfEmbedding_of_not {φ : L →+* ℂ} (h : ¬ ∃ σ : L ≃ₐ[K] L, IsConj φ σ) :
    conjOfEmbedding (K := K) φ = 1 := by
  rw [conjOfEmbedding, dite_eq_right h]

theorem conjOfEmbedding_congr {φ ψ : L →+* ℂ}
    (h : ∀ σ : L ≃ₐ[K] L, IsConj φ σ ↔ IsConj ψ σ) :
    conjOfEmbedding (K := K) φ = conjOfEmbedding ψ := by
  by_cases hφ : ∃ σ : L ≃ₐ[K] L, IsConj φ σ
  · obtain ⟨σ, hσ⟩ := hφ
    rw [conjOfEmbedding_eq hσ, conjOfEmbedding_eq ((h σ).1 hσ)]
  · rw [conjOfEmbedding_of_not hφ,
      conjOfEmbedding_of_not fun ⟨σ, hσ⟩ ↦ hφ ⟨σ, (h σ).2 hσ⟩]

theorem conjOfEmbedding_mul_self (φ : L →+* ℂ) :
    conjOfEmbedding (K := K) φ * conjOfEmbedding φ = 1 := by
  by_cases hφ : ∃ σ : L ≃ₐ[K] L, IsConj φ σ
  · obtain ⟨σ, hσ⟩ := hφ
    rw [conjOfEmbedding_eq hσ]
    exact AlgEquiv.ext fun x ↦ isConj_apply_apply hσ x
  · rw [conjOfEmbedding_of_not hφ, mul_one]


variable (K) in
def conjAt (w : InfinitePlace L) : L ≃ₐ[K] L :=
  conjOfEmbedding w.embedding

theorem conjAt_mul_self (w : InfinitePlace L) : conjAt K w * conjAt K w = 1 :=
  conjOfEmbedding_mul_self _

theorem conjAt_of_isReal {w : InfinitePlace L} (hw : w.IsReal) : conjAt K w = 1 :=
  conjOfEmbedding_eq (isConj_one_iff.2 (isReal_iff.1 hw))

theorem isConj_conjAt [IsGalois K L] {w : InfinitePlace L} (hw : w.IsRamified K) :
    IsConj w.embedding (conjAt K w) := by
  obtain ⟨σ, hσ⟩ := exists_isConj_of_isRamified (k := K) (φ := w.embedding) (by rwa [mk_embedding])
  rw [conjAt, conjOfEmbedding_eq hσ]
  exact hσ

theorem conjAt_ne_one [IsGalois K L] {w : InfinitePlace L} (hw : w.IsRamified K) :
    conjAt K w ≠ 1 :=
  (isConj_ne_one_iff (isConj_conjAt hw)).2 fun h ↦
    not_isReal_iff_isComplex.2 (isRamified_iff.1 hw).1 (isReal_iff.2 h)

theorem conjAt_smul [IsMulCommutative (L ≃ₐ[K] L)] (τ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    conjAt K (τ • w) = conjAt K w := by
  refine conjOfEmbedding_congr fun σ ↦ ?_
  have h : mk (τ • w).embedding = mk (w.embedding.comp (τ.symm : L →+* L)) := by
    rw [mk_embedding, ← smul_mk, mk_embedding]
  rw [isConj_iff_of_mk_eq h]
  exact isConj_comp_iff

theorem conjAt_eq [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {v : InfinitePlace K}
    (w w' : v.placesOver L) : conjAt K (w : InfinitePlace L) = conjAt K (w' : InfinitePlace L) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  rw [InfinitePlace.coe_smul_placesOver, conjAt_smul]

end Conj

section Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]

theorem extensionEmbedding_algebraMap_self (l : L) :
    extensionEmbedding w (algebraMap L w.Completion l) = w.embedding l := by
  rw [AbsoluteValue.Completion.algebraMap_def, extensionEmbedding_coe]
  simp [WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs]

theorem completionConj_algebraMap (hv : v.IsReal) (l : L) :
    InfinitePlace.completionConj (w := w) hv (algebraMap L w.Completion l) =
      algebraMap L w.Completion (conjAt K w l) := by
  by_cases hw : w.IsComplex
  · have hram : w.IsRamified K :=
      isRamified_iff.2 ⟨hw, by rw [InfinitePlace.LiesOver.comap_eq w v]; exact hv⟩
    apply (extensionEmbedding w).injective
    rw [InfinitePlace.extensionEmbedding_completionConj, extensionEmbedding_algebraMap_self,
      extensionEmbedding_algebraMap_self, (isConj_conjAt hram).eq, starRingEnd_apply]
  · have hw' : w.IsReal := not_isComplex_iff_isReal.1 hw
    rw [InfinitePlace.completionConj, dite_eq_right hw, conjAt_of_isReal hw']
    rfl

end Completion

section Symbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : InfinitePlace K)


open scoped Classical in
def infiniteLocalSymbol : v.Completionˣ →* (L ≃ₐ[K] L) :=
  if hv : v.IsReal then
    (InfinitePlace.realSignHom (conjAt K ((IdeleNorm.nonempty_infinitePlacesOver L v).some :
        InfinitePlace L)) (conjAt_mul_self _)).comp
      (Units.map (extensionEmbeddingOfIsReal hv).toMonoidHom)
  else 1

theorem infiniteLocalSymbol_apply (hv : v.IsReal) (w : v.placesOver L) (x : v.Completionˣ) :
    infiniteLocalSymbol L v x =
      if extensionEmbeddingOfIsReal hv x < 0 then conjAt K (w : InfinitePlace L) else 1 := by
  rw [infiniteLocalSymbol, dite_eq_left hv, MonoidHom.comp_apply, InfinitePlace.realSignHom_apply,
    conjAt_eq _ w]
  rfl


omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
theorem infiniteLocalSymbol_of_not_isReal (hv : ¬ v.IsReal) : infiniteLocalSymbol L v = 1 := by
  rw [infiniteLocalSymbol, dite_eq_right hv]

theorem algebraMap_infiniteLocalSymbol_apply (w : v.placesOver L) (x : v.Completionˣ) (l : L) :
    algebraMap L (w : InfinitePlace L).Completion (infiniteLocalSymbol L v x l) =
      InfinitePlace.localSymbol v (w : InfinitePlace L) x
        (algebraMap L (w : InfinitePlace L).Completion l) := by
  by_cases hv : v.IsReal
  · rw [infiniteLocalSymbol_apply L v hv w, InfinitePlace.localSymbol_apply v _ hv]
    split_ifs
    · exact (completionConj_algebraMap (w : InfinitePlace L) hv l).symm
    · rfl
  · rw [infiniteLocalSymbol_of_not_isReal L v hv, InfinitePlace.localSymbol_of_not_isReal v _ hv]
    rfl

theorem ker_infiniteLocalSymbol (w : v.placesOver L) :
    (infiniteLocalSymbol L v).ker = InfinitePlace.normSubgroup v (w : InfinitePlace L) := by
  by_cases h2 : v.IsReal ∧ (w : InfinitePlace L).IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hram : (w : InfinitePlace L).IsRamified K :=
      isRamified_iff.2 ⟨hw, by rw [InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v]; exact hv⟩
    ext x
    rw [MonoidHom.mem_ker, infiniteLocalSymbol_apply L v hv w,
      InfinitePlace.mem_normSubgroup_iff hv hw]
    have hx0 : extensionEmbeddingOfIsReal hv x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    constructor
    · intro h
      by_contra hneg
      rw [if_pos (lt_of_le_of_ne (not_lt.1 hneg) hx0)] at h
      exact conjAt_ne_one hram h
    · intro h
      rw [if_neg (not_lt.2 h.le)]
  · rw [InfinitePlace.normSubgroup_eq_top (w : InfinitePlace L) h2, eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    by_cases hv : v.IsReal
    · have hw : (w : InfinitePlace L).IsReal := not_isComplex_iff_isReal.1 fun hw ↦ h2 ⟨hv, hw⟩
      rw [infiniteLocalSymbol_apply L v hv w, conjAt_of_isReal hw, ite_self]
    · rw [infiniteLocalSymbol_of_not_isReal L v hv, MonoidHom.one_apply]


open scoped Classical in
theorem range_infiniteLocalNorm_le_ker_infiniteLocalSymbol :
    (IdeleNorm.infiniteLocalNorm L v).range ≤ (infiniteLocalSymbol L v).ker := by
  rintro _ ⟨y, rfl⟩
  change ∏ w : v.placesOver L, Units.map (Algebra.norm v.Completion :
    (w : InfinitePlace L).Completion →* v.Completion) (y w) ∈ _
  exact Subgroup.prod_mem _ fun w _ ↦ by
    rw [ker_infiniteLocalSymbol L v w]
    exact ⟨y w, rfl⟩

theorem continuous_infiniteLocalSymbol : Continuous (infiniteLocalSymbol L v) :=
  continuous_monoidHom_of_isOpen_ker _ (Subgroup.isOpen_mono
    (range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L v)
    (IdeleNorm.isOpen_range_infiniteLocalNorm v))

end Symbol

end

end GroundTheory.Global
end

section -- merged from GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
section -- merged from GroundTheory.GlobalFields.NormResidueSymbol.Abstract
namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem eventually_finiteProj_mem_units (x : IdeleGroup K) :
    ∀ᶠ v in cofinite, finiteProj v x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  filter_upwards [(prodRestrictedEquiv K x).2.2] with v hv
  rw [finiteProj_eq]
  exact hv

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)

theorem hasFiniteMulSupport
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
    (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ φ v (finiteProj v x) := by
  have h : ∀ᶠ v in cofinite, φ v (finiteProj v x) = 1 := by
    filter_upwards [hφ, eventually_finiteProj_mem_units x] with v hv hx
    exact hv hx
  exact eventually_cofinite.1 h

def ideleMap
    (hφ : ∀ᶠ v in cofinite, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker) :
    IdeleGroup K →* G where
  toFun x := (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [finprod_mul_distrib (hasFiniteMulSupport φ hφ x) (hasFiniteMulSupport φ hφ y),
      Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

variable (hφ : ∀ᶠ v in cofinite,
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem ideleMap_apply (x : IdeleGroup K) :
    ideleMap φ φinf hφ x = (∏ᶠ v, φ v (finiteProj v x)) * ∏ w, φinf w (infiniteProj w x) :=
  rfl

@[simp]
theorem ideleMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleMap φ φinf hφ (finiteEmbedding v a) = φ v a := by
  rw [ideleMap_apply, finprod_eq_single _ v fun u hu ↦ by
    rw [finiteProj_finiteEmbedding_of_ne hu, map_one]]
  have h : ∀ w, infiniteProj w (finiteEmbedding v a) = 1 := fun w ↦ Units.ext rfl
  simp [h]

@[simp]
theorem ideleMap_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleMap φ φinf hφ (infiniteEmbedding w a) = φinf w a := by
  rw [ideleMap_apply, Finset.prod_eq_single w (fun u _ hu ↦ by
    rw [infiniteProj_infiniteEmbedding_of_ne hu, map_one]) (fun h ↦ (h (Finset.mem_univ w)).elim)]
  have h : ∀ v, finiteProj v (infiniteEmbedding w a) = 1 := fun v ↦ Units.ext rfl
  simp [h]

theorem ideleMap_eq_one_of_forall_mem
    (N : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (Ninf : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
    (hN : ∀ v, N v ≤ (φ v).ker) (hNinf : ∀ w, Ninf w ≤ (φinf w).ker) {x : IdeleGroup K}
    (hx : ∀ v, finiteProj v x ∈ N v) (hxinf : ∀ w, infiniteProj w x ∈ Ninf w) :
    ideleMap φ φinf hφ x = 1 := by
  rw [ideleMap_apply, finprod_eq_one_of_forall_eq_one fun v ↦ hN v (hx v),
    Finset.prod_eq_one fun w _ ↦ hNinf w (hxinf w), mul_one]

variable [TopologicalSpace G] [DiscreteTopology G]

theorem continuous_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w)) :
    Continuous (ideleMap φ φinf hφ) := by
  have hker : ∀ {X : Type _} [TopologicalSpace X] [Group X] (f : X →* G), Continuous f →
      IsOpen (f.ker : Set X) := fun f hf ↦ by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} : Set G)).preimage hf
  set V : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)ˣ := fun v ↦
    ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∩
      ((φ v).ker : Set (v.adicCompletion K)ˣ) with hVdef
  set W : Set (IdeleGroup K) :=
    {x | (∀ w, infiniteProj w x ∈ ((φinf w).ker : Set (w.Completion)ˣ)) ∧
      ∀ v, finiteProj v x ∈ V v} with hWdef
  have hWo : IsOpen W := (isTopologicalBasis K).isOpen
    ⟨fun w ↦ ((φinf w).ker : Set (w.Completion)ˣ), V, fun w ↦ hker _ (hφinfc w),
      fun v ↦ (isOpen_units_adicCompletionIntegers K v).inter (hker _ (hφc v)),
      hφ.mono fun v hv ↦ Set.inter_eq_left.2 (SetLike.coe_subset_coe.2 hv), rfl⟩
  have h1W : (1 : IdeleGroup K) ∈ W :=
    ⟨fun w ↦ by simp, fun v ↦ by simp [V]⟩
  have hψW : ∀ x ∈ W, ideleMap φ φinf hφ x = 1 := fun x hx ↦
    ideleMap_eq_one_of_forall_mem φ φinf hφ (fun v ↦ (φ v).ker) (fun w ↦ (φinf w).ker)
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun v ↦ (hx.2 v).2) hx.1
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, nhds_discrete G, tendsto_pure]
  exact eventually_of_mem (hWo.mem_nhds h1W) hψW

end IdeleMap

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def localEmbeddingSubgroup : Subgroup (IdeleGroup K) :=
  (⨆ v : HeightOneSpectrum (𝓞 K), (finiteEmbedding v).range) ⊔
    ⨆ w : InfinitePlace K, (infiniteEmbedding w).range

variable {K}

theorem finiteEmbedding_mem_localEmbeddingSubgroup (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)

theorem infiniteEmbedding_mem_localEmbeddingSubgroup (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)

theorem exists_mem_localEmbeddingSubgroup_inv_mul_mem {N : Set (IdeleGroup K)} (hN : N ∈ 𝓝 1)
    (x : IdeleGroup K) : ∃ h ∈ localEmbeddingSubgroup K, h⁻¹ * x ∈ N := by
  classical
  obtain ⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩ := (isTopologicalBasis K).mem_nhds_iff.1 hN
  have hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w := fun w ↦ by simpa using h1.1 w
  have hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v := fun v ↦ by simpa using h1.2 v
  have hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧
        finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite :=
    eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))
  set S := hS.toFinset with hSdef
  set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) *
    ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef
  refine ⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩
  · exact Subgroup.mul_mem _
      (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _)
      (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)
  · have hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ),
        infiniteProj w (finiteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    have hw : infiniteProj w h = infiniteProj w x := by
      simp only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]
      rw [Finset.prod_eq_single w
          (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _)
          (fun hw ↦ (hw (Finset.mem_univ w)).elim)]
      simp
    rw [map_mul, map_inv, hw, inv_mul_cancel]
    exact hU1 w
  · have hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ),
        finiteProj v (infiniteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    by_cases hv : v ∈ S
    · have hv' : finiteProj v h = finiteProj v x := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_single_of_mem v hv
            (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]
        simp
      rw [map_mul, map_inv, hv', inv_mul_cancel]
      exact hV1 v
    · have hv' : finiteProj v h = 1 := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne
            (by rintro rfl; exact hv hu) _)]
      have hvS := hv
      rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hvS
      rw [map_mul, map_inv, hv', inv_one, one_mul, hvS.1]
      exact hvS.2

theorem dense_localEmbeddingSubgroup : Dense (localEmbeddingSubgroup K : Set (IdeleGroup K)) := by
  refine fun x ↦ mem_closure_iff_nhds.2 fun t ht ↦ ?_
  have hN : {y : IdeleGroup K | x * y⁻¹ ∈ t} ∈ 𝓝 (1 : IdeleGroup K) := by
    have hc : Continuous fun y : IdeleGroup K ↦ x * y⁻¹ := continuous_const.mul continuous_inv
    exact hc.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨h, hh, hhN⟩ := exists_mem_localEmbeddingSubgroup_inv_mul_mem hN x
  exact ⟨h, by simpa using hhN, hh⟩

theorem continuous_monoidHom_ext {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {ψ ψ' : IdeleGroup K →* M} (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = ψ' (finiteEmbedding v a))
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = ψ' (infiniteEmbedding w a)) : ψ = ψ' := by
  have hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ' :=
    sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a)
      (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)
  exact MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

theorem eq_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w))
    {ψ : IdeleGroup K →* G} (hψ : Continuous ψ)
    (hfin : ∀ v, ψ.comp (finiteEmbedding v) = φ v)
    (hinf : ∀ w, ψ.comp (infiniteEmbedding w) = φinf w) :
    ψ = ideleMap φ φinf hφ :=
  continuous_monoidHom_ext hψ (continuous_ideleMap φ φinf hφ hφc hφinfc)
    (fun v a ↦ by rw [ideleMap_finiteEmbedding, ← hfin v, MonoidHom.comp_apply])
    (fun w a ↦ by rw [ideleMap_infiniteEmbedding, ← hinf w, MonoidHom.comp_apply])


end IdeleMap

end

end GroundTheory.Global
end

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

abbrev galCommGroup : CommGroup (L ≃ₐ[K] L) :=
  { toGroup := (inferInstance : Group (L ≃ₐ[K] L)), mul_comm := mul_comm' }

attribute [local instance] galCommGroup

def ideleSymbol : IdeleGroup K →* (L ≃ₐ[K] L) :=
  IdeleMap.ideleMap (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)

variable {K}

theorem ideleSymbol_apply (x : IdeleGroup K) :
    ideleSymbol K L x = (∏ᶠ v, localSymbol L v (finiteProj v x)) *
      ∏ w, infiniteLocalSymbol L w (infiniteProj w x) :=
  IdeleMap.ideleMap_apply (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) x

theorem hasFiniteMulSupport_localSymbol (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ localSymbol L v (finiteProj v x) :=
  IdeleMap.hasFiniteMulSupport (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v)
    (eventually_units_le_ker_localSymbol L) x

@[simp]
theorem ideleSymbol_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleSymbol K L (finiteEmbedding v a) = localSymbol L v a :=
  IdeleMap.ideleMap_finiteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) v a

@[simp]
theorem ideleSymbol_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleSymbol K L (infiniteEmbedding w a) = infiniteLocalSymbol L w a :=
  IdeleMap.ideleMap_infiniteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) w a

theorem continuous_ideleSymbol : Continuous (ideleSymbol K L) :=
  IdeleMap.continuous_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w)

theorem isOpen_ker_ideleSymbol : IsOpen ((ideleSymbol K L).ker : Set (IdeleGroup K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage (continuous_ideleSymbol L)

theorem eq_ideleSymbol {ψ : IdeleGroup K →* (L ≃ₐ[K] L)} (hψ : Continuous ψ)
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = localSymbol L v a)
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = infiniteLocalSymbol L w a) :
    ψ = ideleSymbol K L :=
  IdeleMap.eq_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w) hψ
    (fun v ↦ MonoidHom.ext (hfin v)) (fun w ↦ MonoidHom.ext (hinf w))

theorem range_ideleNorm_le_ker_ideleSymbol : (ideleNorm K L).range ≤ (ideleSymbol K L).ker := by
  intro x hx
  obtain ⟨hf, hi⟩ := (IdeleNorm.mem_range_ideleNorm_iff_forall L x).1 hx
  exact IdeleMap.ideleMap_eq_one_of_forall_mem (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)
    (fun v ↦ (IdeleNorm.finiteLocalNorm L v).range)
    (fun w ↦ (IdeleNorm.infiniteLocalNorm L w).range)
    (fun v ↦ range_finiteLocalNorm_le_ker_localSymbol L v)
    (fun w ↦ range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L w) hf hi

@[simp]
theorem ideleSymbol_ideleNorm (y : IdeleGroup L) : ideleSymbol K L (ideleNorm K L y) = 1 :=
  range_ideleNorm_le_ker_ideleSymbol L ⟨y, rfl⟩

end

end GroundTheory.Global
