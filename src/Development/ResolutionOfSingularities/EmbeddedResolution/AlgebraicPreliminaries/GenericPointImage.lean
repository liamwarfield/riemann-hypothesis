module

public import Mathlib

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
namespace IsOpenMap

theorem mem_closure_singleton_of_apply {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} (hopen : IsOpenMap f) (hinj : Function.Injective f)
    {a b : A} (h : f b ∈ closure ({f a} : Set B)) : b ∈ closure ({a} : Set A) := by
  rw [mem_closure_iff]
  intro O hO hbO
  obtain ⟨y, hymem, hy⟩ := (mem_closure_iff.mp h) (f '' O) (hopen O hO) ⟨b, hbO, rfl⟩
  obtain ⟨z, hzO, hz⟩ := hymem
  rw [Set.mem_singleton_iff] at hy
  have hza : z = a := hinj (hz.trans hy)
  subst hza
  exact ⟨z, hzO, rfl⟩

end IsOpenMap

namespace FunctorialResolution.EmbeddedResolution

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isIrreducible_inter_open {S U : Set X} (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by
  refine ⟨hne, ?_⟩
  rintro u v hu hv ⟨a, ⟨haS, haU⟩, hau⟩ ⟨b, ⟨hbS, hbU⟩, hbv⟩
  obtain ⟨c, hcS, hc⟩ := hS.2 (U ∩ u) (U ∩ v) (hU.inter hu) (hU.inter hv)
    ⟨a, haS, haU, hau⟩ ⟨b, hbS, hbU, hbv⟩
  exact ⟨c, ⟨hcS, hc.1.1⟩, hc.1.2, hc.2.2⟩

theorem closure_inter_open_eq {S U : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by
  apply Set.Subset.antisymm
  · exact hS.closure_subset_iff.mpr Set.inter_subset_left
  · intro x hx
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨c, hcS, hc⟩ := hirr.2 o U ho hU ⟨x, hx, hxo⟩ hne
    exact ⟨c, hc.1, hcS, hc.2⟩

theorem isIrreducible_preimage_of_isEmbedding {f : Y → X} (hf : Topology.IsEmbedding f)
    {T : Set X} (hT : IsIrreducible T) (hTr : T ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' T) := by
  obtain ⟨t, ht⟩ := hT.1
  obtain ⟨y, rfl⟩ := hTr ht
  refine ⟨⟨y, ht⟩, ?_⟩
  rintro u v hu hv ⟨a, haT, hau⟩ ⟨b, hbT, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hf.toIsInducing.isOpen_iff.mp hv
  obtain ⟨c, hcT, hcu, hcv⟩ := hT.2 u' v' hu' hv' ⟨f a, haT, hau⟩ ⟨f b, hbT, hbv⟩
  obtain ⟨z, rfl⟩ := hTr hcT
  exact ⟨z, hcT, hcu, hcv⟩

theorem isGenericPoint_preimage_of_isInducing {f : Y → X} (hf : Topology.IsInducing f)
    {ξ : X} {T : Set X} (h : IsGenericPoint ξ T) {y : Y} (hy : f y = ξ) :
    IsGenericPoint y (f ⁻¹' T) := by
  have h2 : closure ({y} : Set Y) = f ⁻¹' closure (f '' ({y} : Set Y)) :=
    hf.closure_eq_preimage_closure_image _
  rw [Set.image_singleton, hy, IsGenericPoint.def h] at h2
  exact h2

theorem isGenericPoint_image_of_isClosedEmbedding {f : Y → X}
    (hf : Topology.IsClosedEmbedding f) {y : Y} {T : Set Y} (h : IsGenericPoint y T) :
    IsGenericPoint (f y) (f '' T) := by
  have hyT : y ∈ T := IsGenericPoint.mem h
  show closure ({f y} : Set X) = f '' T
  apply Set.Subset.antisymm
  · have hcl : IsClosed (f '' T) := by
      rw [← IsGenericPoint.def h]
      exact hf.isClosedMap _ isClosed_closure
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨y, hyT, rfl⟩)
  · have h2 : f '' closure ({y} : Set Y) ⊆ closure (f '' ({y} : Set Y)) :=
      image_closure_subset_closure_image hf.continuous
    rw [Set.image_singleton] at h2
    rw [← IsGenericPoint.def h]
    exact h2

theorem closure_image_genericPoint {f : X → Y} (hcont : Continuous f) {S : Set X} {ξ : X}
    (hξ : IsGenericPoint ξ S) : closure (f '' S) = closure ({f ξ} : Set Y) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ isClosed_closure
    have hsub := image_closure_subset_closure_image (f := f) (s := ({ξ} : Set X)) hcont
    rw [Set.image_singleton] at hsub
    rw [← hξ]
    exact hsub
  · refine closure_mono ?_
    refine Set.singleton_subset_iff.2 ⟨ξ, ?_, rfl⟩
    rw [← hξ]
    exact subset_closure rfl

theorem isOpen_sUnion_of_irreducibleComponents {Z : Type*} [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Z] (C : Set (Set Z))
    (hdisj : ∀ S ∈ C, ∀ W ∈ irreducibleComponents Z, W ∉ C → Disjoint S W) :
    IsOpen (⋃₀ C) := by
  have hcomp : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hfin : (irreducibleComponents Z \ C).Finite := hcomp.subset Set.sdiff_subset
  have hclosed : IsClosed (⋃₀ (irreducibleComponents Z \ C)) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun i hi => isClosed_of_mem_irreducibleComponents i hi.1
  have heq : ⋃₀ C = (⋃₀ (irreducibleComponents Z \ C))ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨S, hSmem, hxS⟩
      have hx : x ∉ ⋃₀ (irreducibleComponents Z \ C) := by
        rintro ⟨W, ⟨hW, hWC⟩, hxW⟩
        exact Set.disjoint_left.mp (hdisj S hSmem W hW hWC) hxS hxW
      exact hx
    · intro x hx
      rw [Set.mem_compl_iff] at hx
      by_cases hmem : irreducibleComponent x ∈ C
      · exact Set.mem_sUnion_of_mem mem_irreducibleComponent hmem
      · exact absurd (Set.mem_sUnion_of_mem mem_irreducibleComponent
          (Set.mem_sdiff_of_mem (irreducibleComponent_mem_irreducibleComponents x) hmem)) hx
  rw [heq]
  exact hclosed.isOpen_compl

end

section

open AlgebraicGeometry

theorem support_comap_eq {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap f).support : Set X) = f.base ⁻¹' (I.support : Set Y) :=
  congrArg (fun s : TopologicalSpace.Closeds X => (s : Set X))
    (Scheme.IdealSheafData.support_comap I f)

theorem comap_ι_eq_top_of_disjoint {X : Scheme} (I : X.IdealSheafData) (U : X.Opens)
    (h : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by
  have hempty : ((I.comap U.ι).support : Set U) = ∅ := by
    rw [support_comap_eq]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxU : U.ι.base x ∈ (U : Set X) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp h hxU hx
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  exact SetLike.ext' hempty

end

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
namespace FunctorialResolution.EmbeddedResolution

private theorem prod_notMem_of_isPrime {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {I : Ideal R} (hI : I.IsPrime) (g : ι → R) (t : Finset ι) :
    (∀ j ∈ t, g j ∉ I) → ∏ j ∈ t, g j ∉ I := by
  induction t using Finset.induction_on with
  | empty =>
      intro _ h1
      rw [Finset.prod_empty] at h1
      refine hI.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      exact h1
  | @insert a u ha ih =>
      intro h hmem
      rw [Finset.prod_insert ha] at hmem
      rcases hI.mem_or_mem hmem with h1 | h1
      · exact h a (Finset.mem_insert_self a u) h1
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) h1

private theorem span_singleton_mul_eq_inf {R : Type*} [CommRing R] {a b : R}
    (hpa : (Ideal.span ({a} : Set R)).IsPrime) (hb : b ∉ Ideal.span ({a} : Set R)) :
    Ideal.span ({a * b} : Set R) = Ideal.span ({a} : Set R) ⊓ Ideal.span ({b} : Set R) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨b, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨a, mul_comm a b⟩
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hz2
    have hv : v ∈ Ideal.span ({a} : Set R) := (hpa.mem_or_mem hz1).resolve_left hb
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hv
    exact Ideal.mem_span_singleton.mpr ⟨w, by ring⟩

theorem span_singleton_prod_eq_biInf {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ⨅ i ∈ s, Ideal.span ({f i} : Set R) := by
  revert hp hdvd
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp
  | @insert a u ha ih =>
      intro hp hdvd
      have hpa : (Ideal.span ({f a} : Set R)).IsPrime := hp a (Finset.mem_insert_self a u)
      have hP : (∏ i ∈ u, f i) ∉ Ideal.span ({f a} : Set R) := by
        refine prod_notMem_of_isPrime hpa f u ?_
        intro j hj
        exact hdvd a (Finset.mem_insert_self a u) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      have ihu := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij =>
          hdvd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
      rw [Finset.prod_insert ha, span_singleton_mul_eq_inf hpa hP, ihu, Finset.iInf_insert]

theorem isRadical_biInf_span_singleton {R : Type*} [CommRing R] {ι : Type*}
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime) :
    (⨅ i ∈ s, Ideal.span ({f i} : Set R)).IsRadical := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  refine le_trans (Ideal.radical_mono ?_) (hp i hi).isRadical
  exact iInf_le_of_le i (iInf_le _ hi)

theorem isRadical_span_singleton_prod_finset {R : Type*} [CommRing R] {ι : Type*}
    [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    (Ideal.span ({∏ i ∈ s, f i} : Set R)).IsRadical := by
  rw [span_singleton_prod_eq_biInf f s hp hdvd]
  exact isRadical_biInf_span_singleton f s hp

end FunctorialResolution.EmbeddedResolution

namespace IsLocalization

theorem map_eq_map_of_map_eq_map {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S]
    [IsLocalization M T] {I J : Ideal R}
    (h : Ideal.map (algebraMap R S) I = Ideal.map (algebraMap R S) J) :
    Ideal.map (algebraMap R T) I = Ideal.map (algebraMap R T) J := by
  have he : ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom).comp (algebraMap R S)
      = algebraMap R T :=
    RingHom.ext fun r => by
      show (IsLocalization.algEquiv M S T) (algebraMap R S r) = algebraMap R T r
      exact (IsLocalization.algEquiv M S T).commutes r
  have hmap : ∀ K : Ideal R, Ideal.map (algebraMap R T) K =
      Ideal.map ((IsLocalization.algEquiv M S T).toAlgHom.toRingHom)
        (Ideal.map (algebraMap R S) K) := by
    intro K
    rw [Ideal.map_map, he]
  rw [hmap, hmap, h]

end IsLocalization

namespace Ideal

theorem list_prod_le_getElem {R : Type*} [CommRing R] (L : List (Ideal R)) (i : ℕ)
    (hi : i < L.length) : L.prod ≤ (L[i]'hi) := by
  revert i hi
  induction L with
  | nil =>
      intro i hi
      simp at hi
  | cons A L ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [List.prod_cons, List.getElem_cons_zero]
          exact le_trans Ideal.mul_le_inf inf_le_left
      | succ i' =>
          have hi' : i' < L.length := by simpa using hi
          simp only [List.prod_cons, List.getElem_cons_succ]
          exact le_trans (le_trans Ideal.mul_le_inf inf_le_right) (ih i' hi')

end Ideal

namespace KaehlerDifferential

theorem residue_tmul_D_mul_of_mem_maximalIdeal (k : Type*) [CommRing k] (A : Type*)
    [CommRing A]
    [Algebra k A] [IsLocalRing A] (x c : A) (hx : x ∈ IsLocalRing.maximalIdeal A) :
    (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (x * c) =
      IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x) := by
  have hsm : ∀ a : A, a • (1 : IsLocalRing.ResidueField A) = IsLocalRing.residue A a := by
    intro a
    rw [Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq]
  have hx0 : IsLocalRing.residue A x = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hstep : IsLocalRing.residue A c •
        ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A x)
      = (IsLocalRing.residue A c * 1) ⊗ₜ[A] KaehlerDifferential.D k A x := rfl
  rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, hsm, hsm, hx0, TensorProduct.zero_tmul, zero_add, hstep,
    mul_one]

end KaehlerDifferential
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
namespace FunctorialResolution.EmbeddedResolution

open Set TopologicalSpace

theorem isClosed_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsClosed (⋃₀ 𝒜) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents ..
  have hsub : 𝒜 ⊆ irreducibleComponents X := fun C hC => h𝒜 C hC
  rw [Set.sUnion_eq_biUnion]
  exact (hfin.subset hsub).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents _ (h𝒜 C hC))

theorem isOpen_sUnion_of_subset_irreducibleComponents {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X]
    (hsep : ∀ C₁ ∈ irreducibleComponents X, ∀ C₂ ∈ irreducibleComponents X,
      (C₁ ∩ C₂).Nonempty → C₁ = C₂)
    {𝒜 : Set (Set X)} (h𝒜 : ∀ C ∈ 𝒜, C ∈ irreducibleComponents X) :
    IsOpen (⋃₀ 𝒜) := by
  have key : (⋃₀ 𝒜)ᶜ = ⋃₀ (irreducibleComponents X \ 𝒜) := by
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩,
        mem_irreducibleComponent ..⟩
      intro hmem
      exact hy ⟨irreducibleComponent y, hmem, mem_irreducibleComponent ..⟩
    · intro y hyc
      obtain ⟨C, ⟨hC, hCA⟩, hyC⟩ := hyc
      show y ∉ ⋃₀ 𝒜
      intro hy
      obtain ⟨D, hD, hyD⟩ := hy
      have heq : C = D := hsep C hC D (h𝒜 D hD) ⟨y, hyC, hyD⟩
      rw [heq] at hCA
      exact hCA hD
  rw [← isClosed_compl_iff, key]
  exact isClosed_sUnion_of_subset_irreducibleComponents (fun C hC => hC.1)

theorem irreducibleComponents_eq_of_stalk_isDomain (X : AlgebraicGeometry.Scheme)
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X)
    {x : X} (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by
  have := hX x
  obtain ⟨ξ₁, hg₁⟩ := QuasiSober.sober h₁.1 (isClosed_of_mem_irreducibleComponents _ h₁)
  obtain ⟨ξ₂, hg₂⟩ := QuasiSober.sober h₂.1 (isClosed_of_mem_irreducibleComponents _ h₂)
  have hξ₁ : closure {ξ₁} = C₁ := hg₁
  have hξ₂ : closure {ξ₂} = C₂ := hg₂
  have hrange : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} :=
    AlgebraicGeometry.Scheme.range_fromSpecStalk ..
  have hm₁ : ξ₁ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₁]; exact hx₁)
  have hm₂ : ξ₂ ∈ Set.range (X.fromSpecStalk x).base := by
    rw [hrange]
    exact specializes_iff_mem_closure.mpr (by rw [hξ₂]; exact hx₂)
  have hcont : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hirrU : IsIrreducible (Set.univ : Set (PrimeSpectrum (X.presheaf.stalk x))) :=
    IrreducibleSpace.isIrreducible_univ ..
  have himg : IsIrreducible (Set.range (X.fromSpecStalk x).base) := by
    rw [← Set.image_univ]
    exact hirrU.image _ hcont.continuousOn
  have hcl : IsIrreducible (closure (Set.range (X.fromSpecStalk x).base)) := himg.closure
  have hs₁ : C₁ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₁]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₁)
  have hs₂ : C₂ ⊆ closure (Set.range (X.fromSpecStalk x).base) := by
    rw [← hξ₂]
    exact closure_mono (Set.singleton_subset_iff.mpr hm₂)
  have e₁ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₁ := h₁.2 hcl hs₁
  have e₂ : closure (Set.range (X.fromSpecStalk x).base) ⊆ C₂ := h₂.2 hcl hs₂
  exact Set.Subset.antisymm (hs₁.trans e₂) (hs₂.trans e₁)

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme
open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Opens

theorem isClosedImmersion_ι_of_isClosed {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [U.range_ι]; exact hU)

end AlgebraicGeometry.Scheme.Opens

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_iso_subscheme_vanishingIdeal_of_coe_eq {X : Scheme} [IsReduced X]
    (C : X.Opens) (Z : Closeds X) (hZ : (Z : Set X) = (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
  have hCclosed : IsClosed (C : Set X) := by rw [← hZ]; exact Z.2
  have : IsClosedImmersion C.ι :=
    IsClosedImmersion.of_isPreimmersion C.ι (by rw [C.range_ι]; exact hCclosed)
  have hkersupp : ((Scheme.Hom.ker C.ι).support : Set X) = (Z : Set X) := by
    rw [Scheme.Hom.support_ker, C.range_ι, hCclosed.closure_eq]
    exact hZ.symm
  have hZsupp : (Scheme.Hom.ker C.ι).support = Z := TopologicalSpace.Closeds.ext hkersupp
  have hvan : Scheme.IdealSheafData.vanishingIdeal Z = (Scheme.Hom.ker C.ι).radical := by
    rw [← hZsupp]
    exact Scheme.IdealSheafData.vanishingIdeal_support
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := by
    rw [hvan, Scheme.IdealSheafData.support_radical]
    exact hZsupp
  have hrange :
      Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (C : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
    exact hZ
  have hle : Scheme.Hom.ker C.ι ≤
      Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hvan]
    exact Scheme.IdealSheafData.le_radical _
  let φ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ C.toScheme :=
    IsClosedImmersion.lift C.ι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι hle
  have hφ : φ ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  have hφbase : ∀ x, ⇑C.ι (⇑φ x) =
      ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι x := by
    intro x
    rw [← hφ]
    simp
  have hinj : Function.Injective ⇑C.ι := C.ι.isOpenEmbedding.injective
  have hsurj : Function.Surjective ⇑φ := by
    intro y
    have hy : ⇑C.ι y ∈ Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
      rw [hrange, ← C.range_ι]
      exact Set.mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, hinj ?_⟩
    rw [hφbase x]
    exact hx
  have : IsPreimmersion (φ ≫ C.ι) := by rw [hφ]; infer_instance
  have : IsPreimmersion φ := IsPreimmersion.of_comp φ C.ι
  have : IsClosedImmersion φ :=
    IsClosedImmersion.of_isPreimmersion φ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have hker : Scheme.Hom.ker φ = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hsurj.range_eq, closure_univ]
    simp
  have : IsIso φ := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨asIso φ, hφ⟩

theorem exists_iso_subscheme_vanishingIdeal_of_isClosed
    {X : Scheme} [IsReduced X] (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal
        (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι =
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subschemeι :=
  exists_iso_subscheme_vanishingIdeal_of_coe_eq C _ rfl

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.AffineSpaceJacobson
universe u

open AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem jacobsonSpace_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  JacobsonSpace.of_isClosedEmbedding
    (Scheme.homeoOfIso (AffineSpace.SpecIso n (CommRingCat.of k))).isClosedEmbedding

instance instJacobsonSpaceAffineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  jacobsonSpace_affineSpace k n

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ReducedSubscheme
open CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

private theorem isReduced_stalk_of_isAffineOpen {Z : AlgebraicGeometry.Scheme} {V : Z.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (hred : _root_.IsReduced ↥(Z.presheaf.obj (Opposite.op V))) (x : V) :
    _root_.IsReduced ↥(Z.presheaf.stalk x.1) := by
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl
    ↥(Z.presheaf.stalk x.1) hred

private theorem isReduced_presheaf_obj_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] (U : X.affineOpens) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.obj
      (Opposite.op ((TopologicalSpace.Opens.map
        (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U.1))) := by
  have hid : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U
      = RingHom.ker (AlgebraicGeometry.Scheme.Hom.app f U.1).hom := by
    simp
  have hq : _root_.IsReduced (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U) := by
    rw [hid]
    exact isReduced_of_injective (RingHom.kerLift (AlgebraicGeometry.Scheme.Hom.app f U.1).hom)
      (RingHom.kerLift_injective _)
  have hq' : _root_.IsReduced ↥(CommRingCat.of (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U)) := hq
  exact isReduced_of_injective
    ((AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).hom.hom)
    (AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).commRingCatIsoToRingEquiv.injective

private theorem isReduced_stalk_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f]
    (y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base y ∈ U :=
    ⟨(X.affineCover.f (X.affineCover.idx _)).opensRange,
      AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
  have hVaff : AlgebraicGeometry.IsAffineOpen ((TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U) :=
    hU.preimage (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
  have hyV : y ∈ (TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U := hyU
  have hred := isReduced_presheaf_obj_subscheme_ker f ⟨U, hU⟩
  exact isReduced_stalk_of_isAffineOpen hVaff hred ⟨y, hyV⟩

theorem isReduced_subscheme_ker {W X : AlgebraicGeometry.Scheme}
    (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by
  have : ∀ y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
      _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) :=
    fun y => isReduced_stalk_subscheme_ker f y
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DerivationLocalization
universe u v w x

variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]

namespace Derivation

private theorem isUnit_algebraMap_moduleEnd (M : Submonoid S) [IsLocalization M S'] (y : M) :
    IsUnit ((algebraMap S (Module.End S N)) (y : S)) := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units (M := M) S' y
  have hcomm : ∀ (s : S) (c : S') (n : N), c • s • n = s • c • n := by
    intro s c n
    rw [← IsScalarTower.algebraMap_smul S' s n, ← IsScalarTower.algebraMap_smul S' s (c • n),
      smul_smul, smul_smul, mul_comm]
  have h1 : ∀ n : N, (y : S) • (((u⁻¹ : S'ˣ) : S') • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) (((u⁻¹ : S'ˣ) : S') • n), ← hu, smul_smul,
      u.mul_inv, one_smul]
  have h2 : ∀ n : N, ((u⁻¹ : S'ˣ) : S') • ((y : S) • n) = n := by
    intro n
    rw [← IsScalarTower.algebraMap_smul S' (y : S) n, ← hu, smul_smul, u.inv_mul, one_smul]
  exact ⟨⟨(algebraMap S (Module.End S N)) (y : S),
    { toFun := fun n => ((u⁻¹ : S'ˣ) : S') • n
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s n => hcomm s ((u⁻¹ : S'ˣ) : S') n },
    LinearMap.ext fun n => h1 n, LinearMap.ext fun n => h2 n⟩, rfl⟩

private theorem exists_liftToLocalization (D : Derivation R S N) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' N, ∀ s : S, D' (algebraMap S S' s) = D s := by
  have hu : ∀ y : M, IsUnit ((algebraMap S (Module.End S N)) (y : S)) := fun y =>
    isUnit_algebraMap_moduleEnd (S' := S') M y
  have : IsLocalizedModule M (KaehlerDifferential.map R R S S') := inferInstance
  refine ⟨(LinearMap.extendScalarsOfIsLocalization M S'
      (IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu)).compDer (KaehlerDifferential.D R S'), fun s => ?_⟩
  show IsLocalizedModule.lift M (KaehlerDifferential.map R R S S') D.liftKaehlerDifferential hu
      (KaehlerDifferential.D R S' (algebraMap S S' s)) = D s
  have key : IsLocalizedModule.lift M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu
        (KaehlerDifferential.map R R S S' (KaehlerDifferential.D R S s))
      = D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun
      (IsLocalizedModule.lift_comp M (KaehlerDifferential.map R R S S')
        D.liftKaehlerDifferential hu) (KaehlerDifferential.D R S s)
  rw [← KaehlerDifferential.map_D R R S S' s, key]
  exact D.liftKaehlerDifferential_comp_D s

theorem exists_mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] :
    ∃ D' : Derivation R S' S', ∀ s : S,
      D' (algebraMap S S' s) = algebraMap S S' (D s) := by
  obtain ⟨D', hD'⟩ :=
    exists_liftToLocalization (S' := S') (N := S') ((Algebra.linearMap S S').compDer D) M
  exact ⟨D', fun s => hD' s⟩

noncomputable def mapToLocalization (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] : Derivation R S' S' :=
  (exists_mapToLocalization (S' := S') D M).choose

@[simp]
theorem mapToLocalization_algebraMap (D : Derivation R S S) (M : Submonoid S)
    [IsLocalization M S'] (s : S) :
    (D.mapToLocalization (S' := S') M) (algebraMap S S' s) = algebraMap S S' (D s) :=
  (exists_mapToLocalization (S' := S') D M).choose_spec s

theorem exists_derivation_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D s = algebraMap S S' (D₀ s) := by
  obtain ⟨ψ, m, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    M (Algebra.linearMap S S') D.liftKaehlerDifferential
  refine ⟨m, LinearMap.compDer ψ (KaehlerDifferential.D R S), fun s => ?_⟩
  have h1 : algebraMap S S' (ψ (KaehlerDifferential.D R S s))
      = (m : S) • D.liftKaehlerDifferential (KaehlerDifferential.D R S s) :=
    LinearMap.congr_fun hψ (KaehlerDifferential.D R S s)
  rw [Derivation.liftKaehlerDifferential_comp_D, Algebra.smul_def] at h1
  exact h1.symm

theorem exists_derivation_mul_eq_of_isLocalization (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S' S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₀ s) := by
  obtain ⟨m, D₀, h⟩ := exists_derivation_mul_eq (S' := S') M (D.compAlgebraMap S)
  exact ⟨m, D₀, fun s => h s⟩

end Derivation
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.OpenImmersionAppLE
namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace IsOpenImmersion

theorem bijective_appLE_of_image_eq {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
    (O : B.Opens) (S : A.Opens) (e : S ≤ f ⁻¹ᵁ O) (h : f ''ᵁ S = O) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE f O S e)) := by
  subst h
  have : IsIso (Scheme.Hom.appLE f (f ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' f S]
    infer_instance
  constructor
  · intro a b hab
    have h1 : (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) a
        = (CommRingCat.Hom.hom (Scheme.Hom.appLE f (f ''ᵁ S) S e ≫
          inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) b := by
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hab]
    rw [IsIso.hom_inv_id] at h1
    simpa only [CommRingCat.hom_id, RingHom.id_apply] using h1
  · intro y
    refine ⟨(CommRingCat.Hom.hom (inv (Scheme.Hom.appLE f (f ''ᵁ S) S e))) y, ?_⟩
    have h3 := congrArg (fun mm => (CommRingCat.Hom.hom mm) y)
      (IsIso.inv_hom_id (Scheme.Hom.appLE f (f ''ᵁ S) S e))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
      RingHom.id_apply] using h3

end IsOpenImmersion

end AlgebraicGeometry
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.CoproductBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FunctorialResolution.EmbeddedResolution

private theorem isIso_sigmaDesc_of_isPullback {ι : Type u} [Finite ι] {P : Scheme.{u}}
    (B C : ι → Scheme.{u}) (f : P ⟶ ∐ B) (j : ∀ a, C a ⟶ B a) (u : ∀ a, C a ⟶ P)
    (hsq : ∀ a, IsPullback (u a) (j a) f (Sigma.ι B a)) : IsIso (Sigma.desc u) := by
  have e1 : (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as) ≫ (colimit.cocone (Discrete.functor B)).ι
      = (Cofan.mk P u).ι ≫ (Functor.const (Discrete ι)).map f := by
    apply NatTrans.ext
    funext x
    obtain ⟨a⟩ := x
    exact ((hsq a).w).symm
  have hpb : ∀ x : Discrete ι, IsPullback ((Cofan.mk P u).ι.app x)
      ((Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B)
        fun a => j a.as).app x) f ((colimit.cocone (Discrete.functor B)).ι.app x) := by
    rintro ⟨a⟩
    exact hsq a
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (colimit.isColimit (Discrete.functor B)) (Cofan.mk P u)
      (Discrete.natTrans (F := Discrete.functor C) (G := Discrete.functor B) fun a => j a.as)
      f e1 (NatTrans.Equifibered.of_discrete _) hpb
  have key : Sigma.desc u
      = (IsColimit.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor C)) hc').hom := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (Discrete.functor C)) hc' ⟨a⟩).symm
  rw [key]
  infer_instance

theorem isPullback_sigmaMap_sigmaDesc {ι : Type u} [Finite ι] {A Y : Scheme.{u}} (i : Y ⟶ A)
    (B C : ι → Scheme.{u}) (j : ∀ a, C a ⟶ B a) (q : ∀ a, C a ⟶ Y) (h : ∀ a, B a ⟶ A)
    (hsq : ∀ a, IsPullback (j a) (q a) (h a) i) :
    IsPullback (Limits.Sigma.map j) (Limits.Sigma.desc q) (Limits.Sigma.desc h) i := by
  have hcomm : ∀ a, (j a ≫ Sigma.ι B a) ≫ Sigma.desc h = q a ≫ i := by
    intro a
    rw [Category.assoc, Sigma.ι_desc]
    exact (hsq a).w
  obtain ⟨u, hufst, husnd⟩ : ∃ u : ∀ a, C a ⟶ pullback (Sigma.desc h) i,
      (∀ a, u a ≫ pullback.fst (Sigma.desc h) i = j a ≫ Sigma.ι B a) ∧
        (∀ a, u a ≫ pullback.snd (Sigma.desc h) i = q a) :=
    ⟨fun a => pullback.lift (j a ≫ Sigma.ι B a) (q a) (hcomm a),
      fun a => pullback.lift_fst _ _ _, fun a => pullback.lift_snd _ _ _⟩
  have hP : IsPullback (pullback.fst (Sigma.desc h) i) (pullback.snd (Sigma.desc h) i)
      (Sigma.desc h) i := IsPullback.of_hasPullback _ _
  have hsq2 : ∀ a, IsPullback (j a) (u a) (Sigma.ι B a) (pullback.fst (Sigma.desc h) i) := by
    intro a
    refine IsPullback.of_bot ?_ (hufst a).symm hP
    rw [husnd a, Sigma.ι_desc]
    exact hsq a
  have : IsIso (Sigma.desc u) :=
    isIso_sigmaDesc_of_isPullback B C (pullback.fst (Sigma.desc h) i) j u
      (fun a => (hsq2 a).flip)
  have hcs : CommSq (Limits.Sigma.map j) (Sigma.desc q) (Sigma.desc h) i := by
    constructor
    apply Sigma.hom_ext
    intro a
    simp [(hsq a).w]
  refine IsPullback.of_iso_pullback hcs (asIso (Sigma.desc u)) ?_ ?_
  · apply Sigma.hom_ext
    intro a
    simp [hufst a]
  · apply Sigma.hom_ext
    intro a
    simp [husnd a]

end FunctorialResolution.EmbeddedResolution
end
