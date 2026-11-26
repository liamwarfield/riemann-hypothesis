module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialChart

theorem comap_biSup_finset {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y)
    (I : ι → Y.IdealSheafData) (S : Finset ι) :
    (⨆ j ∈ S, I j).comap f = ⨆ j ∈ S, (I j).comap f := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.iSup_insert, Finset.iSup_insert, Scheme.IdealSheafData.comap_sup, ih]

theorem restrictIdeal_biSup_finset {X : Scheme.{u}} {ι : Type v} (U : X.Opens)
    (I : ι → X.IdealSheafData) (S : Finset ι) :
    restrictIdeal (⨆ j ∈ S, I j) U = ⨆ j ∈ S, restrictIdeal (I j) U :=
  comap_biSup_finset U.ι I S

private theorem ofIdealTop_sup {X : Scheme.{u}} [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  ext U : 2
  simp [Scheme.IdealSheafData.ofIdealTop, Ideal.map_sup]

theorem coordSubspaceIdeal_insert (k : Type u) [Field k] (m : ℕ) (j : Fin m)
    (S : Finset (Fin m)) :
    coordSubspaceIdeal k m (insert j S) =
      coordSubspaceIdeal k m {j} ⊔ coordSubspaceIdeal k m S := by
  classical
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Finset.coe_singleton,
    Set.image_singleton, ofIdealTop_sup]

theorem coordSubspaceIdeal_eq_biSup_singleton (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S = ⨆ j ∈ S, coordSubspaceIdeal k m {j} := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [coordSubspaceIdeal_empty]
  · intro a s _ ih
    rw [coordSubspaceIdeal_insert, ih, Finset.iSup_insert]

theorem coordIdeal_eq_biSup_singleton {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) (c : EtaleChart p U m)
    (S : Finset (Fin m)) :
    c.coordIdeal S = ⨆ j ∈ S, c.coordIdeal {j} := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_biSup_singleton, comap_biSup_finset]
  exact iSup_congr fun j => iSup_congr fun _ => (c.coordIdeal_eq_comap_coordSubspaceIdeal {j}).symm

theorem orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ D ∈ T.boundary, ∀ x : ↥T.scheme, x ∈ D.support → orderAt D x = 1 := by
  intro T hT D hD x hx
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  obtain ⟨i, hi, hDi⟩ := List.mem_iff_getElem.1 hD
  cases hai : a i with
  | none =>
      refine absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ x hxU)
      rw [← hDi]
      exact hnone i hi hai
  | some t =>
      obtain ⟨V, m', hxV, hVU', hV, -⟩ := exists_etaleChart_le T.structMap x U hxU
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        rw [← hDi]
        exact hsome i hi t hai
      have hDV : restrictIdeal D V = (c.restrict hVU').coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c D {t} hDU
      exact orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton T.structMap hV
        (c.restrict hVU') t D hDV x hxV hx

theorem smooth_intersectionIdeal_subscheme : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) := by
  classical
  intro T hT J
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal (p := T.structMap) (intersectionIdeal T.boundary J) ?_
  intro x hx
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  have hle : ∀ j ∈ J, T.boundary.get j ≤ intersectionIdeal T.boundary J := by
    intro j hj
    rw [intersectionIdeal_eq_iSup]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => T.boundary.get j) j hj
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro hcon
    have h2 := stalkIdeal_mono (hle j hj) x
    rw [hcon] at h2
    exact (mem_support_iff_stalkIdeal_ne_top _ _).1 hx (top_le_iff.1 h2)
  have hsomej : ∀ j ∈ J, ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    cases haj : a (j : ℕ) with
    | none =>
        refine absurd (hxj j hj)
          (notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U ?_ x hxU)
        rw [List.get_eq_getElem]
        exact hnone (j : ℕ) j.isLt haj
    | some t => exact ⟨t, rfl⟩
  refine ⟨U, hxU, m, c, J.biUnion (fun j => (a (j : ℕ)).toFinset), ?_⟩
  have h1 : restrictIdeal (intersectionIdeal T.boundary J) U
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) U := by
    rw [intersectionIdeal_eq_iSup]
    exact restrictIdeal_biSup_finset U (fun j => T.boundary.get j) J
  have h2 : c.coordIdeal (J.biUnion (fun j => (a (j : ℕ)).toFinset))
      = ⨆ t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset), c.coordIdeal {t} :=
    coordIdeal_eq_biSup_singleton T.structMap U m c _
  rw [h1, h2]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => iSup_le fun hj => ?_
    obtain ⟨t, ht⟩ := hsomej j hj
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    have htS : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset) :=
      Finset.mem_biUnion.2 ⟨j, hj, by simp [ht]⟩
    rw [hres]
    exact le_iSup₂
      (f := fun t (_ : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset)) =>
        c.coordIdeal ({t} : Finset (Fin m))) t htS
  · refine iSup_le fun t => iSup_le fun htS => ?_
    obtain ⟨j, hj, htj⟩ := Finset.mem_biUnion.1 htS
    have ht : a (j : ℕ) = some t := Option.mem_def.1 (Option.mem_toFinset.1 htj)
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    rw [← hres]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => restrictIdeal (T.boundary.get j) U) j hj

end MonomialChart

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponents
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_irreducibleComponents_iff_isIrreducible_and_maximal {α : Type*}
    [TopologicalSpace α] (s : Set α) :
    s ∈ irreducibleComponents α ↔
      IsIrreducible s ∧ ∀ t : Set α, IsIrreducible t → s ⊆ t → t ⊆ s :=
  ⟨fun h => ⟨h.1, fun _ ht hst => h.2 ht hst⟩, fun h => ⟨h.1, fun t ht hst => h.2 t ht hst⟩⟩

private theorem maximal_irreducible_subset_range_iff {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) {S : Set β}
    (hr : Set.range f = S) (C : Set β) :
    (IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set β, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C)
      ↔ ∃ D ∈ irreducibleComponents α, f '' D = C := by
  constructor
  · rintro ⟨hirr, hsub, hmax⟩
    have hCr : C ⊆ Set.range f := by rw [hr]; exact hsub
    have himg : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCr
    refine ⟨f ⁻¹' C, (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mpr ⟨?_, ?_⟩, himg⟩
    · exact isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hirr hCr
    · intro t ht hDt x hx
      have himgt : IsIrreducible (f '' t) := ht.image f hf.continuous.continuousOn
      have hCt : C ⊆ f '' t := by
        rw [← himg]
        exact Set.image_mono hDt
      have htS : f '' t ⊆ S := by
        rw [← hr]
        exact Set.image_subset_range _ _
      have heq : f '' t = C := hmax _ himgt hCt htS
      have hmem : f x ∈ C := by
        rw [← heq]
        exact ⟨x, hx, rfl⟩
      exact hmem
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hDirr, hDmax⟩ := (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mp hD
    refine ⟨hDirr.image f hf.continuous.continuousOn, ?_, ?_⟩
    · rw [← hr]
      exact Set.image_subset_range _ _
    · intro C' hC' hsub' hS'
      have hC'r : C' ⊆ Set.range f := by rw [hr]; exact hS'
      have hirr' : IsIrreducible (f ⁻¹' C') :=
        isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hC' hC'r
      have hDD : D ⊆ f ⁻¹' C' := fun x hx => hsub' ⟨x, hx, rfl⟩
      have h1 : f ⁻¹' C' ⊆ D := hDmax _ hirr' hDD
      have h2 : f '' (f ⁻¹' C') = C' := Set.image_preimage_eq_of_subset hC'r
      apply Set.Subset.antisymm
      · rw [← h2]
        exact Set.image_mono h1
      · exact hsub'

theorem mem_intersectionComponents_iff_exists_irreducibleComponent {Y : Scheme.{u}}
    (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔
      ∃ D ∈ irreducibleComponents ↥(intersectionIdeal L J).subscheme,
        ⇑(intersectionIdeal L J).subschemeι '' D = C := by
  have hemb : Topology.IsClosedEmbedding ⇑(intersectionIdeal L J).subschemeι :=
    Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι
  have hrange : Set.range ⇑(intersectionIdeal L J).subschemeι
      = (↑(intersectionIdeal L J).support : Set ↥Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  exact maximal_irreducible_subset_range_iff hemb hrange C

theorem isClosed_of_mem_intersectionComponents {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (C : Set ↥Y) (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent L J C).mp hC
  exact (Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι).isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ hD)

theorem intersectionComponents_finite (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) : (intersectionComponents T.boundary J).Finite := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have h : intersectionComponents T.boundary J =
      (fun D => ⇑(intersectionIdeal T.boundary J).subschemeι '' D) ''
        irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme := by
    ext C
    rw [mem_intersectionComponents_iff_exists_irreducibleComponent]
    exact Iff.rfl
  rw [h]
  exact Set.Finite.image _ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ..)

private theorem irreducibleComponents_eq_of_inter_nonempty_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)) :
    ∀ C₁ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
        (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
  have := hsm
  rintro C₁ h₁ C₂ h₂ ⟨x, hx₁, hx₂⟩
  exact irreducibleComponents_eq_of_stalk_isDomain _
    (fun z => isDomain_stalk_of_smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) z)
    h₁ h₂ hx₁ hx₂

theorem intersectionComponents_disjoint_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (C C' : Set ↥T.scheme) (hC : C ∈ intersectionComponents T.boundary J)
    (hC' : C' ∈ intersectionComponents T.boundary J) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC
  obtain ⟨D', hD', rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC'
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ ⟨d', hd', he⟩
  have hdd : d' = d := hinj he
  subst hdd
  have hDD : D = D' :=
    irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm D hD D' hD' ⟨d', hd, hd'⟩
  exact hne (by rw [hDD])

theorem isOpen_preimage_sUnion_intersectionComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (𝒞 : Set (Set ↥T.scheme)) (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J) :
    IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞) := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  have key : ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 =
      ⋃₀ {D : Set ↥(intersectionIdeal T.boundary J).subscheme |
        D ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme ∧
          ⇑(intersectionIdeal T.boundary J).subschemeι '' D ∈ 𝒞} := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨C, hC𝒞, hxC⟩ := hx
      obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC𝒞)
      obtain ⟨d, hd, hde⟩ := hxC
      have hdx : d = x := hinj hde
      subst hdx
      exact ⟨D, ⟨hD, hC𝒞⟩, hd⟩
    · rintro x ⟨D, ⟨hD, hD𝒞⟩, hxD⟩
      exact ⟨⇑(intersectionIdeal T.boundary J).subschemeι '' D, hD𝒞, ⟨x, hxD, rfl⟩⟩
  rw [key]
  exact isOpen_sUnion_of_subset_irreducibleComponents
    (irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm) (fun D hD => hD.1)

theorem componentUnionIdeal_support_eq_sUnion (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞 := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hqc : QuasiCompact ((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) := inferInstance
  have hsub : ⋃₀ 𝒞 ⊆ Set.range ⇑(intersectionIdeal T.boundary J).subschemeι := by
    rintro x ⟨C, hC, hxC⟩
    obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC)
    obtain ⟨d, hd, rfl⟩ := hxC
    exact ⟨d, rfl⟩
  have h0 : ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫ (intersectionIdeal T.boundary J).subschemeι)
      = ⇑(intersectionIdeal T.boundary J).subschemeι ∘ ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι := rfl
  have hr2 : Set.range ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι
      = ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 :=
    Scheme.Opens.range_ι _
  have hrange : Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) = ⋃₀ 𝒞 := by
    rw [h0, Set.range_comp, hr2]
    exact Set.image_preimage_eq_of_subset hsub
  have hfin : 𝒞.Finite := (intersectionComponents_finite T hT J).subset h𝒞
  have hclosed : IsClosed (⋃₀ 𝒞) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))
  have h1 : (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme)
      = closure (Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
          (intersectionIdeal T.boundary J).subschemeι)) :=
    Scheme.Hom.support_ker _
  rw [h1, hrange]
  exact hclosed.closure_eq

end FunctorialResolution.EmbeddedResolution

end
end
