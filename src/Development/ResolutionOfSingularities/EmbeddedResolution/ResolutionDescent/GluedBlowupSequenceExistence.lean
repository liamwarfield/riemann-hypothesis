module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceDescentDatum
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpensPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

universe u

private theorem isReduced_of_isOpenImmersion_cover {X : Scheme.{u}} {J : Type u} {V : J → Scheme.{u}}
    (m : (j : J) → V j ⟶ X) (hm : ∀ j, IsOpenImmersion (m j))
    (hV : ∀ j, AlgebraicGeometry.IsReduced (V j))
    (hcov : ∀ x : ↥X, ∃ (j : J) (y : ↥(V j)), (m j).base y = x) :
    AlgebraicGeometry.IsReduced X := by
  have : ∀ x : ↥X, _root_.IsReduced ↥(X.presheaf.stalk x) := by
    intro x
    obtain ⟨j, y, hy⟩ := hcov x
    have := hm j
    have := hV j
    subst hy
    exact isReduced_of_injective (CommRingCat.Hom.hom ((m j).stalkMap y))
      (asIso ((m j).stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk X

private theorem exists_sigma_ι_base_eq {J : Type u} (f : J → Scheme.{u}) (x : ↥(∐ f)) :
    ∃ (j : J) (y : ↥(f j)), (Sigma.ι f j).base y = x := by
  refine ⟨((sigmaMk f).symm x).1, ((sigmaMk f).symm x).2, ?_⟩
  rw [← sigmaMk_mk]
  simp

private theorem quasiCompact_of_compactSpace_to_spec_field {k : Type u} [Field k] {V : Scheme.{u}}
    [CompactSpace ↥V] (f : V ⟶ Spec (CommRingCat.of k)) : QuasiCompact f := by
  have : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨fun W hW hW' => ?_⟩
  rcases Set.eq_empty_or_nonempty W with rfl | ⟨z, hz⟩
  · simp
  · have hW2 : W = Set.univ := Set.eq_univ_of_forall fun w => by
      rw [Subsingleton.elim w z]; exact hz
    rw [hW2]
    simpa using isCompact_univ

private theorem quasiCompact_of_isAffine_of_locallyOfFiniteType {k : Type u} [Field k] {W' : Scheme.{u}}
    [IsAffine W'] (q : W' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]
    {Z : Scheme.{u}} (g : W' ⟶ Z) : QuasiCompact g := by
  have hft : RingHom.FiniteType (q.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)
      (Q := @RingHom.FiniteType) (f := q)).mp inferInstance
  let : Algebra ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤) := (q.appTop).hom.toAlgebra
  have : Algebra.FiniteType ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤) := hft
  have hk : IsNoetherianRing ↥(CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) := by
    have e : ↥(CommRingCat.of k) ≃+* ↥Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact isNoetherianRing_of_surjective ↥(CommRingCat.of k) ↥Γ(Spec (CommRingCat.of k), ⊤)
      e.toRingHom e.surjective
  have : IsNoetherianRing ↥Γ(W', ⊤) :=
    Algebra.FiniteType.isNoetherianRing ↥Γ(Spec (CommRingCat.of k), ⊤) ↥Γ(W', ⊤)
  have : TopologicalSpace.NoetherianSpace ↥(Spec Γ(W', ⊤)) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum ↥Γ(W', ⊤)))
  have e : ↥W' ≃ₜ ↥(Spec Γ(W', ⊤)) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso W'.isoSpec)
  refine ⟨fun Vo hVo hVc => ?_⟩
  have he : IsCompact (e '' (⇑g ⁻¹' Vo)) := TopologicalSpace.NoetherianSpace.isCompact _
  rwa [Homeomorph.isCompact_image] at he

theorem isReduced_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) [IsReduced W'] (g' : W' ⟶ Y) :
    IsReduced (pullback g' (sigmaOpensDesc Y U)) := by
  refine isReduced_of_isOpenImmersion_cover
    (fun i => pullback.fst (pullback.snd g' (sigmaOpensDesc Y U))
      (Sigma.ι (fun j => (U j).toScheme) i)) (fun i => inferInstance) ?_ ?_
  · intro i
    have hoi : IsOpenImmersion
        (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U) := by
      rw [sigma_ι_sigmaOpensDesc]
      infer_instance
    have : IsReduced
        (pullback g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U)) :=
      isReduced_of_isOpenImmersion
        (pullback.fst g' (Sigma.ι (fun j => (U j).toScheme) i ≫ sigmaOpensDesc Y U))
    exact isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso g' (sigmaOpensDesc Y U)
        (Sigma.ι (fun j => (U j).toScheme) i)).hom
  · intro x
    obtain ⟨i, y, hy⟩ :=
      exists_sigma_ι_base_eq (fun j => (U j).toScheme)
        ((pullback.snd g' (sigmaOpensDesc Y U)).base x)
    obtain ⟨z, hz1, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback
        (f := pullback.snd g' (sigmaOpensDesc Y U))
        (g := Sigma.ι (fun j => (U j).toScheme) i) x y hy.symm
    exact ⟨i, z, hz1⟩

theorem compactSpace_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [QuasiCompact g'] :
    CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) := by
  have : IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hU
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : QuasiCompact (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  constructor
  have hcp := QuasiCompact.isCompact_preimage (f := pullback.snd g' (sigmaOpensDesc Y U))
    Set.univ isOpen_univ isCompact_univ
  simpa using hcp

theorem exists_affine_etale_cover_pullback_sigmaOpensDesc {k : Type u} [Field k]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type u} [Finite ι] (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) [IsAffine W'] [IsReduced W'] (q : W' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] (g' : W' ⟶ Y) [Etale g'] (_hg : g' ≫ p = q) :
    ∃ (V : Scheme.{u}) (s : V ⟶ Spec (CommRingCat.of k))
      (r : V ⟶ pullback g' (sigmaOpensDesc Y U)),
      IsAffine V ∧ IsReduced V ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
        Etale r ∧ Surjective r ∧
        r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ q = s := by
  have : QuasiCompact g' := quasiCompact_of_isAffine_of_locallyOfFiniteType q g'
  have : IsReduced (pullback g' (sigmaOpensDesc Y U)) :=
    isReduced_pullback_sigmaOpensDesc Y U W' g'
  have : CompactSpace ↥(pullback g' (sigmaOpensDesc Y U)) :=
    compactSpace_pullback_sigmaOpensDesc Y U hU W' g'
  have : LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  have : LocallyOfFiniteType (pullback.fst g' (sigmaOpensDesc Y U) ≫ q) := inferInstance
  have : QuasiCompact (pullback.fst g' (sigmaOpensDesc Y U) ≫ q) :=
    quasiCompact_of_compactSpace_to_spec_field _
  obtain ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_affine_etale_cover_of_isReduced (pullback g' (sigmaOpensDesc Y U))
      (pullback.fst g' (sigmaOpensDesc Y U) ≫ q)
  exact ⟨V, s, r, h1, h2, h3, h4, h5, h6, h7⟩

theorem etale_comp_fst_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem etale_comp_snd_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Etale g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Etale r] :
    Etale (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Etale (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem surjective_comp_fst_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.fst g' (sigmaOpensDesc Y U)) := by
  have := surjective_sigmaOpensDesc Y U hU
  have : Surjective (pullback.fst g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem surjective_comp_snd_pullback_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens)
    (W' : Scheme.{u}) (g' : W' ⟶ Y) [Surjective g'] (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) [Surjective r] :
    Surjective (r ≫ pullback.snd g' (sigmaOpensDesc Y U)) := by
  have : Surjective (pullback.snd g' (sigmaOpensDesc Y U)) := inferInstance
  infer_instance

theorem comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u}
    (U : ι → Y.Opens) (W' : Scheme.{u}) (g' : W' ⟶ Y) (V : Scheme.{u})
    (r : V ⟶ pullback g' (sigmaOpensDesc Y U)) :
    r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ g' =
      r ≫ pullback.snd g' (sigmaOpensDesc Y U) ≫ sigmaOpensDesc Y U := by
  rw [pullback.condition]

end FunctorialResolution.EmbeddedResolution
end

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_isStrictPullback_of_pullback_cover {Y W V : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (r : V ⟶ pullback g g) [AlgebraicGeometry.Flat r]
    [AlgebraicGeometry.Surjective r] (t : SequenceOfBlowups W) (u : SequenceOfBlowups V)
    (h1 : IsStrictPullbackBlowupSeq (r ≫ pullback.fst g g) u t)
    (h2 : IsStrictPullbackBlowupSeq (r ≫ pullback.snd g g) u t) :
    ∃ B : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t B := by
  have hA : IsStrictPullbackBlowupSeq (pullback.fst g g) (t.baseChange (pullback.fst g g)) t :=
    isStrictPullbackSequenceOfBlowups_baseChange t (pullback.fst g g)
  have hC : IsStrictPullbackBlowupSeq (pullback.snd g g) (t.baseChange (pullback.snd g g)) t :=
    isStrictPullbackSequenceOfBlowups_baseChange t (pullback.snd g g)
  have hAr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.fst g g)).baseChange r)
      (t.baseChange (pullback.fst g g)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.fst g g)) r
  have hCr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.snd g g)).baseChange r)
      (t.baseChange (pullback.snd g g)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.snd g g)) r
  have e1 : u.Isomorphic ((t.baseChange (pullback.fst g g)).baseChange r) :=
    h1.isomorphic (hAr.comp hA)
  have e2 : u.Isomorphic ((t.baseChange (pullback.snd g g)).baseChange r) :=
    h2.isomorphic (hCr.comp hC)
  exact exists_isStrictPullback_of_isomorphic_baseChange g t
    (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hAr hCr (e1.symm.trans e2))

private theorem isStrictPullback_of_comp_flat_surjective {X X' V : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] (α : V ⟶ X') [AlgebraicGeometry.Flat α]
    [AlgebraicGeometry.Surjective α] (s : SequenceOfBlowups X') (B : SequenceOfBlowups X) (u : SequenceOfBlowups V)
    (h1 : IsStrictPullbackBlowupSeq α u s) (h2 : IsStrictPullbackBlowupSeq (α ≫ φ) u B) :
    IsStrictPullbackBlowupSeq φ s B := by
  have hbc : IsStrictPullbackBlowupSeq φ (B.baseChange φ) B := isStrictPullbackSequenceOfBlowups_baseChange B φ
  have hbcα : IsStrictPullbackBlowupSeq α ((B.baseChange φ).baseChange α) (B.baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B.baseChange φ) α
  have e : u.Isomorphic ((B.baseChange φ).baseChange α) := h2.isomorphic (hbcα.comp hbc)
  exact hbc.of_isomorphic_pullback (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic h1 hbcα e).symm

theorem existsGluedBlowupSequence_of_center_ne_top (R : AffineResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.IsAffine Y] (i : ℕ),
      i < (R k Y p).length → (R k Y p).center i ≠ ⊤) :
    ExistsGluedBlowupSequence R := by
  intro hcover k hk hk0 Y p hpft hpqc hpred
  have : AlgebraicGeometry.IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have : CompactSpace ↥Y := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover Y
  have : AlgebraicGeometry.IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : AlgebraicGeometry.Surjective (sigmaOpensDesc Y U) :=
    surjective_sigmaOpensDesc Y U hUtop
  obtain ⟨V, sV, r, hVaff, hVred, hsft, hsqc, hret, hrsurj, hrq⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff (sigmaOpens Y U)
      (sigmaOpensDesc Y U ≫ p) (sigmaOpensDesc Y U) rfl
  have : AlgebraicGeometry.Etale
      (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Etale
      (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Surjective
      (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Surjective
      (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
  have hq1 : (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫
      (sigmaOpensDesc Y U ≫ p) = sV := by
    rw [Category.assoc]
    exact hrq
  have hq2 : (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫
      (sigmaOpensDesc Y U ≫ p) = sV := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
    have h3 := congrArg (fun m => m ≫ p) h
    simp only [Category.assoc] at h3
    rw [Category.assoc, ← h3]
    exact hrq
  have ht1 := hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV
    (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq1
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have ht2 := hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV
    (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq2
    (fun y => AlgebraicGeometry.Surjective.surj y)
  obtain ⟨B, hB⟩ := exists_isStrictPullback_of_pullback_cover (sigmaOpensDesc Y U) r
    (R k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p)) (R k V sV) ht1 ht2
  refine ⟨B, hB.center_ne_top_of_forall_center_ne_top
    (fun i hi => hR k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p) i hi), ?_⟩
  intro W' q' hq'ft hq'qc hW'red hW'aff φ hφet hφq hφsurj
  have : AlgebraicGeometry.Surjective φ := ⟨hφsurj⟩
  obtain ⟨V', sV', r', hV'aff, hV'red, hs'ft, hs'qc, hr'et, hr'surj, hr'q⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff W' q' φ hφq
  have : AlgebraicGeometry.Etale (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U W' φ V' r'
  have : AlgebraicGeometry.Etale (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'
  have : AlgebraicGeometry.Surjective (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop W' φ V' r'
  have : AlgebraicGeometry.Surjective (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'
  have hα : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ q' = sV' := by
    rw [Category.assoc]
    exact hr'q
  have hβ : (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ (sigmaOpensDesc Y U ≫ p) = sV' := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'
    have h3 := congrArg (fun m => m ≫ p) h
    simp only [Category.assoc] at h3
    rw [Category.assoc, ← h3, hφq]
    exact hr'q
  have hu1 := hcover k W' V' q' sV' (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) hα
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have hu2 := hcover k (sigmaOpens Y U) V' (sigmaOpensDesc Y U ≫ p) sV'
    (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) hβ
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have hαφ : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ
      = (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ sigmaOpensDesc Y U := by
    simp only [Category.assoc]
    exact comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'
  have hfin : IsStrictPullbackBlowupSeq ((r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ)
      (R k V' sV') B := by
    rw [hαφ]
    exact hu2.comp hB
  exact isStrictPullback_of_comp_flat_surjective φ (r' ≫ pullback.fst φ (sigmaOpensDesc Y U))
    (R k W' q') B (R k V' sV') hu1 hfin

end FunctorialResolution.EmbeddedResolution

end
