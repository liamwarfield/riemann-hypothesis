module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.StalkDom
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CharPolEqRootPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsStepHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SpecTopHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TraceSplitHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Closed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SmoothModelCrystalline
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.FibrePowerTowerAdmissibleLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KsGoodHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixedPointsIntBaseHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PWitScal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PCxFinOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.KsHodgeOfGeo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LefschetzFixedPointFiniteEtaleCorrespondence

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExt
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

private theorem exists_isClopen_preimage {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (f : P → X) (hf : Topology.IsEmbedding f) (hd : Dense (Set.range f))
    (hl : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsPreirreducible W)
    (U : Set P) (hU : IsClopen U) : ∃ V : Set X, IsClopen V ∧ f ⁻¹' V = U := by
  have key : ∀ W : Set X, IsOpen W → IsPreirreducible W → (f ⁻¹' W ⊆ U ∨ f ⁻¹' W ⊆ Uᶜ) := by
    intro W hW hWi
    obtain ⟨A, hA, hAU⟩ := hf.isInducing.isOpen_iff.mp hU.isOpen
    obtain ⟨B, hB, hBU⟩ := hf.isInducing.isOpen_iff.mp hU.compl.isOpen
    by_contra hc
    rw [not_or, Set.not_subset, Set.not_subset] at hc
    obtain ⟨⟨a, ha, haU⟩, ⟨b, hb, hbU⟩⟩ := hc
    have h1 : (W ∩ A).Nonempty := by
      refine ⟨f b, hb, ?_⟩
      rw [← Set.mem_preimage, hAU]
      simpa using hbU
    have h2 : (W ∩ B).Nonempty := by
      refine ⟨f a, ha, ?_⟩
      rw [← Set.mem_preimage, hBU]
      exact haU
    obtain ⟨x, hxW, hxA, hxB⟩ := hWi A B hA hB h1 h2
    obtain ⟨_, ⟨q, rfl⟩, -, hqA, hqB⟩ := hd.exists_mem_open (hW.inter (hA.inter hB)) ⟨x, hxW, hxA, hxB⟩
    have hq1 : q ∈ U := by rw [← hAU]; exact hqA
    have hq2 : q ∈ Uᶜ := by rw [← hBU]; exact hqB
    exact hq2 hq1
  refine ⟨{x | ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsPreirreducible W ∧ f ⁻¹' W ⊆ U}, ⟨?_, ?_⟩, ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hW, hxW, hWi⟩ := hl x
    have hWc : f ⁻¹' W ⊆ Uᶜ := by
      rcases key W hW hWi with h | h
      · exact absurd ⟨W, hW, hxW, hWi, h⟩ hx
      · exact h
    refine ⟨W, ?_, hW, hxW⟩
    rintro z hz ⟨W', hW', hzW', hW'i, hW'U⟩
    obtain ⟨_, ⟨q, rfl⟩, hqW, hqW'⟩ := hd.exists_mem_open (hW.inter hW') ⟨z, hz, hzW'⟩
    exact hWc hqW (hW'U hqW')
  · rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, hW, hxW, hWi, hWU⟩
    exact ⟨W, fun z hz => ⟨W, hW, hz, hWi, hWU⟩, hW, hxW⟩
  · ext q
    constructor
    · rintro ⟨W, -, hqW, -, hWU⟩
      exact hWU hqW
    · intro hq
      obtain ⟨W, hW, hxW, hWi⟩ := hl (f q)
      rcases key W hW hWi with h | h
      · exact ⟨W, hW, hxW, hWi, h⟩
      · exact absurd hq (h hxW)

private theorem exists_isPreirreducible_nhd (Y : Scheme.{0}) [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) (y : Y) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ IsPreirreducible W := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI hN : TopologicalSpace.NoetherianSpace (U : Scheme) := noetherianSpace_of_isAffineOpen U hU
  have hdom : ∀ z : (U : Scheme), IsDomain ((U : Scheme).presheaf.stalk z) := by
    intro z
    have e := (Scheme.Opens.stalkIso U z).commRingCatIsoToRingEquiv
    haveI := hY z.1
    exact Function.Injective.isDomain e.toRingHom e.injective
  let z : (U : Scheme) := ⟨y, hyU⟩
  have hC : IsOpen (irreducibleComponent z) := by
    have h := FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents
      (X := (U : Scheme)) (𝒜 := {irreducibleComponent z}) ?_ ?_
    · rwa [Set.sUnion_singleton] at h
    · rintro C₁ h1 C₂ h2 ⟨x, hx1, hx2⟩
      exact FunctorialResolution.EmbeddedResolution.irreducibleComponents_eq_of_stalk_isDomain
        (U : Scheme) hdom h1 h2 hx1 hx2
    · intro D hD
      rw [Set.mem_singleton_iff.mp hD]
      exact irreducibleComponent_mem_irreducibleComponents _
  refine ⟨U.ι '' irreducibleComponent z, U.ι.isOpenEmbedding.isOpenMap _ hC,
    ⟨z, mem_irreducibleComponent, rfl⟩, ?_⟩
  exact isIrreducible_irreducibleComponent.isPreirreducible.image _ U.ι.continuous.continuousOn

theorem UpperTheory.Gal.Int.Geo.Cut.clopenExt :
    UpperTheory.Gal.Int.Geo.Cut.ClopenExt := by
  intro O k _ _ _ _ _ _ Y p hp U hU
  have hf : Flat p := inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨hr, he⟩ := genRange O k Y p
  obtain ⟨V, hV, hVU⟩ := exists_isClopen_preimage (pullback.fst p (gen O k)) he
    (by rw [hr]; exact genDense O Y p hf)
    (exists_isPreirreducible_nhd Y (stalkDom O Y p hp)) U hU
  exact ⟨⟨V, hV.isOpen⟩, hV.isClosed, hVU⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.FEtCut
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.fEtCut :
    UpperTheory.Gal.Int.Geo.Cut.FEtCut := by
  intro Y' Y T' T j s t i s' t' d hj hr hst hs
  haveI := hj.op
  haveI := hr.op
  have hpre : s ⁻¹ᵁ j.opensRange = i.opensRange := by
    apply SetLike.coe_injective
    change s ⁻¹' Set.range j = Set.range i
    rw [hr.rng]
    ext x
    exact ⟨fun h => ⟨h, hst x h⟩, fun h => h.1⟩
  have pb : IsPullback s' i j s := IsOpenImmersion.isPullback s' i j s hr.es.symm hpre
  obtain ⟨hfin, het, hcard⟩ := hs
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) pb.flip hfin,
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) pb.flip het, ?_⟩
  intro K _ _ x
  rw [← hcard K (x ≫ j)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ i, by rw [Category.assoc, ← pb.w, ← Category.assoc, y.2]⟩
      invFun := fun z => ⟨pb.lift x z.1 z.2.symm, pb.lift_fst _ _ _⟩
      left_inv := fun y => Subtype.ext (pb.hom_ext (by simp [y.2]) (by simp))
      right_inv := fun z => Subtype.ext (pb.lift_snd _ _ _) }
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.CorrCut
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

namespace UpperTheory.Gal.Int.Geo.Cut

theorem corrCut : CorrCut := by
  intro l Y' Y T' j T i s' t' hj hr hcond
  haveI := hj.op
  haveI := hr.op
  have hcl : IsClosed (Set.range i) := by
    rw [hr.rng]
    exact (hj.cl.preimage T.p.continuous).inter (hj.cl.preimage T.r.continuous)
  haveI : IsClosedImmersion i := .of_isPreimmersion _ hcl
  haveI := T.fin
  haveI : IsFinite (s' ≫ j) := by rw [hr.es]; infer_instance
  refine ⟨IsFinite.of_comp s' j, ?_, ?_⟩
  · have hV : j ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) = Y'.basicOpen (l : Γ(Y', ⊤)) := by
      rw [Scheme.Hom.preimage_basicOpen, map_natCast]
      rfl
    let a := (s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ i
    have ha : Set.range a ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hu : s' ((s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι u) ∈ j ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
        rw [hV]
        exact u.2
      change T.p (i ((s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι u)) ∈ Y.basicOpen (l : Γ(Y, ⊤))
      rw [← Scheme.Hom.comp_apply, ← hr.es, Scheme.Hom.comp_apply]
      exact hu
    haveI : Etale (IsOpenImmersion.lift _ a ha ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    haveI : Etale (IsOpenImmersion.lift _ a ha) := Etale.of_comp _ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι
    haveI := T.et
    have e1 : (s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ≫ (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j =
        IsOpenImmersion.lift _ a ha ≫ (T.p ∣_ Y.basicOpen (l : Γ(Y, ⊤))) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [morphismRestrict_ι, ← Category.assoc (IsOpenImmersion.lift _ a ha), IsOpenImmersion.lift_fac,
        ← Category.assoc, morphismRestrict_ι, Category.assoc, hr.es]
      simp only [a, Category.assoc]
    haveI : Etale ((s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ≫ (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j) := by
      rw [e1]
      infer_instance
    exact Etale.of_comp _ ((Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j)
  · intro K _ _ hl y
    rw [← T.deg K hl (y ≫ j)]
    have hbo : ∀ (f : Spec (CommRingCat.of K) ⟶ Y) (u : Spec (CommRingCat.of K)),
        f u ∈ Y.basicOpen (l : Γ(Y, ⊤)) := by
      intro f u
      have htop : f ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) = ⊤ := by
        rw [Scheme.Hom.preimage_basicOpen, map_natCast]
        apply Scheme.basicOpen_of_isUnit
        have hu := (IsUnit.mk0 (l : K) hl).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        rw [map_natCast] at hu
        exact hu
      have hu' : u ∈ f ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
        rw [htop]
        trivial
      exact hu'
    have hw : ∀ w : { z // z ≫ T.p = y ≫ j }, Set.range w.1 ⊆ Set.range i := by
      rintro w _ ⟨u, rfl⟩
      rw [hr.rng]
      have h1 : T.p (w.1 u) = j (y u) := by
        rw [← Scheme.Hom.comp_apply, w.2, Scheme.Hom.comp_apply]
      exact ⟨⟨y u, h1.symm⟩, hcond _ ⟨y u, h1.symm⟩ (hbo (w.1 ≫ T.p) u)⟩
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ i, by rw [Category.assoc, ← hr.es, ← Category.assoc, z.2]⟩
        invFun := fun w => ⟨IsOpenImmersion.lift i w.1 (hw w), by
          rw [← cancel_mono j, Category.assoc, hr.es, ← Category.assoc, IsOpenImmersion.lift_fac, w.2]⟩
        left_inv := fun z => Subtype.ext ((cancel_mono i).mp (IsOpenImmersion.lift_fac _ _ _))
        right_inv := fun w => Subtype.ext (IsOpenImmersion.lift_fac _ _ _) }

end UpperTheory.Gal.Int.Geo.Cut
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.PtIdCut
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

namespace UpperTheory.Gal.Int.Geo.Cut

private theorem multiset_map_pts {J P Q : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ)
    (v : (j : J) → I j → P) (g : P → Q) :
    Multiset.map g (crystallineComparison.pts a v) = crystallineComparison.pts a (fun j i => g (v j i)) := by
  simp only [crystallineComparison.pts]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show Multiset.map g = Multiset.mapAddMonoidHom g from rfl, map_sum]
  simp [Multiset.map_nsmul, Multiset.map_map]

private theorem identity_of_comp_injective_semiconj_image (q n : ℕ) {P Q : Type} (F' : P → P) (F : Q → Q) (g : P → Q)
    (hg : Function.Injective g) (hc : Function.Semiconj g F' F) {I : Fin (n + 1) → Type}
    [∀ j, Fintype (I j)] (v : (j : Fin (n + 1)) → I j → P)
    (h : crystallineComparison.AltId q n F (fun j i => g (v j i))) : crystallineComparison.AltId q n F' v := by
  unfold crystallineComparison.AltId at *
  apply Multiset.map_injective hg
  have e : ∀ (k : ℕ) (x : P), F^[k] (g x) = g (F'^[k] x) := fun k x => ((hc.iterate_right k) x).symm
  simp only [e] at h
  rw [multiset_map_pts, multiset_map_pts]
  exact h

private theorem genPt_openImmersion_of_genPt_appTop {Y' Y : Scheme} (j : Y' ⟶ Y) [IsOpenImmersion j] (π : Γ(Y, ⊤)) (x : Y')
    (h : crystallineComparison.GenPt ((ConcreteCategory.hom (Scheme.Hom.appTop j)) π) x) : crystallineComparison.GenPt π (j x) := by
  have key : ∀ y : Y', j y ∈ Y.basicOpen π ↔
      y ∈ Y'.basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop j)) π) := by
    intro y
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  refine ⟨fun hx => h.1 ((key x).1 hx), fun x' hx' hsp => ?_⟩
  obtain ⟨x'', rfl⟩ : x' ∈ Set.range j := hsp.mem_open j.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
  have h2 : x'' ⤳ x := (j.isOpenEmbedding.toIsInducing.specializes_iff).1 hsp
  rw [h.2 x'' (fun hb => hx' ((key x'').2 hb)) h2]

private theorem range_subset_range_of_comp_eq_of_ne_zero {l : ℕ} {Y' Y : Scheme} (j : Y' ⟶ Y) (hP : Part j) (T : crystallineComparison.Corr l Y)
    (T' : crystallineComparison.Corr l Y') (i : T'.Z ⟶ T.Z) (hR : Res j T.p T.r i T'.p T'.r)
    (hr : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j)
    (V : Type) [CommRing V] [IsDomain V] (hl : (l : V) ≠ 0) (y' : Spec (CommRingCat.of V) ⟶ Y')
    (z : Spec (CommRingCat.of V) ⟶ T.Z) (hz : z ≫ T.p = y' ≫ j) :
    Set.range z ⊆ Set.range i := by
  have hp : ∀ s, T.p (z s) = j (y' s) := fun s => by
    rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]
  let η : Spec (CommRingCat.of V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)
  have hη : T.p (z η) ∈ Y.basicOpen (l : Γ(Y, ⊤)) := by
    rw [← Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← Set.mem_preimage, ← Scheme.Hom.coe_preimage,
      Scheme.preimage_basicOpen_top, map_natCast, basicOpen_eq_of_affine', map_natCast]
    exact hl
  have hrη : T.r (z η) ∈ Set.range j := hr _ (by rw [hp]; exact ⟨_, rfl⟩) hη
  rintro _ ⟨s, rfl⟩
  have hsp : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 bot_le
  have hrs : T.r (z s) ∈ Set.range j :=
    ((hsp.map z.continuous).map T.r.continuous).mem_closed hP.cl hrη
  rw [hR.rng]
  exact ⟨by rw [Set.mem_preimage, hp]; exact ⟨_, rfl⟩, hrs⟩

private theorem bijective_sec_comp_of_ne_zero {l : ℕ} {Y' Y : Scheme} (j : Y' ⟶ Y) (hP : Part j) (T : crystallineComparison.Corr l Y)
    (T' : crystallineComparison.Corr l Y') (i : T'.Z ⟶ T.Z) (hR : Res j T.p T.r i T'.p T'.r)
    (hr : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j)
    (V : Type) [CommRing V] [IsDomain V] (hl : (l : V) ≠ 0) (y' : Spec (CommRingCat.of V) ⟶ Y') :
    Function.Bijective (fun u : T'.Sec y' => (⟨u.1 ≫ i, by
      rw [Category.assoc, ← hR.es, ← Category.assoc, u.2]⟩ : T.Sec (y' ≫ j))) := by
  haveI := hP.op
  haveI := hR.op
  constructor
  · intro u v h
    apply Subtype.ext
    exact (cancel_mono i).1 (congrArg Subtype.val h)
  · intro z
    have hsub := range_subset_range_of_comp_eq_of_ne_zero j hP T T' i hR hr V hl y' z.1 z.2
    refine ⟨⟨IsOpenImmersion.lift i z.1 hsub, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    apply (cancel_mono j).1
    rw [Category.assoc, hR.es, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact z.2

theorem ptIdCut : PtIdCut := by
  unfold PtIdCut
  intro l q n Y' Y j π T T' i hP hR hr hT
  unfold crystallineComparison.PtId at hT ⊢
  intro V _ _ _ _ hl y' hg φ hφ I _ z' hz'
  haveI := hP.op
  let w : (a : Fin (n + 1)) → I a → (T a).Sec (y' ≫ j) := fun a b =>
    ⟨(z' a b).1 ≫ i a, by rw [Category.assoc, ← (hR a).es, ← Category.assoc, (z' a b).2]⟩
  have hw : ∀ a, Function.Bijective (w a) := fun a =>
    (bijective_sec_comp_of_ne_zero j hP (T a) (T' a) (i a) (hR a) (hr a) V hl y').comp (hz' a)
  have hg' : crystallineComparison.GenPt π ((y' ≫ j) (IsLocalRing.closedPoint V)) := by
    have h0 := genPt_openImmersion_of_genPt_appTop j π _ hg
    convert h0 using 1
    exact Scheme.Hom.comp_apply y' j _
  have h := hT V hl (y' ≫ j) hg' φ hφ I w hw
  refine identity_of_comp_injective_semiconj_image q n (crystallineComparison.twist φ Y') (crystallineComparison.twist φ Y) (fun x => x ≫ j)
    (fun x y hxy => (cancel_mono j).1 hxy) (fun x => by simp [crystallineComparison.twist, Category.assoc]) _ ?_
  have e : (fun a b => (crystallineComparison.resPt V ≫ (z' a b).1 ≫ (T' a).r) ≫ j) =
      fun a b => crystallineComparison.resPt V ≫ (w a b).1 ≫ (T a).r := by
    funext a b
    simp only [w, Category.assoc, (hR a).et]
  rw [e]
  exact h

end UpperTheory.Gal.Int.Geo.Cut
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ResEx
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.resEx :
    UpperTheory.Gal.Int.Geo.Cut.ResEx := by
  intro Y' Y T j s t hj
  haveI := hj.op
  let U : T.Opens := s ⁻¹ᵁ j.opensRange ⊓ t ⁻¹ᵁ j.opensRange
  have hs : Set.range (U.ι ≫ s) ⊆ Set.range j := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have ht : Set.range (U.ι ≫ t) ⊆ Set.range j := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine ⟨U, U.ι, IsOpenImmersion.lift j _ hs, IsOpenImmersion.lift j _ ht,
    ⟨inferInstance, ?_, IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩⟩
  rw [Scheme.Opens.range_ι]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBridge
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 NumberField IsDedekindDomain Module GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.PhtCompare

section
variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}

theorem exists_bridge (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧ Bw.Kw.1 ≤ Bw.LL.1 ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl, IntermediateField.le_normalClosure _, rfl⟩

end

end GlobalTheory.PhtCompare

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo

structure Steps : Prop where
  rep : RepEx
  es : ESStep
  crys : CrysStep
  jump : JumpStep
  phi : PhiStep
  cut : CutStep
  twES : TwES
  twCrys : TwCrys
  twJ : TwJ
  twPhi : TwPhi
  phiOf : PhiOf
  card : SatCard
  jumpsOf : JumpsOf
  rich : RichOf
  char : TP.Sub.CharEx
  ss : TP.Sub.SSLeft
  cont : TP.Sub.ContLeft

theorem map_inv_mul (R : Multiset ℂ) (c : ℂˣ) : (R.map (· * ((c : ℂ))⁻¹)).map (· * (c : ℂ)) = R := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id R]
  exact Multiset.map_congr rfl fun x _ => by simp

theorem Pack.rep (h : Steps) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a d : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (P : Pack ι d U)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (hlac : LacWtAt ι v U) (hP : P.HTFor v) :
    ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w → CrysAt ρ w ∧ JumpsOcc U ι ρ w) ∧
      ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → PhiKilled ι ρ w a B := by
  obtain ⟨dd, ρ, hc, hs, hp⟩ := h.rep E Ω l P.H P.θ P.nice
  obtain ⟨L, hL, -⟩ := h.char E Ω l ι
  obtain ⟨hχ, hcl⟩ := hL P.κ P.m P.alg
  have hES : ∀ w B, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → CongFor ι a P.H P.θ P.κ w B →
      ESAt ι (tw ρ (L P.κ P.m)) w (algSat a (normV w) B) := by
    rintro w B hw ⟨hu, ϑ, h1, h2⟩
    have := h.twES E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) hw _
      (h.es E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rwa [map_inv_mul] at this
  have hHT : ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w →
      CrysAt (tw ρ (L P.κ P.m)) w ∧ JumpsOcc U ι (tw ρ (L P.κ P.m)) w := by
    rintro w hw ⟨hu, h1, h2⟩
    have hg := (h.cut E _ P.H P.θ P.nice w).1 h1
    have h3 : ∀ τ : E →+* ℂ, ∃ σ : ℂ ≃+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam,
        HodgeAt (ι.trans σ) P.H P.θ (σ.toRingHom.comp τ) (j + P.m τ) := fun τ => by
      by_cases hτ : OverPl ι τ w
      · obtain ⟨σ, hσ⟩ := h2 τ hτ
        exact ⟨σ, fun _ => hσ⟩
      · exact ⟨RingEquiv.refl ℂ, fun h' => absurd h' hτ⟩
    choose σ hσ using h3
    have hJ : JOcc ι ρ w fun τ j => HodgeAt (ι.trans (σ τ)) P.H P.θ ((σ τ).toRingHom.comp τ) j := by
      intro Q AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
      exact h.jump E Ω l (ι.trans (σ (ι.toRingHom.comp τ))) P.H P.θ P.nice dd ρ hc hp w hw hg Q AI hT A hA O Bw hj τ LL' τ' hi
    refine ⟨?_, h.jumpsOf E Ω l ι a dd U _ w _ ?_ (h.twJ E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _ hJ)⟩
    · obtain ⟨C, hC, -⟩ := hg
      exact h.twCrys E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) (h.crys E Ω l P.H P.θ P.nice dd ρ hc hp w hw C hC)
    · intro τ hτ lam hl j hj
      simpa only [sub_neg_eq_add] using hσ τ hτ lam hl j hj
  refine ⟨dd, tw ρ (L P.κ P.m), ⟨(h.cont _ _ dd 0).2.2.1 ρ _ hc hχ, (h.ss _ _ dd 0).2.2 ρ _ hs, ?_,
    h.rich E Ω l ι a dd U _ v hv hlac (hHT v hv hP).2⟩, fun w hw hC B hB => hES w B hw (hC B hB), hHT, ?_⟩
  · obtain ⟨X, hX⟩ := P.cong
    exact ⟨X, fun w h1 h2 h3 B hB => hES w B h3 (hX w h1 h2 h3 B hB)⟩
  · intro w hw hC B hB
    obtain ⟨hu, ϑ, h1, h2⟩ := hC B hB
    have := h.twPhi E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _
      (h.phi E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rw [map_inv_mul] at this
    exact h.phiOf E Ω l ι dd _ w a B (h.card E a U w B hB) this

theorem geoOne_of (h : Steps) (hP : PackEx) : GeoOne := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph hlac
  obtain ⟨⟨P, hP0⟩, hA, hB⟩ := hP E l ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph
  refine ⟨?_, fun w hw hl hs => ?_, fun w hl hk ha0 hav hs => ?_⟩
  · obtain ⟨dd, ρ, hV, -⟩ := P.rep h Ω hv hlac hP0
    exact ⟨dd, ρ, hV⟩
  · obtain ⟨P, h1, h2⟩ := hA w hw hl hs
    obtain ⟨dd, ρ, hV, hE, -⟩ := P.rep h Ω hv hlac h1
    exact ⟨dd, ρ, hV, hE w hl h2⟩
  · obtain ⟨⟨P, h1, h2⟩, P', h1', h2'⟩ := hB w hl hk ha0 hav hs
    obtain ⟨dd, ρ, hV, -, hC, -⟩ := P.rep h Ω hv hlac h1
    obtain ⟨dd', ρ', hV', -, -, hF⟩ := P'.rep h Ω hv hlac h1'
    exact ⟨⟨dd, ρ, hV, hC w hl h2⟩, dd', ρ', hV', hF w hl h2'⟩

end UpperTheory.Gal.Int.Geo

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.GeometricRealizationOfWeightOne
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep
noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Gal.Int.Geo

open Cut

private theorem cut {k L O : Type} [Field k] [Field L] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O k]
    [IsFractionRing O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    ∃ (C' : Cover H θ O) (j : C'.Y ⟶ C.Y), Part j ∧ C'.p = j ≫ C.p ∧ C'.π ≫ j = C.π ∧ C'.Onto ∧
      ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π := by
  haveI := C.finπ
  haveI := C.etπ
  have hU : IsClopen (Set.range (pullback.lift C.π H.q C.ov)) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  obtain ⟨V, hVc, hVpre⟩ := clopenExt O k C.Y C.p C.smooth _ hU
  obtain ⟨C', j, hj, hrj, hp, hπ, hon⟩ := coverCut k L O H θ C V hVc hVpre
  refine ⟨C', j, hj, hp, hπ, hon, ?_⟩
  intro y hy hgen
  have hyV : y ∈ (V : Set C.Y) := hrj ▸ hy
  have hy' : y ∈ Set.range (pullback.fst C.p (gen O k)) := by
    rw [(genRange O k C.Y C.p).1]
    exact hgen
  obtain ⟨z, rfl⟩ := hy'
  have hz : z ∈ Set.range (pullback.lift C.π H.q C.ov) := by
    rw [← hVpre]
    exact hyV
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩

private theorem over_eq {Y' Y T' T S : Scheme.{0}} {j : Y' ⟶ Y} {s t : T ⟶ Y} {i : T' ⟶ T} {s' t' : T' ⟶ Y'}
    (h : Res j s t i s' t') {p : Y ⟶ S} (e : t ≫ p = s ≫ p) : t' ≫ j ≫ p = s' ≫ j ≫ p := by
  rw [← Category.assoc, h.et, Category.assoc, e, ← Category.assoc, ← h.es, Category.assoc]

private theorem mem_range_of_lies_of_mem_range_of_asIdeal_bot {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C C' : Cover H θ O} {j : C'.Y ⟶ C.Y} (hj : Part j) (hπ : C'.π ≫ j = C.π)
    (hgen : ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π) {g : H.Γ} {T : Scheme}
    {s t : T ⟶ C.Y} {m : ℕ} (hl : C.Lies g s t m) (x : T) (hx : s x ∈ Set.range j)
    (hxg : (C.p (s x)).asIdeal = ⊥) : t x ∈ Set.range j := by
  obtain ⟨z, hz⟩ := (liesCut k L O H θ C C' j hj hπ g T s t m hl).1 x (hgen _ hx hxg)
  exact ⟨C'.π z, by rw [← Scheme.Hom.comp_apply, hπ, hz]⟩

private theorem mem_range_of_fEt_of_lies_of_mem_range {k L O : Type} [Field k] [Field L] [CommRing O] [IsDomain O] [Algebra O k]
    {H : HTower k} {θ : H.Γ → L} {C C' : Cover H θ O} {j : C'.Y ⟶ C.Y} (hj : Part j)
    (hπ : C'.π ≫ j = C.π) (hgen : ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π)
    {g : H.Γ} {T : Scheme} {s t : T ⟶ C.Y} {d m : ℕ} (hs : FEt s d) (hl : C.Lies g s t m) :
    ∀ x, s x ∈ Set.range j → t x ∈ Set.range j := by
  haveI : Etale s := hs.2.1
  haveI := C.smooth
  haveI := hj.op
  have hD := genDense O T (s ≫ C.p) inferInstance
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx, hxt⟩ := hne
  have hopen : IsOpen ({x | s x ∈ Set.range j} ∩ {x | t x ∈ Set.range j}ᶜ) :=
    IsOpen.inter (j.isOpenEmbedding.isOpen_range.preimage s.continuous)
      (hj.cl.preimage t.continuous).isOpen_compl
  obtain ⟨y, ⟨hy1, hy2⟩, hyg⟩ := hD.inter_open_nonempty _ hopen ⟨x, hx, hxt⟩
  rw [Set.mem_setOf_eq, Scheme.Hom.comp_apply] at hyg
  exact hy2 (mem_range_of_lies_of_mem_range_of_asIdeal_bot hj hπ hgen hl y hy1 hyg)

private theorem asIdeal_eq_bot_of_mem_basicOpen_natCast {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {Y : Scheme}
    (q : Y ⟶ Spec (CommRingCat.of (Ow w))) (p : ℕ) (hp : (p : 𝓞 E) ∈ w.asIdeal) (y : Y)
    (hy : y ∈ Y.basicOpen (p : Γ(Y, ⊤))) : (q y).asIdeal = ⊥ := by
  have hmax : (p : Ow w) ∈ IsLocalRing.maximalIdeal (Ow w) := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (p : 𝓞 E)).2 hp
    have h2 := (Valuation.isEquiv_iff_val_lt_one.1
      (Valuation.isEquiv_valuation_valuationSubring (w.valuation E))).1 h1
    convert h2 using 2
    push_cast
    rfl
  have h3 : (p : Γ(Y, ⊤)) =
      (q.appTop) ((Scheme.ΓSpecIso (CommRingCat.of (Ow w))).inv (p : Ow w)) := by
    simp
  rw [h3, ← Scheme.Hom.preimage_basicOpen_top] at hy
  have h5 : q y ∈ ((Spec (CommRingCat.of (Ow w))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Ow w))).inv (p : Ow w)) : Set _) := hy
  rw [basicOpen_eq_of_affine] at h5
  have h6 : (p : Ow w) ∉ (q y).asIdeal := h5
  by_contra hne
  have hM := IsLocalRing.eq_maximalIdeal ((q y).isPrime.isMaximal hne)
  exact h6 (hM ▸ hmax)

theorem cutStep_holds : CutStep := by
  intro E _ _ L _ H θ _ w
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨C', j, hj, hp, hπ, hon, hgen⟩ := cut C
    refine ⟨C', hon, fun g => ?_⟩
    obtain ⟨T, s, t, d, m, hs, ht, hl⟩ := hC g
    obtain ⟨T', i, s', t', hR⟩ := resEx _ _ _ j s t hj
    have hst := mem_range_of_fEt_of_lies_of_mem_range hj hπ hgen hs hl
    refine ⟨T', s', t', d, m, fEtCut _ _ _ _ j s t i s' t' d hj hR hst hs, ?_, ?_⟩
    · rw [hp]
      exact over_eq hR ht
    · exact (liesCut _ _ _ H θ C C' j hj hπ g T s t m hl).2 T' i s' t' hR
  · rintro n ϑ ⟨C, p, f, hpr, hpw, hnorm, ϖ, T, γ, m, hirr, hpt, hT⟩
    obtain ⟨C', j, hj, hp, hπ, hon, hgen⟩ := cut C
    have hres := fun a => resEx _ _ _ j (T a).p (T a).r hj
    choose Z i s' t' hR using hres
    have hcond : ∀ a (x : (T a).Z), (T a).p x ∈ Set.range j →
        (T a).p x ∈ C.Y.basicOpen (p : Γ(C.Y, ⊤)) → (T a).r x ∈ Set.range j :=
      fun a x hx hb => mem_range_of_lies_of_mem_range_of_asIdeal_bot hj hπ hgen (hT a).2.1 x hx (asIdeal_eq_bot_of_mem_basicOpen_natCast w C.p p hpw _ hb)
    have hc := fun a => corrCut p _ _ _ j (T a) (i a) (s' a) (t' a) hj (hR a) (hcond a)
    let T' : Fin (n + 1) → crystallineComparison.Corr p C'.Y := fun a =>
      ⟨Z a, s' a, t' a, (T a).d, (hc a).1, (hc a).2.1, (hc a).2.2⟩
    refine ⟨C', p, f, hpr, hpw, hnorm, hon, ϖ, T', γ, m, hirr, ?_, fun a => ⟨?_, ?_, (hT a).2.2⟩⟩
    · have := ptIdCut p (p ^ f) n _ _ j (crystallineComparison.fn C.p ϖ) T T' i hj hR hcond hpt
      convert this using 2
      rw [hp]
      simp only [crystallineComparison.fn, Scheme.Hom.comp_appTop]
      rfl
    · show t' a ≫ C'.p = s' a ≫ C'.p
      rw [hp]
      exact over_eq (hR a) (hT a).1
    · exact (liesCut _ _ _ H θ C C' j hj hπ (γ a) _ _ _ (m a) (hT a).2.1).2 _ (i a) _ _ (hR a)

end UpperTheory.Gal.Int.Geo
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.AevalSmulProd
open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem aeval_smul_prod {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (c : K) (S : Multiset K) :
    aeval (c • M) ((S.map fun b => X - C (b * c)).prod) =
      c ^ Multiset.card S • aeval M ((S.map fun b => X - C b).prod) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, map_mul (aeval (c • M)), map_mul (aeval M), ih]
    simp only [map_sub, aeval_X, aeval_C]
    have e : (algebraMap K (Matrix (Fin n) (Fin n) K)) (z * c) = c • (algebraMap K (Matrix (Fin n) (Fin n) K)) z := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    rw [e, ← smul_sub, smul_mul_smul_comm, pow_succ']

theorem UpperTheory.Gal.Int.Geo.twES :
    UpperTheory.Gal.Int.Geo.TwES := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hCl hw R hES A hA
  have hχ := hCl.1 hw A hA
  obtain ⟨hi, hf⟩ := hES A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 := (hχ.1 s hs)
    have h2 : (χ s : Qbar l) = 1 := by
      have h3 : ((GlobalTheory.TripleGal.rk1 χ s : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 = (χ s : Qbar l) := by
        simp [GlobalTheory.TripleGal.rk1]
      rw [h1] at h3
      simpa using h3.symm
    apply Units.ext
    rw [UpperTheory.V.Af.tw_val, hi s hs, h2]
    simp
  · have hk : ι ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = c := by
      have h1 := (hχ.2 σ hσ)
      have h2 := (UpperTheory.Gal.TP.Sub.cpFacts_holds (G E Ω) (Qbar l) 0 0).2.1 χ σ⁻¹
      simp only [UpperTheory.Gal.TP.Sub.cp] at h2
      rw [h2] at h1
      simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C] at h1
      exact C_injective (sub_right_injective h1)
    have hs : ∀ T : Multiset ℂ, ((T.map fun b => X - C b).prod).map ι.symm.toRingHom =
        ((T.map ι.symm).map fun b => X - C b).prod := by
      intro T
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
      simp
    have hc : ι.symm c = ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) := by
      rw [← hk]; simp
    have hfin := hf σ hσ
    rw [hs] at hfin
    have hR : (R.map (· * c)).map ι.symm = (R.map ι.symm).map (· * ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l)) := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp [map_mul, hc]
    rw [UpperTheory.V.Af.tw_val, hs, hR, Multiset.map_map]
    have := aeval_smul_prod (ρ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l)) ((χ σ⁻¹ : (Qbar l)ˣ) : Qbar l) (R.map ι.symm)
    rw [hfin, smul_zero] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwCrys
open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.twCrys :
    UpperTheory.Gal.Int.Geo.TwCrys := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ _ _ w c m hχ hρ P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, -, -, -⟩ := hχ.2 P AI hT A h O Bw hj
  have c2 := hρ P AI hT A h O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  rw [e1] at c1
  rw [e2]
  exact (UpperTheory.Gal.TP.Sub.twLoc_holds l P AI hT E Ω A O Bw dd (ρ.comp (Dec (F := E) A).subtype)
    (χ.comp (Dec (F := E) A).subtype)).2 c2 c1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.JumpsOf
open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.jumpsOf :
    UpperTheory.Gal.Int.Geo.JumpsOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ w Q hQ hJ P AI hT A hA O _ _ _ Bw hBw τ LL' τ' hi lam J hl hJm
  obtain ⟨J', h1, h2⟩ := hJ P AI hT A hA O Bw hBw τ LL' τ' hi
  have e : J = (GlobalTheory.RoadWGeo.wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJm.trans (GlobalTheory.RoadWGeo.wtJumps_val lam).symm)
  refine ⟨J', h1, fun j hj => h2 j (hQ _ (GlobalTheory.CongL.LimAtLU.overPl_of_induced ι hA hBw hi) lam hl j ?_)⟩
  rw [e] at hj
  exact hj
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RichOf
open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_lt_one_iff_mem {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (τ : E →+* Om l)
    (v : HeightOneSpectrum (𝓞 E)) (hv : ∀ x ∈ v.asIdeal, ‖τ (x : E)‖ < 1) (x : 𝓞 E) :
    ‖τ (x : E)‖ < 1 ↔ x ∈ v.asIdeal := by
  refine ⟨fun hx => ?_, hv x⟩
  by_contra hn
  obtain ⟨y, i, hi, e⟩ := v.isMaximal.exists_inv hn
  have hy : ‖τ (y : E)‖ ≤ 1 :=
    GlobalTheory.CongW.PlaceEmb.norm_le_one_of_isIntegral_int ((NumberField.RingOfIntegers.isIntegral_coe y).map τ.toIntAlgHom)
  have h1 : τ (y : E) * τ (x : E) + τ (i : E) = 1 := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) e
    simpa using this
  have h2 : ‖τ (y : E) * τ (x : E)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hy) hx
  have h3 := IsUltrametricDist.norm_add_le_max (τ (y : E) * τ (x : E)) (τ (i : E))
  rw [h1, norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt h2 (hv i hi)))

private theorem exists_place {Ω : Type} [Field Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) :
    ∃ A : ValuationSubring Ω, ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1 :=
  ⟨{ carrier := {x | ‖j x‖ ≤ 1}
     mul_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *; exact mul_le_one₀ ha (norm_nonneg _) hb
     one_mem' := by simp
     add_mem' := fun {a b} ha hb => by
       simp only [Set.mem_setOf_eq, map_add (f := _)] at *
       exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
     zero_mem' := by simp
     neg_mem' := fun {a} ha => by simpa using ha
     mem_or_inv_mem' := fun x => by
       simp only [Set.mem_setOf_eq, map_inv₀, norm_inv]
       rcases le_total ‖j x‖ 1 with h | h
       · exact Or.inl h
       · exact Or.inr (inv_le_one_of_one_le₀ h) }, fun _ => Iff.rfl⟩

theorem UpperTheory.Gal.Int.Geo.richOf :
    UpperTheory.Gal.Int.Geo.RichOf := by
  intro E Ω _ _ _ _ _ _ l _ ι a dd U ρ v hv hlac hJ
  obtain ⟨τc, hover, lam, hw, hl⟩ := hlac
  obtain ⟨P, AI, hT⟩ := GlobalTheory.MemLoc.exists_locPrime_tied l
  let τ₀ : E →+* Om l := ι.symm.toRingHom.comp τc
  have hτ₀ : ι.toRingHom.comp τ₀ = τc := by
    ext x
    simp [τ₀]
  have hsmall : ∀ x ∈ v.asIdeal, ‖τ₀ (x : E)‖ < 1 := hover
  letI : Algebra E (Om l) := τ₀.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[E] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let j : Ω →+* Om l := jA.toRingHom
  have hjτ : ∀ x : E, j (algebraMap E Ω x) = τ₀ x := fun x => jA.commutes x
  obtain ⟨A, hA⟩ := exists_place j
  obtain ⟨L, Bw, hBj, -, -⟩ := GlobalTheory.PhtCompare.exists_bridge (E := E) (A := A) j hA
  have hBw : Induces Bw := fun x => by rw [hBj]; exact hA x
  have hP : IsPlaceOver A v := fun x => by
    rw [hBw.valuation_lt_one_iff, hBj, hjτ]
    exact norm_lt_one_iff_mem τ₀ v hsmall x
  have hi : IsInduced Bw τ₀ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := fun x => by
    show τ₀ x = Bw.j (algebraMap E Ω x)
    rw [hBj, hjτ]
  obtain ⟨J', hJ', hsub⟩ := hJ P AI hT A hP _ Bw hBw τ₀ Bw.Kw (AlgHom.id ℚ_[l] ↥Bw.Kw.1) hi lam (wtJumps lam).val
    (by rw [hτ₀]; exact hw) (wtJumps_val lam)
  exact ⟨P, AI, hT, v, A, hv, hP, _, inferInstance, inferInstance, inferInstance, Bw, hBw, τ₀, J', hJ',
    wtJumps lam, card_wtJumps lam, fun j hj => hsub j hj, hl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.TwJ
open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.Int.Geo.twJ :
    UpperTheory.Gal.Int.Geo.TwJ := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ χ hρ hχ w c m h1 Q hQ P AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
  obtain ⟨J, hJ, hJQ⟩ := hQ P AI hT A hA O Bw hj τ LL' τ' hi
  obtain ⟨-, -, j1, -⟩ := h1.2 P AI hT A hA O Bw hj
  have e1 : (rk1 χ).comp (Dec (F := E) A).subtype = rk1 (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw ρ χ).comp (Dec (F := E) A).subtype =
      tw (ρ.comp (Dec (F := E) A).subtype) (χ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have j2 := j1 τ LL' τ' hi
  rw [e1] at j2
  have cs : Continuous (ρ.comp (Dec (F := E) A).subtype) := hρ.comp continuous_subtype_val
  have cμ : Continuous (χ.comp (Dec (F := E) A).subtype) := hχ.comp continuous_subtype_val
  refine ⟨J.map (· + m (ι.toRingHom.comp τ)), ?_, fun j hj' => ?_⟩
  · rw [e2]
    exact UpperTheory.Gal.TP.Sub.twJumps_holds l P AI hT E Ω A O Bw dd _ _ cs cμ τ J _ hJ j2
  · exact Multiset.mem_map.2 ⟨_, hJQ _ hj', by simp⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.UnrPolNegOne
open Neutral.B1 hiding G IsPlaceOver Dec
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem unrPol_neg_one (S : Multiset ℂ) : unrPol S (-1) = rootPol S := by
  simp [unrPol, rootPol]

theorem UpperTheory.Gal.Int.Geo.phiOf :
    UpperTheory.Gal.Int.Geo.PhiOf := by
  intro E Ω _ _ _ _ _ l _ ι dd ρ w a B _ hK P AI hT A h O _ _ _ Bw hj
  obtain ⟨hc, g, hg, m, hd⟩ := hK P AI hT A h O Bw hj
  refine ⟨hc, g, hg, m, ?_⟩
  rw [UpperTheory.Gal.TP.Sub.satPol_holds E Ω A w h a B g, hg, unrPol_neg_one]
  exact hd
end

namespace UpperTheory.Gal.Int.Geo

theorem steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps :=
  ⟨repEx_holds, Mod.esStep_holds, hC, hJ, hP, cutStep_holds, twES, twCrys, twJ, twPhi, phiOf, satCard, jumpsOf, richOf,
    TP.Sub.charEx, TP.Sub.sSLeft_holds, TP.Sub.contLeft_holds⟩

end UpperTheory.Gal.Int.Geo
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.GeoOneOfParts
namespace UpperTheory.Gal.Int.Geo

theorem geoOne_of_parts (h₁ : Steps) (h₂ : KSAll) (h₃ : PlanEx) : GeoOne := geoOne_of h₁ (packEx_of h₂ h₃)

end UpperTheory.Gal.Int.Geo
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PScalEx
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

private theorem scalEx_of :
    UpperTheory.Gal.G3.SysOf → UpperTheory.Gal.FixZ.ScalEx := by
  intro hS p _ D G L h hI
  obtain ⟨f, u, c, k, hsys, -, hk, -⟩ := hS p D G L h hI
  have hkp : k.Coprime p := hsys.2.1
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : p = 1 := by simpa using hkp
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hone : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _
  have hact : ∀ v, L.actG (GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0)) v = k • v :=
    GlobalTheory.W2.actG_natScalar L k hk0
  refine ⟨k, GlobalTheory.W2.scalarAf G (GlobalTheory.W2.natUnit p k hk0), Nat.pos_of_ne_zero hk0, hkp,
    ⟨fun g => GlobalTheory.W2.scalarAf_comm _ g, hact, 1, 1, hone, hone, one_mul 1, ?_⟩, ?_, ?_⟩
  · show ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) * (GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) = ((k ^ 2 : ℕ) : AfP p) * 1
    have e : ((GlobalTheory.W2.natUnit p k hk0 : (AfP p)ˣ) : AfP p) = (k : AfP p) := by
      show algebraMap ℚ (AfP p) (k : ℚ) = _
      rw [map_natCast]
    rw [e, mul_one]; push_cast; ring
  · intro v hv
    rw [hact]
    exact nsmul_mem hv k
  · intro v hv
    rw [map_mul, Module.End.mul_apply, hact]
    exact hk v hv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PTrScal
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (KS Lv Sc Integ IsTrans)

private theorem powMap_scal {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (d k : ℕ) (Φ : A.left ⟶ A.left)
    (hw : Φ ≫ A.hom = A.hom ≫ 𝟙 S) (h : Φ = ((𝟙 A) ^ d).left) :
    GlobalTheory.KS.powMap (𝟙 S) Φ hw k = (Limits.Pi.map (fun _ : Fin k => (𝟙 A) ^ d)).left := by
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [GlobalTheory.KS.PowPB.powMap_w, Over.w, Category.comp_id]
  · intro i
    rw [GlobalTheory.KS.PowPB.powMap_pr, h, ← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold KS.pr
    simp

private theorem trScal_of :
    UpperTheory.Gal.G3.WitUniq → UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.WitScal → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.TrScal := by
  intro hWU hIso hWS hPow p _ D G L gb k T N d z hd hdp hsc a b
  obtain ⟨π, o, ψ, φ, hw, hπ, htr, heq⟩ := T.tr_eq N N z a b
  have hI : Integ L z := (T.Δ_eq z).1 a
  have hA : UpperTheory.Gal.G3.AdmK L N.1 N.1 z := by
    intro u hu
    have hb := b u (by rw [T.K_eq]; exact hu)
    rwa [T.K_eq] at hb
  obtain ⟨rfl, hΦ⟩ := hWU p D G L ℂ gb N N (T.M N) (T.M N) z hI hA π (Over.Hom.left ψ ≫ φ.φ) (𝟙 _)
    (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ⟨hπ, o, ψ, φ, htr, rfl⟩ (hWS p D G L gb N (T.M N) d z hd hdp hsc)
  have hpm := GlobalTheory.DrinLev.HT.MulModel.isMonHom_id_pow (T.M N).univ.A d
  have hS := powMap_scal (T.M N).univ.A d k _ hw hΦ
  rw [hS] at heq
  have hfe : IsFinite (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ∧ Etale (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) ∧
      Surjective (Over.Hom.left (𝟙 (T.M N).univ.A ^ d)) := by
    refine hIso ℂ _ (T.M N).s _ _ (T.M N).univ.ab (T.M N).univ.ab (𝟙 _ ^ d) (𝟙 _ ^ d) (d * d)
      (Nat.mul_pos hd hd) hpm hpm ?_ ?_
    · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
    · rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]
  obtain ⟨hf1, hf2, -⟩ := hPow _ (T.M N).univ.A k (fun _ => 𝟙 _ ^ d) (fun _ => hfe)
    (Limits.Pi.map (fun _ : Fin k => 𝟙 (T.M N).univ.A ^ d)) (fun i => by unfold KS.pr; simp)
  have htr' : T.X.tr (T.lev N) (T.lev N) z a b =
      (T.e N).hom ≫ Over.Hom.left (Limits.Pi.map (fun _ : Fin k => 𝟙 (T.M N).univ.A ^ d)) ≫ (T.e N).inv := by
    rw [← Category.assoc, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [htr']
  constructor
  · infer_instance
  · infer_instance
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PEtCancel
open AlgebraicGeometry in
private theorem etCancel_of :
    UpperTheory.Gal.FixZ.EtCancel := by
  intro A B C E f g f' hg hfin1 het1 hfin2 het2
  have h1 : AlgebraicGeometry.IsSeparated (CategoryTheory.CategoryStruct.comp g f') :=
    inferInstance
  have h2 : AlgebraicGeometry.IsSeparated g := AlgebraicGeometry.IsSeparated.of_comp g f'
  have h3 : AlgebraicGeometry.FormallyUnramified g :=
    AlgebraicGeometry.FormallyUnramified.of_comp g f'
  exact ⟨AlgebraicGeometry.IsFinite.of_comp f g, AlgebraicGeometry.Etale.of_comp f g⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescEt
open AlgebraicGeometry CategoryTheory
private theorem descEt_of : UpperTheory.Gal.FixZ.DescEt := by
  intro A B C c f hc hs hf hcf
  exact GlobalTheory.etale_of_comp_of_etale_of_surjective c f
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDescFin
open AlgebraicGeometry CategoryTheory
private theorem descFin_of : UpperTheory.Gal.FixZ.DescFin := by
  intro A B C c f hc hs he hfin
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective c f
  have : IsProper f := { }
  have : LocallyQuasiFinite f := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PLegOf
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
private theorem legOf_of : UpperTheory.Gal.FixZ.LegOf := by
  intro p _ D G L gb k T N' N h b
  obtain ⟨π, o, ψ, φ, hw, hs, htr, he⟩ := T.tr_eq N' N h b.1 b.2
  refine ⟨UpperTheory.Gal.W2.Leg.mk π o ψ φ hs ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.2⟩, he, fun α => ?_⟩
  simp only [UpperTheory.Gal.LocalSmoothExtension.leg, UpperTheory.Gal.LocalSmoothExtension.al, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PDimUniq
open AlgebraicGeometry CategoryTheory
private lemma relDim_eq_of_ringHom {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] (f : R →+* S)
    {m n : ℕ} (hm : f.IsStandardSmoothOfRelativeDimension m)
    (hn : f.IsStandardSmoothOfRelativeDimension n) : m = n := by
  letI := f.toAlgebra
  have e₁ : Module.rank S Ω[S⁄R] = m :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ m hm
  have e₂ : Module.rank S Ω[S⁄R] = n :=
    @Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential R S _ _ _ _ n hn
  exact_mod_cast e₁.symm.trans e₂

private lemma exists_nontrivial_away {S : Type} [CommRing S] [Nontrivial S] (s : Set S)
    (hs : Ideal.span s = ⊤) : ∃ t ∈ s, Nontrivial (Localization.Away t) := by
  by_contra hne
  push_neg at hne
  have hsub : s ⊆ nilradical S := by
    intro t ht
    haveI : Subsingleton (Localization.Away t) := hne t ht
    have h0 : algebraMap S (Localization.Away t) 1 = algebraMap S (Localization.Away t) 0 :=
      Subsingleton.elim _ _
    obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers t) _).1 h0
    obtain ⟨k, rfl⟩ := hc
    exact ⟨k, by simpa using hc'⟩
  have hle := Ideal.span_le.2 hsub
  rw [hs, top_le_iff] at hle
  have h1 : (1 : S) ∈ nilradical S := hle ▸ Submodule.mem_top
  obtain ⟨k, hk⟩ := h1
  simp at hk

private lemma relDim_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) (x : X) : m = n := by
  obtain ⟨U, hU, V, hV, hx, e, hmU⟩ := hm.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hst⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f hn ⟨U, hU⟩ ⟨V, hV⟩ e
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨t, ht, hnt⟩ := exists_nontrivial_away s hs
  have hm' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway m).2
    (Localization.Away t) t _ hmU
  exact relDim_eq_of_ringHom _ hm' (hst t ht)

private theorem dimUniq_of : UpperTheory.Gal.FixZ.DimUniq := by
  intro Z s d d' hd hd' hZ
  obtain ⟨z⟩ := hZ
  exact relDim_eq s hd hd' z
end

namespace UpperTheory.Gal.FixZ

private theorem translation_finite_etale_of_isogeny_data (h1 : G3.SysOf) (h2 : G3.RelComp) (h3 : G3.WitUniq) (h4 : G3.IsogFEt) (h5 : G3.PowSm) : TrFEt :=
  trFEt_of h5 (scalEx_of h1) (trScal_of h3 h4 (witScal_of h2) powFEt_of) etCancel_of descEt_of descFin_of

theorem FixK_holds : LocalSmoothExtension.FixK :=
  bridge_of (translation_finite_etale_of_isogeny_data G3.sysOf_holds G3.relComp_holds G3.witUniq_holds G3.isogFEt_holds G3.powSm_holds)
    (alFEt_of G3.isogFEt_holds powFEt_of) legOf_of wtEq_of tanIso_of dimUniq_of cxFinOf_of
    W2.fixedPoints_int_base_holds W2.FixZ_holds

end UpperTheory.Gal.FixZ

namespace UpperTheory.Gal.Int.Geo

theorem jumpStep_holds : JumpStep := G3.jumpStep_of Seam.HT.htSpecGood Seam.crysStep_holds repEx_holds

theorem steps_holds : Steps := steps_of Seam.crysStep_holds jumpStep_holds UpperTheory.Ru.crystallineComparison.phiStep

theorem kodaira_spencer_of_weight_one (hW : LocalSmoothExtension.HolomorphicLefschetzFormula) : KSAll :=
  ⟨CovMain.stdEx_holds, G3.kSEx_holds, G3.kSNice_holds, FiniteEtaleModels.ksGood_holds, CovMain.ksCong_holds, LocalSmoothExtension.ksHodge_of_geo hW FixZ.FixK_holds⟩

theorem geometric_realization_of_weight_one (hW : LocalSmoothExtension.HolomorphicLefschetzFormula) : GeoOne := geoOne_of_parts steps_holds (kodaira_spencer_of_weight_one hW) Pl.planEx_holds

end UpperTheory.Gal.Int.Geo
end

namespace UpperTheory.Gal.Int.Geo

theorem weight_one_geometric_realization : LocalSmoothExtension.HolomorphicLefschetzFormula := by
  unfold LocalSmoothExtension.HolomorphicLefschetzFormula
  exact GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence

theorem geoOne_holds : GeoOne := geometric_realization_of_weight_one weight_one_geometric_realization

end UpperTheory.Gal.Int.Geo
