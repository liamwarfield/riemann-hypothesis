module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev PrincipalizationAlgorithm : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData), NonzeroOnComponents I →
      ∀ E : List X.IdealSheafData, InStrictNormalCrossingPosition p E → IdealBlowupSequence p I E

abbrev specMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom f)

theorem specMapOfFieldHom_eq (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    specMapOfFieldHom k K f = Spec.map (CommRingCat.ofHom f) := rfl

instance instSurjectiveSpecMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Surjective (specMapOfFieldHom k K f) := by
  have hk : Subsingleton (PrimeSpectrum k) := by
    refine ⟨fun x y => ?_⟩
    have hx : x.asIdeal = ⊥ := x.asIdeal.eq_bot_or_top.resolve_right x.isPrime.ne_top
    have hy : y.asIdeal = ⊥ := y.asIdeal.eq_bot_or_top.resolve_right y.isPrime.ne_top
    exact PrimeSpectrum.ext (hx.trans hy.symm)
  obtain ⟨x⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  refine ⟨fun y => ⟨x, ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum k) _ _

instance instFlatSpecMapOfFieldHom (k K : Type u) [Field k] [Field K] (f : k →+* K) :
    Flat (specMapOfFieldHom k K f) := by
  show Flat (Spec.map (CommRingCat.ofHom f))
  let _inst : Algebra k K := f.toAlgebra
  have hflat : Module.Flat k K := inferInstance
  have hf : RingHom.Flat (CommRingCat.ofHom f).hom := hflat
  exact HasRingHomProperty.Spec_iff.mpr hf

structure IsFunctorialPrincipalization (A : PrincipalizationAlgorithm.{u}) : Prop where
  pushforward :
    ∀ (k : Type u) [Field k] [CharZero k] (S X : Scheme.{u})
      (pS : S ⟶ Spec (CommRingCat.of k)) (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth pS] [AlgebraicGeometry.LocallyOfFiniteType pS]
      [AlgebraicGeometry.QuasiCompact pS]
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (j : S ⟶ X) [IsClosedImmersion j] (_ : j ≫ p = pS)
      (c : ℕ) (_ : 1 ≤ c) (_ : HasEtaleCoordCodim p j c)
      (I : S.IdealSheafData) (hI : NonzeroOnComponents I)
      (hIX : NonzeroOnComponents (imageIdealSheaf j I))
      (hES : InStrictNormalCrossingPosition pS ([] : List S.IdealSheafData))
      (hEX : InStrictNormalCrossingPosition p ([] : List X.IdealSheafData)),
      IsPushforwardBlowupSeq j (A k S pS I hI [] hES).toSequenceOfBlowups
        (A k X p (imageIdealSheaf j I) hIX [] hEX).toSequenceOfBlowups
  base_change :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (K : Type u) [Field K] [CharZero K] (f : k →+* K)
      [AlgebraicGeometry.Smooth (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.QuasiCompact (pullback.snd p (specMapOfFieldHom k K f))]
      (hI' : NonzeroOnComponents (I.comap (pullback.fst p (specMapOfFieldHom k K f))))
      (hE' : InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k K f))
        (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f)))),
      IsPullbackBlowupSequence (pullback.fst p (specMapOfFieldHom k K f))
        (A K (pullback p (specMapOfFieldHom k K f)) (pullback.snd p (specMapOfFieldHom k K f))
          (I.comap (pullback.fst p (specMapOfFieldHom k K f))) hI'
          (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f))) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  base_change_strict :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (K : Type u) [Field K] [CharZero K] (f : k →+* K)
      [AlgebraicGeometry.Smooth (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.LocallyOfFiniteType (pullback.snd p (specMapOfFieldHom k K f))]
      [AlgebraicGeometry.QuasiCompact (pullback.snd p (specMapOfFieldHom k K f))]
      (hI' : NonzeroOnComponents (I.comap (pullback.fst p (specMapOfFieldHom k K f))))
      (hE' : InStrictNormalCrossingPosition (pullback.snd p (specMapOfFieldHom k K f))
        (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f)))),
      IsStrictPullbackBlowupSeq (pullback.fst p (specMapOfFieldHom k K f))
        (A K (pullback p (specMapOfFieldHom k K f)) (pullback.snd p (specMapOfFieldHom k K f))
          (I.comap (pullback.fst p (specMapOfFieldHom k K f))) hI'
          (E.map fun D => D.comap (pullback.fst p (specMapOfFieldHom k K f))) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  lastIdeal_eq_top :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E),
      (A k X p I hI E hE).lastIdeal = ⊤
  smooth_pullback :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
      [AlgebraicGeometry.QuasiCompact p']
      (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] (_ : φ ≫ p = p')
      (hI' : NonzeroOnComponents (I.comap φ))
      (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)),
      IsPullbackBlowupSequence φ
        (A k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups
  smooth_pullback_strict :
    ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (p : X ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p]
      (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
      (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
      (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
      [AlgebraicGeometry.QuasiCompact p']
      (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] [AlgebraicGeometry.Surjective φ]
      (_ : φ ≫ p = p')
      (hI' : NonzeroOnComponents (I.comap φ))
      (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)),
      IsStrictPullbackBlowupSeq φ
        (A k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE').toSequenceOfBlowups
        (A k X p I hI E hE).toSequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificateMonotone
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem forall_principalizationCertificate_of_subset {k : Type u} [Field k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (motive_2 := fun W p N μ Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hmem Mem' hsub
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hsub
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hsub) hmu hZ (ih Mem' hsub)
  · intro W p I m Mem Z U hU _ ih Mem' hsub
    refine PrincipalizationCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z hmem Mem' hsub
    exact OrderCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hsub
    refine OrderCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hsub
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJz x hx
      exact hJloc z hz Jz hJz x fun hmem => hx (hsub hmem)
    · intro z hz Jz hJz
      exact ih z hz Jz hJz (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hsub)

theorem principalizationCertificate_mono_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m Mem' Z :=
  forall_principalizationCertificate_of_subset h Mem' hsub

private theorem forall_orderCertificate_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z := by
  refine @OrderCertificate.rec k ‹Field k›
    (fun W p I m Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (fun W p N μ Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ W p N μ Mem Z h
  · intro W p I m Mem Z hmem Mem' hs
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hs
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hs) hmu hZ (ih Mem' hs)
  · intro W p I m Mem Z U hU _ ih Mem' hs
    exact PrincipalizationCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z hmem Mem' hs
    exact OrderCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hs
    exact OrderCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hs
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJ x hx
      exact hJloc z hz Jz hJ x fun hm => hx (hs hm)
    · intro z hz Jz hJ
      exact ih z hz Jz hJ (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hs)

theorem orderCertificate_mono_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W p N μ Mem' Z :=
  forall_orderCertificate_of_subset h Mem' hsub

end FunctorialResolution.EmbeddedResolution
end
