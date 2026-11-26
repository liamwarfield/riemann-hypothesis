module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SepClosedPointFilteredEtaleColimit
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechLevelIsoSigmaIntersectionsOfCoprod
public import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
public import Development.EtaleCohomology.EtaleSheaves.AffinePf
public import Development.EtaleCohomology.EtaleSheaves.ChasePf
public import Development.EtaleCohomology.EtaleSheaves.ArchimedeanComparison
public import Development.EtaleCohomology.EtaleSheaves.LeafConsPfC
public import Development.EtaleCohomology.EtaleSheaves.LocSHPf
public import Development.EtaleCohomology.EtaleSheaves.IdemCoverPf
public import Development.EtaleCohomology.EtaleSheaves.SecPrePf
public import Development.EtaleCohomology.EtaleSheaves.ResBijPf
public import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
public import Development.EtaleCohomology.EtaleSheaves.PointwisePf
public import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks.PolyPO
public import Development.EtaleCohomology.WeilConjectures.EtaleAlgebrasHaveSmallModelSet
public import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks.ULAStalkOf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.CompositionGoal
namespace LateralTheory.E.CompositionGoal

theorem goal_of : LateralTheory.E.SHExistsPf.Comp := LateralTheory.E.TruncationIsoComparison.Comp_of

end LateralTheory.E.CompositionGoal
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpSOfIntegralInjective
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ULAPf
open LateralTheory.E.t_E3Cut

theorem spS_of_integral_injective {C D : CommRingCat.{0}} (g : C ⟶ D) (hi : g.hom.IsIntegral)
    (hj : Function.Injective g.hom) : SpS g := by
  intro r hr
  letI := g.hom.toAlgebra
  have : Algebra.IsIntegral C D := ⟨hi⟩
  have hk : RingHom.ker (algebraMap C D) ≤ r := by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap C D)).1 hj]; exact bot_le
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral r ⊥ (by rw [Ideal.under_def C (B := D), ← RingHom.ker_eq_comap_bot (algebraMap C D)]; exact hk)
  exact ⟨Q, hQ, hQc⟩

theorem SpS.comp {C D E : CommRingCat.{0}} {f : C ⟶ D} {g : D ⟶ E} (hf : SpS f) (hg : SpS g) : SpS (f ≫ g) := by
  intro r hr
  obtain ⟨Q0, hQ0, hQ0c⟩ := hf r hr
  obtain ⟨Q, hQ, hQc⟩ := hg Q0 hQ0
  exact ⟨Q, hQ, by rw [CommRingCat.hom_comp, ← Ideal.comap_comap, hQc, hQ0c]⟩

theorem ULA_of (hS : Stalk) (hP : AlgResProps) (hE : AICExt) (hD : DomCover) (hL : LocIE) (hU : ULAStalk) : ULA := by
  intro H q _ i A X h hq hA hX hIE hloc C c hc
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP
  refine hS H q i (pC A ≫ h) hq (fun _ c => AlgRes c) ?_ ?_ ?_ C c hc
  · intro C D E Z c f g u v hpo _ hf hg
    have hv : AlgRes v := p3 f g u v hpo (p2 c f hf)
    have := p1 (c ≫ g) v hg hv
    rw [hpo.w, ← Category.assoc]; exact this
  · intro C D c f hc hf
    exact p1 c f hc (p4 f hf)
  · intro C c hc
    obtain ⟨D0, g0, hg0i, hg0j, hg0a⟩ := hE C
    obtain ⟨D, g1, hg1i, hg1s, hg1d⟩ := hD D0 hg0a
    have hgi : (g0 ≫ g1).hom.IsIntegral := by
      rw [CommRingCat.hom_comp]; exact RingHom.IsIntegral.trans _ _ hg0i hg1i
    refine ⟨D, g0 ≫ g1, hgi, SpS.comp (spS_of_integral_injective g0 hg0i hg0j) hg1s,
      p1 c (g0 ≫ g1) hc (p5 _ hgi), ?_⟩
    intro r hr
    have := hr
    obtain ⟨hdom, haic⟩ := hg1d r
    let o : D ⟶ CommRingCat.of (Localization.AtPrime r) := CommRingCat.ofHom (algebraMap D _)
    have ho : AlgRes o := p6 D (Localization.AtPrime r) r.primeCompl
    refine ⟨CommRingCat.of (Localization.AtPrime r), o, IsLocalRing.maximalIdeal _,
      hL D (Localization.AtPrime r) r.primeCompl, inferInstance,
      IsLocalization.AtPrime.under_maximalIdeal _ r, ?_⟩
    haveI : IsDomain (CommRingCat.of (Localization.AtPrime r)) := hdom
    haveI : IsLocalRing (CommRingCat.of (Localization.AtPrime r)) :=
      inferInstanceAs (IsLocalRing (Localization.AtPrime r))
    exact hU H q i h hq hA hX hIE hloc _ (c ≫ (g0 ≫ g1) ≫ o) haic
      (p1 c _ hc (p1 _ o (p5 _ hgi) ho))

end LateralTheory.E.ULAPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BasePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.BasePf

theorem polyPO {A C : CommRingCat.{0}} (f : A ⟶ C) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC C) := by
  algebraize [f.hom, Polynomial.mapRingHom f.hom]
  exact (CommRingCat.isPushout_of_isPushout A C (Polynomial A) (Polynomial C)).flip

theorem et_map {A C : CommRingCat.{0}} (f : A ⟶ C) (hf : Et f) :
    Et (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty RingHom.Etale).of_isPushout (polyPO f) hf

theorem Base_of (h : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial) : LateralTheory.E.t_E3Cut.Base := by
  intro H q _ i T _ _ _ hT hq B c hc Y' w φ' hpo
  rw [Category.id_comp] at hpo
  have hc4 : C4 := H.2.2.2.2.2.2.2.2.2.2
  have hqB : IsUnit (q : B) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqB.map φ'.hom
  have sq := hpo.flip.paste_horiz (polyPO φ')
  have e1 : c ≫ pC B = pC (CommRingCat.of T) ≫ CommRingCat.ofHom (Polynomial.mapRingHom c.hom) := by
    ext x; simp
  rw [e1] at sq
  have hIE : IE (CommRingCat.ofHom (Polynomial.mapRingHom c.hom)) :=
    MorphismProperty.le_ind _ _ (et_map c hc)
  have r2 : RE q i (CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom)) :=
    h H q i T (FractionRing T) hT hq _ _ hIE _ _ _ sq.flip
  have r1 : RE q i (pC B) := hc4 q B hqB i
  have r3 : RE q i (pC Y') := hc4 q Y' hqY i
  have e2 : pC B ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom) = φ' ≫ pC Y' := by
    ext x; simp
  have r4 : RE q i (φ' ≫ pC Y') := e2 ▸ r1.comp r2
  exact RE.of_comp_right r3 r4

end LateralTheory.E.BasePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntClosPf
noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IntClosPf

theorem intMul {A C : Type} [CommRing A] [CommRing C] [IsDomain C] [Algebra A C] (z : C) (p : Polynomial A)
    (hp : ∃ n, algebraMap A C (p.coeff n) ≠ 0) (hz : Polynomial.aeval z p = 0) :
    ∃ a : A, algebraMap A C a ≠ 0 ∧ IsIntegral A (algebraMap A C a * z) := by
  let A' := (algebraMap A C).range
  letI : Algebra A A' := (algebraMap A C).rangeRestrict.toAlgebra
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hsurj : Function.Surjective (algebraMap A A') := (algebraMap A C).rangeRestrict_surjective
  have : Algebra.IsIntegral A A' := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hsurj x
    exact isIntegral_algebraMap⟩
  set p' := p.map (algebraMap A A') with hp'def
  have h1 : Polynomial.aeval z p' = 0 := by rw [Polynomial.aeval_map_algebraMap]; exact hz
  have hp' : p' ≠ 0 := by
    intro h0
    obtain ⟨n, hn⟩ := hp
    apply hn
    have : p'.coeff n = 0 := by rw [h0]; rfl
    rw [hp'def, Polynomial.coeff_map] at this
    have := congrArg Subtype.val this
    exact this
  have hint := isIntegral_leadingCoeff_smul p' z h1
  obtain ⟨a, ha⟩ := hsurj p'.leadingCoeff
  have hlc : p'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp'
  have hval : algebraMap A C a = (p'.leadingCoeff : C) := by rw [← ha]; rfl
  refine ⟨a, ?_, ?_⟩
  · rw [hval]; intro h; exact hlc (Subtype.ext h)
  · have h2 : algebraMap A C a * z = p'.leadingCoeff • z := by rw [Algebra.smul_def, hval]; rfl
    rw [h2]
    exact isIntegral_trans _ hint

theorem IntClos_of (hH : HensInt) : IntClos := by
  intro A C c _ hSH hAIC hAR
  obtain ⟨hHA, -⟩ := hSH
  letI : Algebra A C := c.hom.toAlgebra
  let B := integralClosure A C
  refine ⟨CommRingCat.of B, CommRingCat.ofHom (algebraMap A B), CommRingCat.ofHom B.val.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x; rfl
  · intro x; exact integralClosure.isIntegral x
  · exact Subtype.val_injective
  · have hne : Nontrivial B := inferInstance
    obtain ⟨h⟩ := hH A B (algebraMap A B) (fun x => integralClosure.isIntegral x) (fun e he => by
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (show IsIdempotentElem (e : C) from congrArg Subtype.val he)) with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h)
    exact h.toIsLocalRing
  · intro p hm hdeg
    have hm' : (p.map B.val.toRingHom).Monic := hm.map _
    have hdeg' : 0 < (p.map B.val.toRingHom).natDegree := by
      rw [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective]; exact hdeg
    obtain ⟨r, hr⟩ := hAIC _ hm' hdeg'
    have hrB : IsIntegral B r := ⟨p, hm, by rw [← Polynomial.eval_map]; exact hr⟩
    have hrA : IsIntegral A r := isIntegral_trans _ hrB
    have hrM : r ∈ B := hrA
    refine ⟨⟨r, hrM⟩, Subtype.val_injective ?_⟩
    show B.val.toRingHom (p.eval ⟨r, hrM⟩) = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hr
  · intro z
    have hQ : (⊥ : Ideal C).IsPrime := Ideal.isPrime_bot
    obtain ⟨p, ⟨n, hn⟩, hz⟩ := hAR ⊥ hQ z
    obtain ⟨a, ha, hint⟩ := intMul z p ⟨n, fun h => hn (by rw [Ideal.mem_bot]; exact h)⟩
      (by rw [Ideal.mem_bot] at hz; exact hz)
    refine ⟨algebraMap A B a, ⟨_, hint⟩, fun h => ha (congrArg Subtype.val h), rfl⟩

end LateralTheory.E.IntClosPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.HensIntPf
noncomputable section
open IsLocalRing Polynomial

namespace LateralTheory.E.HensIntPf

theorem local_of_finite (A S : Type) [CommRing A] [HenselianLocalRing A] [CommRing S] [Algebra A S]
    [Module.Finite A S] [Nontrivial S] (hid : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => ?_⟩
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian A q
  rcases hid e he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · exact (H n hn).1 (h ▸ fun h1 => hn.ne_top ((Ideal.eq_top_iff_one n).2 h1))

theorem sub_finite (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (Algebra.adjoin A (s : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet (fun x _ => Algebra.IsIntegral.isIntegral (R := A) x)

theorem sub_local (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) : IsLocalRing (Algebra.adjoin A (s : Set B)) := by
  haveI := sub_finite A B s
  refine local_of_finite A _ fun e he => ?_
  rcases hid e (by have h := congrArg Subtype.val he.eq; exact h) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem isLocal (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  haveI := sub_local A B hid {x}
  let y : Algebra.adjoin A ((({x} : Finset B)) : Set B) := ⟨x, Algebra.subset_adjoin (by simp)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h
  · exact Or.inl (h.map (Algebra.adjoin A _).val)
  · exact Or.inr (by simpa [y] using h.map (Algebra.adjoin A _).val)

theorem maxIdeal_comap (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (s : Finset B) :
    letI := isLocal A B hid
    letI := sub_local A B hid s
    (maximalIdeal B).comap (Algebra.adjoin A (s : Set B)).val = maximalIdeal (Algebra.adjoin A (s : Set B)) := by
  letI := isLocal A B hid
  letI := sub_local A B hid s
  haveI : Algebra.IsIntegral (Algebra.adjoin A (s : Set B)) B := Algebra.IsIntegral.tower_top A
  have : ((maximalIdeal B).comap (algebraMap (Algebra.adjoin A (s : Set B)) B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (fun x => Algebra.IsIntegral.isIntegral x) (maximalIdeal B)
  exact IsLocalRing.eq_maximalIdeal this

theorem hens (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B] [Algebra A B]
    [Algebra.IsIntegral A B] (hid : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) : HenselianLocalRing B := by
  classical
  letI := isLocal A B hid
  refine ⟨fun f hf a0 h0 h1 => ?_⟩
  set s : Finset B := insert a0 f.coeffs
  let S := Algebra.adjoin A (s : Set B)
  letI := sub_local A B hid s
  haveI := sub_finite A B s
  haveI : HenselianLocalRing S := GlobalTheory.henselianLocalRing_of_finite A S
  have hc : (↑f.coeffs : Set B) ⊆ S.toSubring := fun c hc =>
    Algebra.subset_adjoin (by simp [s, hc])
  let g : S[X] := f.toSubring S.toSubring hc
  have hgf : g.map S.val.toRingHom = f := f.map_toSubring S.toSubring hc
  let b0 : S := ⟨a0, Algebra.subset_adjoin (by simp [s])⟩
  have hmem : ∀ y : S, y ∈ maximalIdeal S ↔ (y : B) ∈ maximalIdeal B := fun y => by
    rw [← maxIdeal_comap A B hid s]; rfl
  have he' : ∀ (p : S[X]) (y : S), ((p.eval y : S) : B) = (p.map S.val.toRingHom).eval (y : B) := fun p y => by
    rw [eval_map, ← show S.val.toRingHom y = (y : B) from rfl, eval₂_at_apply]; rfl
  have he : ∀ p : S[X], ((p.eval b0 : S) : B) = (p.map S.val.toRingHom).eval a0 := fun p => he' p b0
  have hgm : g.Monic := by
    rw [← hgf] at hf; exact Polynomial.monic_of_injective Subtype.val_injective hf
  obtain ⟨a, ha, ha'⟩ := HenselianLocalRing.is_henselian g hgm b0
    ((hmem _).2 (by rw [he, hgf]; exact h0))
    (by
      rw [← IsLocalRing.notMem_maximalIdeal, hmem, he, ← derivative_map, hgf]
      exact IsLocalRing.notMem_maximalIdeal.2 h1)
  refine ⟨a, ?_, (hmem _).1 ha'⟩
  rw [IsRoot.def, ← hgf, ← he', ha.eq_zero]; rfl

theorem HensInt_of : LateralTheory.E.t_E3Cut.HensInt := by
  intro A B _ _ _ _ f hf hid
  letI : Algebra A B := f.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hf⟩
  exact ⟨hens A B hid⟩

end LateralTheory.E.HensIntPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangePolynomialInductionOfLimit
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.E.t_E3Cut

theorem etale_base_change_fraction_field_of_etale_polynomial_algebra (hC3 : C3) (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (hA : AIC T) (hq : IsUnit (q : T))
    (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C) (hc : Et c) :
    BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c) := by
  letI : Algebra (Polynomial T) C := c.hom.toAlgebra
  haveI : Algebra.Etale (Polynomial T) C := hc
  letI : Algebra T C := (pC (CommRingCat.of T) ≫ c).hom.toAlgebra
  haveI : IsScalarTower T (Polynomial T) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h3 := hC3 q T hA hq C i
  have hsq := CommRingCat.isPushout_tensorProduct T (FractionRing T) C
  let e : CommRingCat.of (FractionRing T) ≅ CommRingCat.of K :=
    (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv.toCommRingCatIso
  have hsq' : IsPushout (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c)
      (e.inv ≫ CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeRight.toRingHom) := by
    refine hsq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x
      simp [e]
    · rfl
    · simp
    · rfl
  exact BC.of_one hsq' h3

theorem etale_base_change_polynomial_induction_of_limit (hL : Limit) : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := by
  intro hH q _ i T K _ _ _ _ _ _ hA hq X h hIE
  have hC3 : C3 := hH.2.2.2.2.2.2.2.2.2.1
  let k := CommRingCat.ofHom (algebraMap T K)
  let φ := pushout.inr k (pC (CommRingCat.of T))
  have P1 : IsPushout k (pC (CommRingCat.of T)) (pushout.inl k (pC (CommRingCat.of T))) φ :=
    IsPushout.of_hasPushout _ _
  have hqX : IsUnit ((q : ℕ) : CommRingCat.of (Polynomial T)) := by
    have := hq.map (Polynomial.C : T →+* Polynomial T)
    simpa using this
  have hEt : ∀ (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C), Et c → BC q i φ c := by
    intro C c hc
    have hb := etale_base_change_fraction_field_of_etale_polynomial_algebra hC3 q i T K hA hq C c hc
    have P2 := IsPushout.of_hasPushout φ c
    exact BC.of_one P2 (hb _ _ _ (P1.paste_vert P2))
  have hB := hL hH q i φ hqX hEt X h hIE
  have P2 := IsPushout.of_hasPushout φ h
  exact BC.of_one (P1.paste_vert P2) (hB _ _ _ P2)

end LateralTheory.E.t_E3Cut
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StrictHenselizationStalkEquivOfColimitPresentati
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.Cb.EtalePushouts

private theorem etCobase : Et.IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange

private theorem etOfPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (s : IsPushout f g u v) (hg : Et g) : Et u :=
  haveI := etCobase
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout s hg

private theorem ieOfPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (s : IsPushout f g u v) (hg : IE g) : IE u :=
  haveI := etCobase
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := MorphismProperty.ind.{0} Et) s hg

private theorem etComp {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : Et f) (hg : Et g) : Et (f ≫ g) := by
  change (f ≫ g).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hf hg

private theorem etRight {R S W : CommRingCat.{0}} {c : R ⟶ S} {f : S ⟶ W} (h1 : Et c) (h2 : Et (c ≫ f)) : Et f := by
  letI := c.hom.toAlgebra
  letI := f.hom.toAlgebra
  letI := (c ≫ f).hom.toAlgebra
  haveI : IsScalarTower R S W := .of_algebraMap_eq' rfl
  haveI : Algebra.Etale R S := h1
  haveI : Algebra.Etale R W := h2
  have h3 : Algebra.Etale S W := {
    formallyEtale := Algebra.FormallyEtale.of_restrictScalars (R := R)
    finitePresentation := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S W }
  exact h3

private theorem polySq {A S : CommRingCat.{0}} (f : A ⟶ S) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC S) := by
  have w : pC A ≫ CommRingCat.ofHom (Polynomial.mapRingHom f.hom) = f ≫ pC S := by
    ext a; simp
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (Polynomial.eval₂RingHom s.inr.hom (s.inl.hom Polynomial.X))) ?_ ?_ ?_⟩⟩
  · intro s
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(s.condition).hom a)
      simpa using this.symm
    · simp
  · intro s
    ext a
    simp
  · intro s m h1 h2
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(h2).hom a)
      simpa using this
    · have := congr($(h1).hom Polynomial.X)
      simpa using this

private theorem exPrime {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
    (h : IsPushout f g u v) (r : Ideal B) (s : Ideal C) [hr : r.IsPrime] [hs : s.IsPrime]
    (e : r.comap f.hom = s.comap g.hom) :
    ∃ p : Ideal D, p.IsPrime ∧ p.comap u.hom = r ∧ p.comap v.hom = s := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ h
  let x : Spec B := ⟨r, hr⟩
  let y : Spec C := ⟨s, hs⟩
  have hxy : Spec.map f x = Spec.map g y := PrimeSpectrum.ext e
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map f) (g := Spec.map g) x y hxy
  let z' : Spec D := sq.isoPullback.inv z
  have e1 : Spec.map u z' = x := by
    rw [← h1, ← sq.isoPullback_inv_fst]; rfl
  have e2 : Spec.map v z' = y := by
    rw [← h2, ← sq.isoPullback_inv_snd]; rfl
  exact ⟨z'.asIdeal, z'.isPrime, congrArg PrimeSpectrum.asIdeal e1, congrArg PrimeSpectrum.asIdeal e2⟩

variable {q : ℕ} {i : ℤ}

private theorem bcBack {T K A Y C : CommRingCat.{0}} {k : T ⟶ K} {a : T ⟶ A} {w : K ⟶ Y} {φ : A ⟶ Y}
    (s : IsPushout k a w φ) {c : A ⟶ C} (h : BC q i k (a ≫ c)) : BC q i φ c :=
  fun _ _ _ s' => h _ _ _ (s.paste_vert s')

private theorem bcFwd {T K A Y C : CommRingCat.{0}} {k : T ⟶ K} {a : T ⟶ A} {w : K ⟶ Y} {φ : A ⟶ Y}
    (s : IsPushout k a w φ) {c : A ⟶ C} (h : BC q i φ c) : BC q i k (a ≫ c) :=
  BC.of_one (s.paste_vert (IsPushout.of_hasPushout φ c)) (h _ _ _ (IsPushout.of_hasPushout φ c))

private theorem coh (hLimit : Limit) (hAlg : AlgResProps) (hSHE : SHEqv) (hULA : ULA) (H : Hyp)
    (q : ℕ) [NeZero q] (i : ℤ) {T K A A' X : CommRingCat.{0}} (k : T ⟶ K) (t : T ⟶ A) (hq : IsUnit (q : T))
    (hk : AlgRes k) (hG : Good q i k t) (f : A ⟶ A') (hf : IE f) (hA' : SH A') (hX : SH X)
    (h : CommRingCat.of (Polynomial A') ⟶ X) (hh : IE h) (hl : IsLocalHom (pC A' ≫ h).hom) :
    BC q i k ((t ≫ f) ≫ pC A' ≫ h) := by
  have hqA : IsUnit (q : A) := by simpa using hq.map t.hom
  have hqA' : IsUnit (q : A') := by simpa using hqA.map f.hom
  have s0 := IsPushout.of_hasPushout k t
  have hL := hLimit H q i (pushout.inr k t) hqA (fun C c hc => bcBack s0 (hG C c hc)) A' f hf
  have s1 := IsPushout.of_hasPushout (pushout.inr k t) f
  have rψ := hL _ _ _ s1
  have aψ := hAlg.2.2.1 _ _ _ _ s1 (hAlg.2.2.1 _ _ _ _ s0 hk)
  have hU := hULA H q i h hqA' hA' hX hh hl _ _ aψ
  have s2 := IsPushout.of_hasPushout (pC A' ≫ h) (pushout.inr (pushout.inr k t) f)
  have rθ := hU _ _ _ s2
  have rx := hSHE H q i (pC A' ≫ h) hqA' hA' hX
  have rw₃ := RE.of_comp_left rx (g := pushout.inl (pC A' ≫ h) (pushout.inr (pushout.inr k t) f))
    (by rw [s2.w]; exact rψ.comp rθ)
  exact BC.of_one ((s0.paste_vert s1).paste_vert s2.flip) rw₃

private theorem geo (hSH : SHExists) (hIE : IEComp) {A U : CommRingCat.{0}}
    (c : CommRingCat.of (Polynomial A) ⟶ U) (hc : Et c) (r : Ideal U) (hr : r.IsPrime) :
    ∃ (A' X : CommRingCat.{0}) (f : A ⟶ A') (h : CommRingCat.of (Polynomial A') ⟶ X) (o : U ⟶ X) (Q : Ideal X),
      IE f ∧ SH A' ∧ SH X ∧ IE h ∧ IsLocalHom (pC A' ≫ h).hom ∧ IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
        pC A ≫ c ≫ o = f ≫ pC A' ≫ h := by
  obtain ⟨A', f, hf, hA', hfr⟩ := hSH A (r.comap (pC A ≫ c).hom) inferInstance
  obtain ⟨_, -⟩ := id hA'
  have hsq := IsPushout.of_hasPushout (pC A ≫ c) f
  obtain ⟨r', hr', e₁, e₂⟩ := exPrime hsq r (IsLocalRing.maximalIdeal A') (by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hfr a)
  obtain ⟨X, f₂, hf₂, hX, hfr₂⟩ := hSH _ r' hr'
  obtain ⟨_, -⟩ := id hX
  let u₁ := pushout.inl (pC A ≫ c) f
  let u₂ := pushout.inr (pC A ≫ c) f
  let h₀ : CommRingCat.of (Polynomial A') ⟶ pushout (pC A ≫ c) f :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom u₂.hom (u₁.hom (c.hom Polynomial.X)))
  have e0 : pC A' ≫ h₀ = u₂ := by
    ext a; simp [h₀]
  have e1 : CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫ h₀ = c ≫ u₁ := by
    ext1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have := congr($(hsq.w).hom a)
      simpa [h₀, u₁, u₂] using this.symm
    · simp [h₀]
  have hpo : IsPushout (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) c h₀ u₁ :=
    IsPushout.of_top (by rw [e0]; exact hsq.flip) e1 (polySq f).flip
  have hh₀ : Et h₀ := etOfPushout hpo hc
  have e3 : (IsLocalRing.maximalIdeal X).comap f₂.hom = r' := by
    ext a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (hfr₂ a).symm
  refine ⟨A', X, f, h₀ ≫ f₂, u₁ ≫ f₂, IsLocalRing.maximalIdeal X, hf, hA', hX,
    hIE _ _ (MorphismProperty.le_ind _ _ hh₀) hf₂, ?_, hIE _ _ (ieOfPushout hsq hf) hf₂, inferInstance, ?_, ?_⟩
  · refine ⟨fun a ha => ?_⟩
    by_contra hn
    have hm : a ∈ IsLocalRing.maximalIdeal A' := hn
    rw [← e₂, Ideal.mem_comap] at hm
    refine (hfr₂ _).1 hm ?_
    have e4 : (pC A' ≫ h₀ ≫ f₂) = u₂ ≫ f₂ := by rw [← Category.assoc, e0]
    rw [e4] at ha
    exact ha
  · rw [CommRingCat.hom_comp, ← Ideal.comap_comap, e3]
    exact e₁
  · rw [← Category.assoc (pC A') h₀ f₂, e0, ← Category.assoc f u₂ f₂]
    have e5 : f ≫ u₂ = (pC A ≫ c) ≫ u₁ := hsq.w.symm
    rw [e5]
    simp only [Category.assoc]

end UpperTheory.Cb.EtalePushouts

open UpperTheory.Cb.EtalePushouts in
theorem UpperTheory.Cb.strictHenselization_stalk_equiv_of_colimit_presentation :
    LateralTheory.E.t_E3Cut.Stalk → LateralTheory.E.t_E3Cut.Limit → LateralTheory.E.t_E3Cut.SHExists → LateralTheory.E.t_E3Cut.IEComp → LateralTheory.E.t_E3Cut.AlgResProps → LateralTheory.E.t_E3Cut.SHEqv → LateralTheory.E.t_E3Cut.ULA → LateralTheory.E.t_E3Cut.Step := by
  intro hStalk hLimit hSH hIE hAlg hSHE hULA H q _ i T K A k t hq hk hG B c hc
  have hqP : IsUnit (q : CommRingCat.of (Polynomial A)) := by simpa using hq.map (t ≫ pC A).hom
  have s := IsPushout.of_hasPushout k (t ≫ pC A)
  refine bcFwd s (hStalk H q i (pushout.inr k (t ≫ pC A)) hqP (fun _ c => Et c) ?_ ?_ ?_ B c hc)
  · intro C D E Z c f g u v sq hc hf hg
    rw [← Category.assoc]
    exact etComp hf (etOfPushout sq (etRight hc hg))
  · intro C D c f hc hf
    exact etComp hc hf
  · intro U c hc
    refine ⟨U, 𝟙 U, ?_, fun r hr => ⟨r, hr, Ideal.comap_id r⟩, ?_, fun r hr => ?_⟩
    · exact RingHom.isIntegral_of_surjective _ Function.surjective_id
    · simpa using hc
    · obtain ⟨A', X, f, h, o, Q, hf, hA', hX, hh, hl, ho, hQ, hQr, e⟩ := geo hSH hIE c hc r hr
      refine ⟨X, o, Q, ho, hQ, hQr, bcBack s ?_⟩
      have hb := coh hLimit hAlg hSHE hULA H q i k t hq hk hG f hf hA' hX h hh hl
      have e' : (t ≫ pC A) ≫ c ≫ 𝟙 U ≫ o = (t ≫ f) ≫ pC A' ≫ h := by
        simp only [Category.id_comp, Category.assoc]
        rw [e]
      rw [e']
      exact hb
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyContinuityFilteredColimitRings
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.DirectSumIndependence

private abbrev P (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    Ht q (sch.obj (Spec A)) n i →+ Ht q (sch.obj (Spec B)) n i :=
  pull _ (sch.map (Spec.map f)) (tw q i) n

private theorem pullback_comp₂ (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : Ht q (sch.obj (Spec A)) n i) : P q i n (f ≫ g) x = P q i n g (P q i n f x) := by
  show pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n x = _
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

private theorem isUnit_of_hom {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) :
    IsUnit (q : B) := by
  simpa using h.map f.hom

private theorem chase (b1 : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J]
    (D D' : J ⥤ CommRingCat.{0}) (α : D ⟶ D') (c : Cocone D) (hc : IsColimit c)
    (c' : Cocone D') (hc' : IsColimit c') (g : c.pt ⟶ c'.pt)
    (hg : ∀ j, c.ι.app j ≫ g = α.app j ≫ c'.ι.app j)
    (hα : ∀ j, RE q i (α.app j)) (hq : ∀ j, IsUnit (q : D.obj j)) : RE q i g := by
  intro n
  change Function.Bijective (P q i n g)
  have hqc : IsUnit (q : c.pt) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact isUnit_of_hom (c.ι.app j) (hq j)
  have hqc' : IsUnit (q : c'.pt) := isUnit_of_hom g hqc
  have hqD' : ∀ j, IsUnit (q : D'.obj j) := fun j => isUnit_of_hom (α.app j) (hq j)
  have comm : ∀ j y, P q i n g (P q i n (c.ι.app j) y) =
      P q i n (c'.ι.app j) (P q i n (α.app j) y) := by
    intro j y
    rw [← pullback_comp₂, ← pullback_comp₂, hg]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, hy⟩ := (b1 q D c hc n i).1 x hqc
    change P q i n (c.ι.app j) y = x at hy
    subst hy
    rw [comm] at hx
    obtain ⟨k, f, hf⟩ := (b1 q D' c' hc' n i).2 j (P q i n (α.app j) y) (hqD' j) hx
    change P q i n (D'.map f) (P q i n (α.app j) y) = 0 at hf
    rw [← pullback_comp₂, ← α.naturality f, pullback_comp₂] at hf
    have h0 : P q i n (D.map f) y = 0 := by
      apply (hα k n).1
      show P q i n (α.app k) (P q i n (D.map f) y) = P q i n (α.app k) 0
      rw [hf, map_zero]
    rw [← c.w f, pullback_comp₂, h0, map_zero]
  · intro z
    obtain ⟨j, y', hy'⟩ := (b1 q D' c' hc' n i).1 z hqc'
    change P q i n (c'.ι.app j) y' = z at hy'
    obtain ⟨y, rfl⟩ := (hα j n).2 y'
    refine ⟨P q i n (c.ι.app j) y, ?_⟩
    rw [← hy']
    exact comm j y

variable {J : Type} [SmallCategory J] {A Y : CommRingCat.{0}} (φ : A ⟶ Y) (D : J ⥤ CommRingCat.{0})
  (t : ∀ j, A ⟶ D.obj j) (ht : ∀ {j k : J} (f : j ⟶ k), t j ≫ D.map f = t k)

private def Dp : J ⥤ CommRingCat.{0} where
  obj j := pushout φ (t j)
  map {j k} f := pushout.desc (pushout.inl φ (t k)) (D.map f ≫ pushout.inr φ (t k)) (by
    rw [← Category.assoc, ht f, pushout.condition])
  map_id j := by
    apply pushout.hom_ext <;> simp
  map_comp {j k l} f g := by
    apply pushout.hom_ext
    · erw [pushout.inl_desc, ← Category.assoc, pushout.inl_desc, pushout.inl_desc]
    · erw [pushout.inr_desc, ← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        D.map_comp, Category.assoc]

private theorem inl_Dp {j k : J} (f : j ⟶ k) :
    pushout.inl φ (t j) ≫ (Dp φ D t ht).map f = pushout.inl φ (t k) :=
  pushout.inl_desc _ _ _

private theorem inr_Dp {j k : J} (f : j ⟶ k) :
    pushout.inr φ (t j) ≫ (Dp φ D t ht).map f = D.map f ≫ pushout.inr φ (t k) :=
  pushout.inr_desc _ _ _

private def toDp : D ⟶ Dp φ D t ht where
  app j := pushout.inr φ (t j)
  naturality j k f := (inr_Dp φ D t ht f).symm

variable (c : Cocone D) (hc : IsColimit c) {Y' : CommRingCat.{0}} (w : Y ⟶ Y') (φ' : c.pt ⟶ Y')
  (cc : A ⟶ c.pt) (hcc : ∀ j, t j ≫ c.ι.app j = cc) (hp : IsPushout φ cc w φ')

private def cocDp : Cocone (Dp φ D t ht) where
  pt := Y'
  ι :=
    { app j := pushout.desc w (c.ι.app j ≫ φ') (by
        rw [← Category.assoc, hcc, hp.w])
      naturality j k f := by
        refine pushout.hom_ext ?_ ?_
        · erw [← Category.assoc, inl_Dp, pushout.inl_desc, ← Category.assoc, pushout.inl_desc,
            Category.comp_id]
        · erw [← Category.assoc, inr_Dp, Category.assoc, pushout.inr_desc, ← Category.assoc, c.w f,
            ← Category.assoc, pushout.inr_desc, Category.comp_id] }

private theorem inl_coc (j : J) :
    pushout.inl φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = w :=
  pushout.inl_desc _ _ _

private theorem inr_coc (j : J) :
    pushout.inr φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = c.ι.app j ≫ φ' :=
  pushout.inr_desc _ _ _

private theorem inl_indep [IsFiltered J] (e : Cocone (Dp φ D t ht)) (j k : J) :
    pushout.inl φ (t j) ≫ e.ι.app j = pushout.inl φ (t k) ≫ e.ι.app k := by
  rw [← e.w (IsFiltered.leftToMax j k), ← e.w (IsFiltered.rightToMax j k)]
  erw [← Category.assoc, inl_Dp, ← Category.assoc, inl_Dp]

private def resCoc (e : Cocone (Dp φ D t ht)) : Cocone D where
  pt := e.pt
  ι :=
    { app j := pushout.inr φ (t j) ≫ e.ι.app j
      naturality j k f := by
        erw [Category.comp_id, ← e.w f, ← Category.assoc, ← Category.assoc, inr_Dp]
        simp
        rfl }

private def isColDp [IsFiltered J] : IsColimit (cocDp φ D t ht c w φ' cc hcc hp) :=
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  { desc := fun e => hp.desc (pushout.inl φ (t j0) ≫ e.ι.app j0)
      (hc.desc (resCoc φ D t ht e)) (by
        erw [← hcc j0, Category.assoc, hc.fac, ← Category.assoc, pushout.condition, Category.assoc])
    fac := fun e j => by
      refine pushout.hom_ext ?_ ?_
      · erw [← Category.assoc, inl_coc, hp.inl_desc]
        exact inl_indep φ D t ht e j0 j
      · erw [← Category.assoc, inr_coc, Category.assoc, hp.inr_desc, hc.fac]
        rfl
    uniq := fun e m hm => by
      refine hp.hom_ext ?_ ?_
      · erw [hp.inl_desc, ← hm j0, ← Category.assoc, inl_coc]
        rfl
      · erw [hp.inr_desc]
        refine hc.hom_ext fun j => ?_
        erw [hc.fac, ← Category.assoc, ← inr_coc φ D t ht c w φ' cc hcc hp j, Category.assoc, hm j]
        rfl }

end UpperTheory.DirectSumIndependence

theorem UpperTheory.cohomology_continuity_filtered_colimit_rings :
    LateralTheory.E.t_E3Cut.Limit := by
  intro hyp q _ i A Y φ hq hEt C c hc Y' w φ' hp
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hc
  have ht : ∀ {j k : J} (f : j ⟶ k), t.app j ≫ D.map f = t.app k := by
    intro j k f
    rw [← t.naturality f]
    simp
  exact UpperTheory.DirectSumIndependence.chase hyp.2.2.2.2.2.2.1 q i D
    (UpperTheory.DirectSumIndependence.Dp φ D (fun j => t.app j) ht)
    (UpperTheory.DirectSumIndependence.toDp φ D (fun j => t.app j) ht) (Cocone.mk C s) hs
    (UpperTheory.DirectSumIndependence.cocDp φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp)
    (UpperTheory.DirectSumIndependence.isColDp φ D (fun j => t.app j) ht (Cocone.mk C s) hs w φ' c
      (fun j => (hts j).2) hp)
    φ'
    (fun j => (UpperTheory.DirectSumIndependence.inr_coc φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp j).symm)
    (fun j => hEt _ _ (hts j).1 _ _ _ (IsPushout.of_hasPushout _ _))
    (fun j => UpperTheory.DirectSumIndependence.isUnit_of_hom (t.app j) hq)
end
end

namespace UpperTheory.Et.E3

theorem n2 : LateralTheory.E.AlgResPropsPf.Comp := @LateralTheory.E.CompPf.Comp_of

theorem n3 : LateralTheory.E.AlgResPropsPf.Push := @LateralTheory.E.PushPf.Push_of

theorem n4 : LateralTheory.E.AlgResPropsPf.EtAlg := @LateralTheory.E.EtAlgPf.EtAlg_of

theorem n1 : LateralTheory.E.t_E3Cut.AlgResProps := by
  exact LateralTheory.E.AlgResPropsPf.AlgResProps_of n2 n3 n4

theorem n7 : LateralTheory.E.t_E3Cut.Limit := @UpperTheory.cohomology_continuity_filtered_colimit_rings

theorem n6 : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := @LateralTheory.E.t_E3Cut.etale_base_change_polynomial_induction_of_limit @n7

theorem n5 : LateralTheory.E.t_E3Cut.Base := @LateralTheory.E.BasePf.Base_of @n6

theorem n12 : LateralTheory.E.TruncationPieces.Piece := @LateralTheory.E.SimplicialPieceDiscrete.Piece_of

theorem n15 : LateralTheory.E.FiltPf.TowerFin := @LateralTheory.E.FiltPf.TowerFin_of

theorem n17 : LateralTheory.E.TruncPf.TruncBij := @LateralTheory.E.TruncPf.TruncBij_of

theorem n16 : LateralTheory.E.FiltPf.Trunc := @LateralTheory.E.TruncationInclusionIso.Trunc_of @n17

theorem n14 : LateralTheory.E.FiltPf.Tower := @LateralTheory.E.FiltPf.tower_of @n15 @n16

theorem n13 : LateralTheory.E.TruncationPieces.Filt := @LateralTheory.E.TruncationPieces.Filt_of_tower @n14

theorem n11 : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := @LateralTheory.E.TruncationPieces.etale_relK_single_degree_pieces_of_piece_and_filtration @n12 @n13

theorem n19 : LateralTheory.E.CechSqPf.IntegralSurjectiveRingCechAugmentationEtaleEqv := @LateralTheory.E.CechSqPf.integral_surjective_ring_cech_augmentation_etale_eqv

theorem n20 : LateralTheory.E.CechSqPf.BaseChange := @LateralTheory.E.CechSqPf.BaseChange_of

theorem n21 : LateralTheory.E.CechSqPf.LevelPush := @LateralTheory.E.CechSqPf.LevelPush_of

theorem n22 : LateralTheory.E.CechSqPf.LevelP := @LateralTheory.E.CechSqPf.cechConerve_levelwise

theorem n23 : LateralTheory.E.CechSqPf.Level0 := by
  exact LateralTheory.E.CechSqPf.Level0_of n21

theorem n18 : LateralTheory.E.DescIntPf.CechSq := by
  exact LateralTheory.E.CechSqPf.CechSq_of n19 n20 n21 n22 n23

theorem n10 : LateralTheory.E.StalkCut.DescInt := @LateralTheory.E.DescIntPf.DescInt_of @n11 @n18

theorem n27 : LateralTheory.E.CoprodPf.FreeCoprod := @LateralTheory.E.FreeCoprodPf.FreeCoprod_of

theorem n28 : LateralTheory.E.CoprodPf.ChainsDiscCoprod := @LateralTheory.E.ChainsDiscCoprodPf.ChainsDiscCoprod_of

theorem n29 : LateralTheory.E.CoprodPf.HKCoprod := @LateralTheory.E.HKCoprodPf.HKCoprod_of

theorem n26 : LateralTheory.E.t_E3Cut.Coprod := @LateralTheory.E.CoprodPf.Coprod_of @n27 @n28 @n29

theorem n31 : LateralTheory.E.PointwisePf.PushColim := @LateralTheory.E.PointwisePf.pushColim

theorem n30 : LateralTheory.E.KillCokPf.Pointwise := by
  exact LateralTheory.E.PointwisePf.Pointwise_of_pushColim n31

theorem n32 : LateralTheory.E.KillCokPf.Glue.PushGlue := @LateralTheory.E.PushGluePf.PushGlue_of @n26

theorem n25 : LateralTheory.E.DescLocPf.Fine.KillCok := @LateralTheory.E.KillCokPf.Glue.KillCok_of' @n26 @n30 @n32

theorem n35 : LateralTheory.E.RelDescPf.RelEqvInj := @LateralTheory.E.RelEqvInjPf.RelEqvInj_of

theorem n36 : LateralTheory.E.RelDescPf.CechEqv := @LateralTheory.E.RelDescPf.cechEqv

theorem n39 : LateralTheory.E.FiltrationLevelBase.Step0 := @UpperTheory.Cb.simplicial_chains_degree_zero_injective @n26

theorem n38 : LateralTheory.E.FiltrationLevelInjectivity.Filt := @LateralTheory.E.FiltrationLevelBase.Filt_of @n39

theorem n40 : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := @LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of

theorem n37 : LateralTheory.E.RelDescPf.LevelInj := @LateralTheory.E.FiltrationLevelInjectivity.LevelInj_of @n38 @n40

theorem n34 : LateralTheory.E.TruncationKernel.RelDesc := @LateralTheory.E.RelDescPf.relDesc_of @n35 @n36 @n37

theorem n33 : LateralTheory.E.DescLocPf.Fine.TruncCok := @LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of @n34

theorem n41 : LateralTheory.E.DescLocPf.KerLoc := @LateralTheory.E.KernelLocalization.KerLoc_of @n26 @n34

theorem n24 : LateralTheory.E.StalkCut.DescLoc := @LateralTheory.E.DescLocPf.Fine.DescLoc_of' @n25 @n33 @n41

theorem n9 : LateralTheory.E.t_E3Cut.Stalk := @LateralTheory.E.StalkCut.goal_of @n10 @n24

theorem n47 : LateralTheory.EWeil.AbsorbPf.Model := @LateralTheory.EWeil.AbsorbPf3.etaleAlgebras_have_small_model_set

theorem n48 : LateralTheory.EWeil.AbsorbPf.Pair := @LateralTheory.EWeil.AbsorbPf2.etaleNeighborhoods_have_common_refinement

theorem n49 : LateralTheory.EWeil.AbsorbPf.Coeq := @LateralTheory.EWeil.AbsorbPf4.etaleNeighborhoods_equalize_parallel_maps

theorem n46 : LateralTheory.E.ColimPf.Absorb := @LateralTheory.EWeil.AbsorbPf.Absorb_of @n47 @n48 @n49

theorem n52 : LateralTheory.E.SpreadPf.Cut.EtStage := @LateralTheory.E.EtStagePf.EtStage_of

theorem n51 : LateralTheory.E.DescendPf.Spread := by
  exact LateralTheory.E.SpreadPf.Main.Spread_of n52

theorem n50 : LateralTheory.E.ColimPf.Descend := @LateralTheory.E.DescendPf.Descend_of @n51

theorem n45 : LateralTheory.E.SHLocPf.Colim := @LateralTheory.E.ColimPf.Main.Colim_of @n46 @n50

theorem n44 : LateralTheory.E.SHLocPf.Build := @LateralTheory.E.SHLocPf.build_of @n45

theorem n53 : LateralTheory.E.SHLocPf.Lift := @LateralTheory.E.SHLocPf.etaleClosed_point_lifts_simple_roots_monic

theorem n43 : LateralTheory.E.SHExistsPf.SHLoc := @LateralTheory.E.SHLocPf.SHLoc_of @n44 @n53

theorem n54 : LateralTheory.E.SHExistsPf.LocAt := @LateralTheory.E.LocAtPf.LocAt_of

theorem n55 : LateralTheory.E.SHExistsPf.Comp := @LateralTheory.E.CompositionGoal.goal_of

theorem n42 : LateralTheory.E.t_E3Cut.SHExists := by
  exact LateralTheory.E.SHExistsPf.SHExists_of n43 n54 n55

theorem n56 : LateralTheory.E.t_E3Cut.IEComp := @LateralTheory.E.TruncationIsoComparison.IEComp_of

theorem n59 : LateralTheory.E.SHSectionPf.SHAlgSec := @LateralTheory.E.SHAlgSecPf.SHAlgSec_of

theorem n60 : LateralTheory.E.SHSectionPf.EtAffNbhd := @LateralTheory.E.EtAffNbhdPf.EtAffNbhd_of

theorem n58 : LateralTheory.E.t_E3Cut.SHSection := @LateralTheory.E.SHSectionPf.SHSection_of @n59 @n60

theorem n62 : LateralTheory.E.SHEqvPf.SecPre := @LateralTheory.E.SecPrePf.SecPre_of @n58

theorem n63 : LateralTheory.E.SHEqvPf.TwFBij := @LateralTheory.E.TwFBijPf.TwFBij_of

theorem n61 : LateralTheory.E.SHEqvPf.SecBij := @LateralTheory.E.SHEqvPf.SecBij_of @n62 @n63

theorem n57 : LateralTheory.E.t_E3Cut.SHEqv := @LateralTheory.E.SHEqvPf.SHEqv_of_secBij @n58 @n61

theorem n65 : LateralTheory.E.t_E3Cut.AICExt := @LateralTheory.E.AICExtPf.AICExt_of

theorem n67 : LateralTheory.E.DomCoverPf.IdemCover := @LateralTheory.E.IdemCoverPf.IdemCover_of

theorem n66 : LateralTheory.E.t_E3Cut.DomCover := @LateralTheory.E.DomCoverPf.DomCover_of @n67

theorem n68 : LateralTheory.E.t_E3Cut.LocIE := @LateralTheory.E.LocIEPf.LocIE_of

theorem n71 : LateralTheory.E.t_E3Cut.HensInt := @LateralTheory.E.HensIntPf.HensInt_of

theorem n70 : LateralTheory.E.t_E3Cut.IntClos := @LateralTheory.E.IntClosPf.IntClos_of @n71

theorem n73 : LateralTheory.E.SHTensorPf.LocTensor := @LateralTheory.E.LocTensorPf.LocTensor_of

theorem n74 : LateralTheory.E.SHTensorPf.SepTensor := @LateralTheory.E.SepTensorPf.SepTensor_of

theorem n72 : LateralTheory.E.t_E3Cut.SHTensor := by
  exact LateralTheory.E.SHTensorPf.SHTensor_of n71 n73 n74

theorem n75 : LateralTheory.E.t_E3Cut.AICSH := @LateralTheory.E.t_E3Cut.AICSH_of

theorem n76 : LateralTheory.E.ULAStalkPf.IECob := @LateralTheory.E.IECobPf.IECob_of

theorem n77 : LateralTheory.E.ULAStalkPf.FracAIC := @LateralTheory.E.FracAICPf.FracAIC_of

theorem n69 : LateralTheory.E.t_E3Cut.ULAStalk := by
  exact LateralTheory.E.ULAStalkPf.ULAStalk_of' n70 n72 n75 n57 n6 n76 n77

theorem n64 : LateralTheory.E.t_E3Cut.ULA := @LateralTheory.E.ULAPf.ULA_of @n9 @n1 @n65 @n66 @n68 @n69

theorem n8 : LateralTheory.E.t_E3Cut.Step := by
  exact UpperTheory.Cb.strictHenselization_stalk_equiv_of_colimit_presentation n9 n7 n42 n56 n1 n57 n64

theorem n81 : LateralTheory.E.CechSigma_xy1Pf_Lev.CechYoneda := @LateralTheory.E.CechSigma_xy1Pf_Yo.cechYoneda

theorem n82 : LateralTheory.E.CechSigma_xy1Pf_Lev.SchemeLevel := @UpperTheory.Cb.cechLevel_iso_sigma_intersections_of_coprod @n26

theorem n80 : LateralTheory.E.ZariskiLocalCech.CechSigma := by
  exact LateralTheory.E.CechSigma_xy1Pf_Lev.CechSigma_of n81 n82

theorem n79 : LateralTheory.E.t_E3Cut.ZarLocal := @LateralTheory.E.ZariskiLocalCech.ZarLocal_of @n26 @n80

theorem n83 : LateralTheory.E.GlobalPf.Affine := @LateralTheory.E.AffinePf.Affine_of

theorem n84 : LateralTheory.E.GlobalPf.LocEt := @LateralTheory.E.LocEtPf.LocEt_of

theorem n78 : LateralTheory.E.t_E3Cut.Global := by
  exact LateralTheory.E.GlobalPf.Global_of n79 n83 n84


open CategoryTheory LateralTheory.E.t_E3Cut in
theorem main (H : LateralTheory.E.t_E3Cut.Hyp) : GlobalTheory.EtC.E3 := by
  intro q _ T _ _ _ hAIC hq X p _ i
  have hAR : LateralTheory.E.t_E3Cut.AlgRes (CommRingCat.ofHom (algebraMap T (FractionRing T))) := by
    intro Q hQ c
    obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors T) c
    have hb : algebraMap T (FractionRing T) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    refine ⟨Polynomial.C (b : T) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
    · intro hmem
      apply hQ.ne_top
      apply Ideal.eq_top_of_isUnit_mem _ _ (IsUnit.mk0 _ hb)
      simpa using hmem
    · have h0 : Polynomial.eval₂ (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap T (FractionRing T)))) c
          (Polynomial.C (b : T) * Polynomial.X - Polynomial.C a) = 0 := by
        simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [mul_comm, hc, sub_self]
      rw [h0]
      exact Q.zero_mem
  have hgood : ∀ n : ℕ, LateralTheory.E.t_E3Cut.Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T)))
      (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T)) := by
    intro n
    induction n with
    | zero =>
      refine LateralTheory.E.t_E3Cut.Good.of_equiv (n5 H q i T hAIC hq)
        (MvPolynomial.isEmptyAlgEquiv T (Fin 0)).symm.toRingEquiv _ ?_
      ext x
      simp
    | succ n ih =>
      refine LateralTheory.E.t_E3Cut.Good.of_equiv (n8 H q i _ _ hq hAR ih)
        (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (MvPolynomial.finSuccEquiv T n).symm (algebraMap T _ x) = algebraMap T (MvPolynomial (Fin (n + 1)) T) x
      exact AlgEquiv.commutes _ x
  exact n78 H q i _ hgood p

end UpperTheory.Et.E3
