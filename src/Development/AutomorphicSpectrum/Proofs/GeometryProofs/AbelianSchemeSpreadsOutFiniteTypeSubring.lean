module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedFibersStableUnderSpecialization
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebra

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOpenGeometricallyConnectedFibers
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizes
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralOfClosedFibre
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_comp_residue_eq (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (K : Type) [Field K] (φ : A →+* K) :
    ∃ ψ : IsLocalRing.ResidueField A →+* K, ψ.comp (IsLocalRing.residue A) = φ := by
  have hm : (RingHom.ker φ).IsMaximal := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    exact IsArtinianRing.isMaximal_of_isPrime _
  have he : RingHom.ker φ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  have H : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := fun a ha => by
    rw [← he] at ha
    exact (RingHom.mem_ker).1 ha
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ H,
    RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ H⟩

theorem geometricallyIntegral_of_closedFibre (A : Type) [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A)
    (h : GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A)))) :
    GeometricallyIntegral p := by
  constructor
  intro K _ y Z fst snd hpb
  obtain ⟨ψ, hψ⟩ := exists_comp_residue_eq A K (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A) = y := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom]
    exact Spec.map_preimage y
  have hw : fst ≫ p = (snd ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ spMap (IsLocalRing.residue A) := by
    rw [Category.assoc, hy]
    exact hpb.w
  have hbig : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw ≫
      pullback.fst p (spMap (IsLocalRing.residue A))) snd p
      (Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A)) := by
    rw [pullback.lift_fst, hy]
    exact hpb
  have hsq : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw) snd
      (pullback.snd p (spMap (IsLocalRing.residue A))) (Spec.map (CommRingCat.ofHom ψ)) :=
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  exact h.geometrically_isIntegral (Spec.map (CommRingCat.ofHom ψ)) _ snd hsq

theorem isIso_appTop_of_artinian : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (X : Scheme.{0}) (p : X ⟶ Sp A), Flat p → IsProper p →
    GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) → IsIso p.appTop := by
  intro A _ _ _ X p hflat hprop hgi
  haveI : IsAffine (Sp A) := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  haveI : IsLocallyNoetherian (Sp A) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
  haveI := hflat
  haveI := hprop
  haveI : GeometricallyIntegral p := geometricallyIntegral_of_closedFibre A X p hgi
  exact GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine p

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

open IsLocalRing GlobalTheory.ProperFunctions

theorem isClosed_germ_ne_zero (X : Scheme.{0}) (f : Γ(X, ⊤)) :
    IsClosed {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hx
  have hx' : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ ⊤ x trivial 0 := by
    rw [hx, map_zero]
  obtain ⟨W, hxW, iU, iV, h⟩ := TopCat.Presheaf.germ_eq X.presheaf (U := ⊤) (V := ⊤) x trivial trivial f 0 hx'
  refine Filter.mem_of_superset (W.2.mem_nhds hxW) fun y hy ↦ ?_
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rw [← X.presheaf.germ_res_apply iU y hy, h, map_zero, map_zero]

theorem germ_mem_maximalIdeal {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (x : X) (hx : p x = closedPoint A) {a : A} (ha : a ∈ maximalIdeal A) :
    X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) ∈
      maximalIdeal (X.presheaf.stalk x) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := (X.mem_basicOpen (U := ⊤) _ x trivial).mpr hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1
  have h3 : p x ∈ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact h3 ha

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{0}} (p : X ⟶ Sp A) [UniversallyClosed p] [LocallyOfFiniteType p]
    (f : Γ(X, ⊤))
    (h : ∀ (n : ℕ) (U : X.affineOpens), X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f ∈
      (((maximalIdeal A) ^ (n + 1)).map (Scheme.ΓSpecIso (.of A)).inv.hom).map
        (p.appLE ⊤ U.1 (le_preimage_top p _)).hom) : f = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hf
  have hne : ∃ z : X, X.presheaf.germ ⊤ z trivial f ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hf (TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x _ ↦ ?_)
    rw [map_zero]
    exact hall x
  obtain ⟨z, hz⟩ := hne
  have hcl := p.isClosedMap _ (isClosed_germ_ne_zero X f)
  have hmem : closedPoint A ∈ p '' {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} :=
    (specializes_closedPoint (p z)).mem_closed hcl ⟨z, hz, rfl⟩
  obtain ⟨x, hxZ, hx⟩ := hmem
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine hxZ ?_
  have hθ : ∀ a : A, X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    intro a
    have e1 : p.appLE ⊤ U (le_preimage_top p _) =
        p.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := rfl
    rw [e1, CommRingCat.comp_apply]
    exact X.presheaf.germ_res_apply _ x hxU _
  have hpow : ∀ n : ℕ, X.presheaf.germ ⊤ x trivial f ∈
      maximalIdeal (X.presheaf.stalk x) ^ (n + 1) := by
    intro n
    have h1 := Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom (h n ⟨U, hU⟩)
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_pow] at h1
    have h2 : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ U x hxU
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) :=
      (X.presheaf.germ_res_apply _ x hxU f).symm
    rw [h2]
    refine Ideal.pow_right_mono ?_ _ h1
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    change X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) ∈ _
    rw [hθ]
    exact germ_mem_maximalIdeal p x hx ha
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x))
    Ideal.IsPrime.ne_top'
  have : X.presheaf.germ ⊤ x trivial f ∈ (⊥ : Ideal (X.presheaf.stalk x)) := by
    rw [← hbot, Ideal.mem_iInf]
    intro i
    exact Ideal.pow_le_pow_right (Nat.le_succ i) (hpow i)
  simpa using this

theorem geometricallyIntegral_fibre {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A)))) :
    GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B))) := by
  let φ : ResidueField A →+* ResidueField B := ResidueField.map π
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨residue A a, ResidueField.map_residue π a⟩
  have : IsIso (CommRingCat.ofHom φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have : IsIso (spMap φ) := inferInstanceAs (IsIso (Spec.map _))
  have e1 : φ.comp (residue A) = (residue B).comp π := by
    ext a
    exact ResidueField.map_residue π a
  have hw : spMap (residue B) ≫ spMap π = spMap φ ≫ spMap (residue A) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  have H := (IsPullback.of_hasPullback (pullback.snd p (spMap π)) (spMap (residue B))).paste_horiz
    (IsPullback.of_hasPullback p (spMap π))
  rw [hw] at H
  have R := IsPullback.of_hasPullback p (spMap (residue A))
  have w : (pullback.fst (pullback.snd p (spMap π)) (spMap (residue B)) ≫
      pullback.fst p (spMap π)) ≫ p =
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)) ≫ spMap φ) ≫
        spMap (residue A) := H.w.trans (Category.assoc _ _ _).symm
  have H2 : IsPullback (R.lift _ _ w) (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)))
      (pullback.snd p (spMap (residue A))) (spMap φ) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (spMap (residue A))) (v₁₃ := p)
      (h₂₂ := spMap (residue A)) ?_ (R.lift_snd _ _ w) R
    rw [R.lift_fst]
    exact H
  exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H2 hG

theorem appTop_fst_eq_zero {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [IsArtinianRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π]
    {X : Scheme.{0}} (p : X ⟶ Sp A) (e : Sp A ⟶ X) (he : e ≫ p = 𝟙 _) (hF : Flat p)
    (hP : IsProper p) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A))))
    (f : Γ(X, ⊤)) (hf : e.appTop f = 0) : (pullback.fst p (spMap π)).appTop f = 0 := by
  have H := IsPullback.of_hasPullback p (spMap π)
  have hqF : Flat (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hF
  have hqP : IsProper (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hP
  have hiso := isIso_appTop_of_artinian B _ (pullback.snd p (spMap π)) hqF hqP
    (geometricallyIntegral_fibre π hπ p hG)
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (pullback.snd p (spMap π)).appTop).2
    ((pullback.fst p (spMap π)).appTop f)
  let e' : Sp B ⟶ pullback p (spMap π) :=
    pullback.lift (spMap π ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e'.appTop ((pullback.snd p (spMap π)).appTop c) = c := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd,
      Scheme.Hom.id_appTop]
    rfl
  have h2 : e'.appTop ((pullback.fst p (spMap π)).appTop f) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_zero]
  have hc0 : c = 0 := by
    rw [hc, h2] at h1
    exact h1.symm
  rw [← hc, hc0, map_zero]

theorem ker_appTop_le {A : Type} [CommRing A] (I : Ideal A) :
    RingHom.ker (spMap (Ideal.Quotient.mk I)).appTop.hom ≤
      I.map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  intro r hr
  obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (.of A)).inv a = r :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 r
  refine Ideal.mem_map_of_mem _ ?_
  have h1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) a)
  simp only [CommRingCat.comp_apply] at h1
  have h2 : (Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a) = 0 :=
    h1.trans hr
  have h3 : Ideal.Quotient.mk I a = 0 :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1
      (h2.trans (map_zero _).symm)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

theorem quotient_pow_facts (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    ∃ (_ : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)))
      (_ : IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1))),
      IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  have hle : maximalIdeal A ^ (n + 1) ≤ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hI : maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h ↦
    Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hL : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hH : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).mpr hna
    have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)
    have := (ha.pow (n + 1))
    rw [h0] at this
    exact not_isUnit_zero this
  have hK : Ring.KrullDimLE 0 (A ⧸ maximalIdeal A ^ (n + 1)) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ ↦ ?_
    have : Q = maximalIdeal _ := by
      refine le_antisymm (le_maximalIdeal hQ.ne_top) fun b hb ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      have ham : a ∈ maximalIdeal A := by
        rw [mem_maximalIdeal] at hb ⊢
        exact fun hu ↦ hb (hu.map _)
      have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) ∈ Q := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)]
        exact Q.zero_mem
      exact hQ.mem_of_pow_mem _ h0
    rw [this]
    exact maximalIdeal.isMaximal _
  exact ⟨hL, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero, hH⟩

theorem isIso_appTop_of_closedFibre : ∀ (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A) (e : Sp A ⟶ X), e ≫ p = 𝟙 _ → Flat p →
    IsProper p → GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) →
    IsIso p.appTop := by
  intro A _ _ _ X p e he hF hP hG
  have h1 : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h2 : Function.Injective e.appTop := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    refine eq_zero_of_mem_pow p f fun n U ↦ ?_
    obtain ⟨_, _, _⟩ := quotient_pow_facts A n
    have h0 := appTop_fst_eq_zero (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
      Ideal.Quotient.mk_surjective p e he hF hP hG f hf
    have h3 := mem_map_ker_of_app_eq_zero
      (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))) U.2
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f) (by
        rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        erw [h0]
        exact map_zero _)
    exact Ideal.map_mono (ker_appTop_le _) h3
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ h2
  exact ⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfIsFieldGlobalFunctions
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem connectedSpace_of_isField_globalFunctions (Z : Scheme.{0}) (h : IsField Γ(Z, ⊤)) :
    ConnectedSpace Z := by
  have hne : Nonempty Z := by
    by_contra hZ
    have hb : (⊤ : Z.Opens) = ⊥ := by
      ext x
      exact (hZ ⟨x⟩).elim
    have hs : Subsingleton Γ(Z, ⊤) := by
      rw [hb]
      infer_instance
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hp : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z U hU
    by_cases h0 : e = 0
    · left
      rw [← hUe, h0, Z.basicOpen_zero]
      rfl
    · right
      obtain ⟨b, hb⟩ := h.mul_inv_cancel h0
      have h1 : e = 1 := by
        calc e = e * e * b := by rw [_root_.mul_assoc, hb, _root_.mul_one]
          _ = e * b := by rw [he]
          _ = 1 := hb
      rw [← hUe, h1, Z.basicOpen_of_isUnit isUnit_one]
      rfl
  exact { toPreconnectedSpace := hp, toNonempty := hne }

theorem geometricallyConnected_of_isIso_appTop :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), QuasiCompact p → QuasiSeparated p →
      IsIso p.appTop → GeometricallyConnected p := by
  intro K _ X p _ _ _
  refine ⟨fun L _ y Z a q H => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    rw [Flat.SpecMap_iff]
    algebraize [φ.hom]
    exact inferInstanceAs (Module.Flat K L)
  have hq : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  let e₁ : Γ(Spec (.of L), ⊤) ≃+* Γ(Z, ⊤) := (asIso q.appTop).commRingCatIsoToRingEquiv
  let e₂ : Γ(Spec (.of L), ⊤) ≃+* L := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have hL : IsField Γ(Spec (.of L), ⊤) := MulEquiv.isField (Field.toIsField L) e₂.toMulEquiv
  exact connectedSpace_of_isField_globalFunctions Z (MulEquiv.isField hL e₁.symm.toMulEquiv)

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizes
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_isPullback_left {P Q X S T U : Scheme.{0}} {t : P ⟶ X} {v : P ⟶ U} {p : X ⟶ S}
    {g : U ⟶ T} {f : T ⟶ S} {t' : Q ⟶ X} {v' : Q ⟶ T}
    (h : IsPullback t v p (g ≫ f)) (h' : IsPullback t' v' p f) :
    ∃ u : P ⟶ Q, IsPullback u v v' g := by
  refine ⟨h'.lift t (v ≫ g) (by simpa using h.w), ?_⟩
  refine IsPullback.of_right (h₁₂ := t') (h₂₂ := f) (v₁₃ := p) ?_ (by simp) h'
  simpa using h

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem geometricallyConnected_of_local {k A E L K : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Field E] [Field L] [Field K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (φ : k →+* A) (a : k →+* E)
    (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp φ)
    (hE : GeometricallyConnected (pullback.snd p (spMap a)))
    (j : A →+* L) (hj : j.Flat) (c : k →+* K) (d : K →+* L) (hd : d.comp c = j.comp φ) :
    GeometricallyConnected (pullback.snd p (spMap c)) := by
  have hPA : IsPullback (pullback.fst p (spMap φ)) (pullback.snd p (spMap φ)) p (spMap φ) :=
    .of_hasPullback _ _
  haveI : Smooth (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : IsProper (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : Flat (pullback.snd p (spMap φ)) := inferInstance
  let eA : Sp A ⟶ pullback p (spMap φ) :=
    pullback.lift (spMap φ ≫ e) (𝟙 _) (by rw [Category.assoc, hs]; simp)
  have heA : eA ≫ pullback.snd p (spMap φ) = 𝟙 _ := pullback.lift_snd _ _ _

  have hW : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)) := .of_hasPullback _ _
  have hbot : spMap (IsLocalRing.residue A) ≫ spMap φ = spMap b ≫ spMap a := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hb]
  have hW' := hW.paste_horiz hPA
  rw [hbot] at hW'
  obtain ⟨u, hu⟩ := exists_isPullback_left hW' (.of_hasPullback p (spMap a))
  haveI : Smooth (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hW ‹_›
  haveI : GeometricallyConnected
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hu hE
  have hGI : GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    GlobalTheory.geometricallyIntegral_of_smooth _
  haveI hA : IsIso (pullback.snd p (spMap φ)).appTop :=
    isIso_appTop_of_closedFibre A _ _ eA heA inferInstance inferInstance hGI

  have hL : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd p (spMap φ)) (spMap j) := .of_hasPullback _ _
  haveI : Flat (spMap j) := Flat.SpecMap_iff.2 hj
  haveI hL1 : IsIso (pullback.snd (pullback.snd p (spMap φ)) (spMap j)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback hL
  have hbot' : spMap j ≫ spMap φ = spMap d ≫ spMap c := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hd]
  have hL' := hL.paste_horiz hPA
  rw [hbot'] at hL'
  obtain ⟨w, hw⟩ := exists_isPullback_left hL' (.of_hasPullback p (spMap c))
  haveI : Flat (spMap d) := Flat.SpecMap_iff.2 (by
    algebraize [d]
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : Surjective (spMap d) := by
    refine ⟨fun x => ?_⟩
    have y : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  haveI hK : IsIso (pullback.snd p (spMap c)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective hw
  exact geometricallyConnected_of_isIso_appTop K _ _ inferInstance inferInstance hK

theorem geometricallyConnected_of_localDomain {k B A E K : Type} [CommRing k] [CommRing B]
    [IsDomain B] [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field E] [Field K]
    [Algebra B K] [IsFractionRing B K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (q : k →+* B) (ψ : B →+* A)
    (hψ : Function.Injective ψ) (a : k →+* E) (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp (ψ.comp q))
    (hE : GeometricallyConnected (pullback.snd p (spMap a))) :
    GeometricallyConnected (pullback.snd p (spMap ((algebraMap B K).comp q))) := by
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp ψ) :=
    (IsFractionRing.injective A (FractionRing A)).comp hψ
  refine geometricallyConnected_of_local (A := A) (E := E) (L := FractionRing A) X p e hs (ψ.comp q)
    a b hb hE (algebraMap A (FractionRing A)) (RingHom.flat_algebraMap_iff.2 inferInstance) _
    (IsFractionRing.lift hinj) ?_
  ext r
  simp only [RingHom.comp_apply]
  exact IsFractionRing.lift_algebraMap hinj (q r)

theorem stableUnderGeneralization_geometricallyConnected_fibre :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
      (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p →
      StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ X p e hs _ _ x y hyx hx
  have hle : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).2 hyx
  have hq : Function.Surjective (Ideal.Quotient.mk y.asIdeal) := Ideal.Quotient.mk_surjective
  obtain ⟨Q, hQ, hcomap⟩ : ∃ Q : Ideal (k ⧸ y.asIdeal), ∃ _ : Q.IsPrime,
      x.asIdeal = Q.comap (Ideal.Quotient.mk y.asIdeal) := by
    refine ⟨x.asIdeal.map (Ideal.Quotient.mk y.asIdeal),
      Ideal.map_isPrime_of_surjective hq (by rw [Ideal.mk_ker]; exact hle), ?_⟩
    rw [Ideal.comap_map_of_surjective _ hq, eq_comm, sup_eq_left]
    refine le_trans ?_ hle
    rw [show Ideal.comap (Ideal.Quotient.mk y.asIdeal) ⊥ = RingHom.ker (Ideal.Quotient.mk y.asIdeal)
      from rfl, Ideal.mk_ker]
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
  have := geometricallyConnected_of_localDomain (K := y.asIdeal.ResidueField) X p e hs
    (Ideal.Quotient.mk y.asIdeal) (algebraMap (k ⧸ y.asIdeal) (Localization.AtPrime Q))
    (IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors)
    (algebraMap k x.asIdeal.ResidueField)
    (Ideal.ResidueField.map x.asIdeal Q (Ideal.Quotient.mk y.asIdeal) hcomap)
    (by
      ext r
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      rfl) hx
  exact this

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizesStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_connectedness_generalizes : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p → StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre | exact GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpen
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isClosed_of_stable_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] (V : Set X)
    (hg : StableUnderGeneralization V) (hs : StableUnderSpecialization V) : IsClosed V := by
  have key : ∀ x ∈ V, irreducibleComponent x ⊆ V := by
    intro x hx y hy
    have hS : IsGenericPoint (isIrreducible_irreducibleComponent (x := x)).genericPoint
        (irreducibleComponent x) :=
      (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
        isClosed_irreducibleComponent
    exact hs (hS.specializes hy) (hg (hS.specializes mem_irreducibleComponent) hx)
  have hV : V = ⋃₀ {C | C ∈ irreducibleComponents X ∧ C ⊆ V} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, key x hx⟩, mem_irreducibleComponent⟩
    · exact Set.sUnion_subset fun C hC => hC.2
  rw [hV, Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun C hC => hC.1))
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

theorem isOpen_of_stable (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k))
    (hg : StableUnderGeneralization U) (hs : StableUnderSpecialization U) : IsOpen U := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stable_of_noetherian Uᶜ
    (stableUnderGeneralization_compl_iff.mpr hs) (stableUnderSpecialization_compl_iff.mpr hg)

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpenStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stable_under_generalization_specialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k)), StableUnderGeneralization U → StableUnderSpecialization U → IsOpen U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | exact GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOpenGeometricallyConnectedFibers
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isOpen_geometricallyConnected_fibres :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      IsOpen {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hs hp
  have hgen := GlobalTheory.T.geometric_connectedness_generalizes k G.left G.hom (η[G]).left (Over.w η[G]) hs hp
  have hspec := GlobalTheory.T.connected_fibers_stableUnderSpecialization k G hs hp
  exact GlobalTheory.T.isOpen_of_stable_under_generalization_specialization k _ hgen hspec

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOpenGeometricallyConnectedFibersStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.isOpen_geometricallyConnected_fibers : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → IsOpen {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isOpen_geometricallyConnected_fibres | exact GlobalTheory.CompanionTheory.Ar.Approx.isOpen_geometricallyConnected_fibres | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isOpen_geometricallyConnected_fibres <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibers
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibers
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Approx

private theorem eq_of_sp_complex_pts {K : Type} [Field K] (a b : ↥(Sp K)) : a = b := by
  revert a b
  change ∀ a b : PrimeSpectrum K, a = b
  intro a b
  exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)

private theorem nonempty_sp (K : Type) [Field K] : Nonempty ↥(Sp K) := by
  change Nonempty (PrimeSpectrum K)
  infer_instance

theorem connectedSpace_pullback_of_fieldHom {k K K' : Type} [CommRing k] [Field K] [Field K']
    {X : Scheme.{0}} (p : X ⟶ Sp k) (f : k →+* K) (j : K →+* K')
    (h : ConnectedSpace ↥(pullback p (spMap (j.comp f)))) :
    ConnectedSpace ↥(pullback p (spMap f)) := by
  rw [spMap_comp] at h
  let e := pullbackLeftPullbackSndIso p (spMap f) (spMap j)
  let g : pullback p (spMap j ≫ spMap f) ⟶ pullback p (spMap f) :=
    e.inv ≫ pullback.fst (pullback.snd p (spMap f)) (spMap j)
  refine Function.Surjective.connectedSpace (f := ⇑g) ?_ g.continuous
  intro z
  obtain ⟨y'⟩ := nonempty_sp K'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd p (spMap f)) (g := spMap j) z y' (eq_of_sp_complex_pts _ _)
  refine ⟨e.hom w, ?_⟩
  have h2 : e.hom ≫ g = pullback.fst (pullback.snd p (spMap f)) (spMap j) := by
    simp [g, e]
  rw [← hw, ← h2]
  rfl

private theorem connectedSpace_of_iso {A B : Scheme.{0}} (e : A ≅ B) [ConnectedSpace A] :
    ConnectedSpace B := by
  refine Function.Surjective.connectedSpace (f := ⇑e.hom) (fun b => ⟨e.inv b, ?_⟩) e.hom.continuous
  rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

theorem geometricallyConnected_pullback_snd_iff {X S T : Scheme.{0}} (p : X ⟶ S) (g : T ⟶ S) :
    GeometricallyConnected (pullback.snd p g) ↔
      ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ T),
        ConnectedSpace ↥(pullback p (y ≫ g)) := by
  rw [geometricallyConnected_iff]
  constructor
  · intro H K _ y
    haveI : ConnectedSpace ↥(pullback (pullback.snd p g) y) :=
      H y (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    exact connectedSpace_of_iso (pullbackLeftPullbackSndIso p g y)
  · intro H K _ y Z fst snd hpb
    haveI := H K y
    exact connectedSpace_of_iso (hpb.isoPullback ≪≫ pullbackLeftPullbackSndIso p g y).symm

theorem geometricallyConnected_pullback_snd_spMap_iff {k R : Type} [CommRing k] [CommRing R]
    {X : Scheme.{0}} (p : X ⟶ Sp k) (a : k →+* R) :
    GeometricallyConnected (pullback.snd p (spMap a)) ↔
      ∀ (K : Type) [Field K] (φ : R →+* K), ConnectedSpace ↥(pullback p (spMap (φ.comp a))) := by
  rw [geometricallyConnected_pullback_snd_iff]
  constructor
  · intro H K _ φ
    have := H K (spMap φ)
    rwa [← spMap_comp] at this
  · intro H K _ y
    obtain ⟨φ, rfl⟩ : ∃ φ : R →+* K, spMap φ = y :=
      ⟨(Spec.preimage (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))).hom, Spec.map_preimage _⟩
    rw [← spMap_comp]
    exact H K φ

theorem exists_field_amalgam {F K₁ K₂ : Type} [Field F] [Field K₁] [Field K₂]
    (a : F →+* K₁) (b : F →+* K₂) :
    ∃ (L : Type) (_ : Field L) (i : K₁ →+* L) (j : K₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  haveI : Nontrivial (K₁ ⊗[F] K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[F] K₂)
  letI := Ideal.Quotient.field m
  refine ⟨K₁ ⊗[F] K₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  congr 1
  exact (Algebra.TensorProduct.algebraMap_apply x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x)

theorem exists_residueField_lift {k K : Type} [CommRing k] [Field K] (f : k →+* K)
    (x : PrimeSpectrum k) (hx : x.asIdeal = RingHom.ker f) :
    ∃ ψ : x.asIdeal.ResidueField →+* K, ψ.comp (algebraMap k x.asIdeal.ResidueField) = f := by
  have h2 : x.asIdeal.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid K) := by
    intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    refine isUnit_iff_ne_zero.mpr fun h0 => Ideal.mem_primeCompl_iff.mp hr ?_
    rw [hx]
    exact RingHom.mem_ker.mpr h0
  refine ⟨Ideal.ResidueField.lift x.asIdeal f hx.le h2, ?_⟩
  ext r
  exact Ideal.ResidueField.lift_algebraMap x.asIdeal f hx.le h2 r

theorem geometricallyConnected_pullback_snd_spMap_iff_residueField :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k),
      GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔
        ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)),
          GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  intro k V _ _ _ X p
  rw [geometricallyConnected_pullback_snd_spMap_iff]
  constructor
  · rintro H x ⟨q, rfl⟩
    rw [geometricallyConnected_pullback_snd_spMap_iff]
    intro K _ ψ
    have hker : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker ((algebraMap V q.asIdeal.ResidueField).comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
      rfl
    obtain ⟨ψ', hψ'⟩ := exists_residueField_lift _ _ hker
    obtain ⟨L, hL, i, j', hij⟩ := exists_field_amalgam ψ ψ'
    apply connectedSpace_pullback_of_fieldHom p _ i
    have e : i.comp (ψ.comp (algebraMap k (PrimeSpectrum.comap (algebraMap k V) q).asIdeal.ResidueField)) =
        (j'.comp (algebraMap V q.asIdeal.ResidueField)).comp (algebraMap k V) := by
      rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    rw [e]
    exact H L _
  · intro H K _ φ
    haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    let q : PrimeSpectrum V := ⟨RingHom.ker φ, inferInstance⟩
    have hx : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker (φ.comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker]
      rfl
    obtain ⟨ψ, hψ⟩ := exists_residueField_lift _ _ hx
    have := (geometricallyConnected_pullback_snd_spMap_iff p _).mp (H _ ⟨q, rfl⟩) K ψ
    rwa [hψ] at this

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibersStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔ ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerate
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_descends_to_fg :
    ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k))
      [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom →
      GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) →
      ∃ R : Subalgebra k V, R.FG ∧
        GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  intro k V _ _ _ _ G _ _ hs hp hV
  classical
  set U : Set (PrimeSpectrum k) := {x | GeometricallyConnected
      (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} with hUdef
  have hU : IsOpen U := GlobalTheory.T.isOpen_geometricallyConnected_fibers k G hs hp
  have hVU : ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), x ∈ U :=
    (GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers k V G.left G.hom).1 hV
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have htop : Ideal.map (algebraMap k V) I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hx := hVU (PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩) ⟨_, rfl⟩
    have hx' : PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.1 hle
    exact hx' hx
  have h1 : (1 : V) ∈ Submodule.span V (algebraMap k V '' (I : Set k)) := by
    have h := (Ideal.eq_top_iff_one _).1 htop
    exact h
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
  choose f hfI hfg using fun i => (g i).2
  let s : Finset V := Finset.univ.image c
  have hc : ∀ i, c i ∈ Algebra.adjoin k (s : Set V) := fun i =>
    Algebra.subset_adjoin (by simp [s])
  refine ⟨Algebra.adjoin k (s : Set V), Subalgebra.fg_adjoin_finset s, ?_⟩
  apply (GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers k (Algebra.adjoin k (s : Set V)) G.left G.hom).2
  rintro x ⟨y, rfl⟩
  by_contra hx
  have hx' : PrimeSpectrum.comap (algebraMap k (Algebra.adjoin k (s : Set V))) y ∈ Uᶜ := hx
  rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal] at hx'
  have hmem : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) ∈ y.asIdeal :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx' (hfI i))
  have hone : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = 1 := by
    apply Subtype.ext
    have key : (Algebra.adjoin k (s : Set V)).val (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
        algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = ∑ i, c i • (g i : V) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, AlgHom.commutes, Subalgebra.coe_val, hfg, smul_eq_mul]
    exact key.trans (hsum.trans (by simp))
  exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ hmem))

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerateStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.geometricallyConnected_descends_to_finitelyGenerated : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeSpreadsOutFiniteTypeSubring
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem prop_snd_of_isPullback (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange]
    {X Y S' S : Scheme.{0}} {φ : X ⟶ Y} {a : X ⟶ S'} {b : Y ⟶ S} {f : S' ⟶ S}
    (h : IsPullback φ a b f) (ha : P a) : P (pullback.snd b f) := by
  have sq : IsPullback h.isoPullback.inv (pullback.snd b f) a (𝟙 S') :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact P.of_isPullback sq ha

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    [IsCommMonObj G] {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G b φ) : IsCommMonObj G' := by
  have key : ∀ {T : Over S'} (x y : T ⟶ G'), x * y = y * x := by
    intro T x y
    let x₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    let y₀ : Over.mk (T.hom ≫ b) ⟶ G := Over.homMk (y.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc, h.1.w, Over.w_assoc])
    have e₁ := h.2 T x y x₀ y₀ rfl rfl
    have e₂ := h.2 T y x y₀ x₀ rfl rfl
    have c : x₀ * y₀ = y₀ * x₀ := mul_comm _ _
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [← e₁, ← e₂, c]
    · rw [Over.w, Over.w]
  refine ⟨?_⟩
  rw [mul_eq_mul, comp_mul, key]
  simp

theorem abelianScheme_descends_to_fg_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  haveI : IsCommMonObj A := hA.comm
  haveI : IsProper A.hom := hA.proper
  obtain ⟨k, A₀, i₀, c₀, φ, hFk, hk, s₀, sep₀, qc₀, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  haveI : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have hφ' : IsGrpPullback A A₀ (spMap (algebraMap k R)) φ := hφ
  obtain ⟨R₁, hR₁, pr₁⟩ := GlobalTheory.T.separated_properness_fg_subalgebra k R A₀.left A₀.hom sep₀ inferInstance qc₀
    (prop_snd_of_isPullback @IsProper hφ.1 hA.proper)
  obtain ⟨i₁, φ₁, h₁₀, h₁, -⟩ := GlobalTheory.T.abelianScheme_model_baseChange_subalgebra k R A A₀ φ hφ' R₁
  haveI : Algebra.FiniteType k R₁ := (Subalgebra.fg_iff_finiteType R₁).1 hR₁
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing k R₁
  haveI : IsCommMonObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))) :=
    isCommMonObj_of_isGrpPullback h₁₀
  have hk₁ : Algebra.FiniteType ℤ R₁ := Algebra.FiniteType.trans hk inferInstance
  have h₁' : IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁))))
      (spMap (algebraMap R₁ R)) φ₁ := h₁
  have sm₁ : Smooth (pullback.snd A₀.hom (spMap (algebraMap k R₁))) :=
    by haveI := s₀; infer_instance
  obtain ⟨R₂, hR₂, gc₂⟩ := GlobalTheory.T.geometricallyConnected_descends_to_finitelyGenerated R₁ R (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁))))
    sm₁ pr₁ (prop_snd_of_isPullback @GeometricallyConnected h₁.1 hA.geomConnected)
  obtain ⟨i₂, φ₂, h₂₁, h₂, -⟩ := @GlobalTheory.T.abelianScheme_model_baseChange_subalgebra R₁ R _ _ _ A _
    (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))) i₁ φ₁ h₁' R₂
  haveI : Algebra.FiniteType R₁ R₂ := (Subalgebra.fg_iff_finiteType R₂).1 hR₂
  have hk₂ : Algebra.FiniteType ℤ R₂ := Algebra.FiniteType.trans hk₁ inferInstance
  refine ⟨R₂.toSubring, Over.mk (pullback.snd (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R₁)))).hom
    (spMap (algebraMap R₁ R₂))), i₂, φ₂, ?_, hk₂, ?_, h₂⟩
  · intro x hx
    have hx₁ : x ∈ R₁ := R₁.algebraMap_mem (⟨x, hFk hx⟩ : k)
    exact R₂.algebraMap_mem (⟨x, hx₁⟩ : R₁)
  · haveI := sm₁
    haveI := pr₁
    exact ⟨isCommMonObj_of_isGrpPullback h₂₁, by dsimp only [Over.mk_hom]; infer_instance,
      by dsimp only [Over.mk_hom]; infer_instance, gc₂⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeSpreadsOutFiniteTypeSubringStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring | exact GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring <;> assumption)
end
