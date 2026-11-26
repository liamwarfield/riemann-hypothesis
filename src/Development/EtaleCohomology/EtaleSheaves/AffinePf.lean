module

public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
public import Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.AffinePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.AffinePf

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (f' : E₁' ⟶ E₂')
    (a : E₁ ≅ E₁') (b : E₂ ≅ E₂') (h : f ≫ b.hom = a.hom ≫ f') (hf : Eqv R f' F) : Eqv R f F := fun n => by
  have hiso : ∀ {X Y : Spc} (e : X ≅ Y), Function.Bijective (pull R e.hom F n) := fun e => by
    refine ⟨Function.LeftInverse.injective (g := pull R e.inv F n) fun x => ?_,
      Function.RightInverse.surjective (g := pull R e.inv F n) fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hf2 : f = a.hom ≫ f' ≫ b.inv := by rw [← Category.assoc, ← h]; simp
  have : ⇑(pull R f F n) = pull R a.hom F n ∘ pull R f' F n ∘ pull R b.inv F n := by
    funext x; rw [hf2]; simp only [Function.comp_apply]; rw [pull_comp, pull_comp]
  rw [this]
  exact (hiso a).comp ((hf n).comp (hiso b.symm))

theorem ι_comp_eq {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) (hV : IsAffineOpen V) :
    V.ι ≫ p = hV.isoSpec.hom ≫ Spec.map (gam p V) := by
  have h1 : Spec.map (gam p V) = hV.fromSpec ≫ p := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec T)) hV (by simp)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [gam, Spec.map_comp]
    exact this
  rw [h1, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem Affine_of : Affine := by
  intro q i T K k X p V hV hb
  have hpo := IsPushout.of_hasPushout k (gam p V)
  have hre := hb _ _ _ hpo
  have hS := isPullback_SpecMap_of_isPushout _ _ _ _ hpo.flip
  have h1 := (isPullback_morphismRestrict (pullback.fst p (Spec.map k)) V).paste_vert
    (IsPullback.of_hasPullback p (Spec.map k))
  have h2 : IsPullback hV.isoSpec.hom (V.ι ≫ p) (Spec.map (gam p V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [ι_comp_eq p V hV, Category.comp_id]⟩
  have h3 := h1.paste_horiz h2
  rw [Category.comp_id] at h3
  refine eqv_of_sq _ _ _ (sch.map (Spec.map (pushout.inr k (gam p V))))
    (sch.mapIso (h3.isoIsPullback _ _ hS)) (sch.mapIso hV.isoSpec) ?_ hre
  simp only [Functor.mapIso_hom, ← Functor.map_comp, IsPullback.isoIsPullback_hom_fst]

end LateralTheory.E.AffinePf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtAlgPf
open CategoryTheory LateralTheory.E.t_E3Cut

namespace LateralTheory.E.EtAlgPf

theorem key (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (c : B) : ∃ p : Polynomial A, (∃ n, algebraMap A B (p.coeff n) ∉ Q) ∧ p.eval₂ (algebraMap A B) c ∈ Q := by
  let P := Q.comap (algebraMap A B)
  have : Q.LiesOver P := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  have : Algebra.IsUnramifiedAt A Q := inferInstance
  have : Module.Finite P.ResidueField Q.ResidueField := inferInstance
  have : IsScalarTower A P.ResidueField Q.ResidueField := inferInstance
  set x := algebraMap B Q.ResidueField c
  have hx : IsIntegral P.ResidueField x := Algebra.IsIntegral.isIntegral x
  let p := minpoly P.ResidueField x
  have hp0 : p ≠ 0 := minpoly.ne_zero hx
  let M := nonZeroDivisors (A ⧸ P)
  let q := IsLocalization.integerNormalization M p
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_spec M p
  have hq0 : q ≠ 0 := by
    intro h; exact hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h)
  have hqm : q.map (algebraMap (A ⧸ P) P.ResidueField) = Polynomial.C (algebraMap (A ⧸ P) P.ResidueField b) * p := by
    rw [hb.2, ← Polynomial.smul_eq_C_mul, algebraMap_smul]
  obtain ⟨r, hr⟩ := Polynomial.map_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
  obtain ⟨n, hn⟩ : ∃ n, q.coeff n ≠ 0 := by
    by_contra h; push_neg at h; exact hq0 (Polynomial.ext h)
  refine ⟨r, ⟨n, ?_⟩, ?_⟩
  · intro hm; apply hn
    rw [← hr, Polynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  · rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
    have e1 : algebraMap A Q.ResidueField = (algebraMap P.ResidueField Q.ResidueField).comp
        ((algebraMap (A ⧸ P) P.ResidueField).comp (Ideal.Quotient.mk P)) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply A (A ⧸ P) P.ResidueField,
        ← IsScalarTower.algebraMap_apply A P.ResidueField Q.ResidueField]
    rw [e1, ← Polynomial.eval₂_map, ← Polynomial.map_map, hr, hqm, ← Polynomial.aeval_def, map_mul,
      minpoly.aeval, mul_zero]

theorem EtAlg_of : LateralTheory.E.AlgResPropsPf.EtAlg := by
  intro A B f hf
  let _ := f.hom.toAlgebra
  have : Algebra.Etale A B := hf
  intro Q hQ c
  exact key A B Q c

end LateralTheory.E.EtAlgPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocEtPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.LocEtPf

lemma et_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    Et (X.presheaf.map (homOfLE h).op) := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  show (X.presheaf.map (homOfLE h).op).hom.Etale
  convert this using 2
  rfl

theorem LocEt_of : LocEt := by
  intro T X p _ x
  obtain ⟨_, _, V0, hV0, hx0, -, -⟩ := Smooth.exists_isStandardSmooth p x
  have hf : (p.appLE ⊤ V0 (by simp)).hom.Smooth := p.smooth_appLE (isAffineOpen_top _) hV0 _
  have hloc := (RingHom.Smooth.locally_isStandardSmooth hf).span_eq_top
  have hcov := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top V0 _ hloc
  have hx1 : x ∈ (⨆ i ∈ {g : Γ(X, V0) | ((algebraMap Γ(X, V0) (Localization.Away g)).comp
      (p.appLE ⊤ V0 (by simp)).hom).IsStandardSmooth}, X.basicOpen i) := by rw [hcov]; exact hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx1
  obtain ⟨t, ht, hxt⟩ := hx1
  have hB := hV0.basicOpen t
  let := hV0.isLocalization_basicOpen t
  let e : Localization.Away t ≃ₐ[Γ(X, V0)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have hs : (gam p (X.basicOpen t)).hom.IsStandardSmooth := by
    have h1 := (RingHom.isStandardSmooth_respectsIso.1 _ e.toRingEquiv ht)
    have h2 := RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv.symm h1
    have hgam : gam p (X.basicOpen t) = (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V0 (by simp) ≫
        X.presheaf.map (homOfLE (X.basicOpen_le t)).op := by
      simp only [gam]
      congr 1
      exact (Scheme.Hom.appLE_map ..).symm
    have halg : algebraMap Γ(X, V0) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := rfl
    rw [hgam]
    convert h2 using 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, halg]
    rfl
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  refine ⟨X.basicOpen t, n, hxt, fun V hV hVU => ?_⟩
  refine ⟨CommRingCat.ofHom g ≫ X.presheaf.map (homOfLE hVU).op, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ hg (et_res hB hV hVU)
  · ext1
    rw [← Category.assoc]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [hgC]
    simp only [gam, Scheme.Hom.appLE, ← CommRingCat.hom_comp, Category.assoc, ← Functor.map_comp]
    rfl

end LateralTheory.E.LocEtPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafCochainVanishPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCochainVanishPf

variable {R : Type} [CommRing R]

theorem free_ext_zero (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.hom.app (op U)).hom (freeGen R P U x) = 0) : φ = 0 := by
  have h0 : (0 : (free R).obj P ⟶ G).hom = 0 := rfl
  refine Sheaf.hom_ext ?_
  rw [h0]
  refine sheafify_hom_ext _ _ _ G.property ?_
  ext U : 2
  refine ModuleCat.free_hom_ext (fun x => ?_)
  exact (h U.unop x.down).trans (by erw [Limits.comp_zero]; rfl)

theorem chains_isZero (E : Spc) (p : ℤ) (hp : 0 < p) : Limits.IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => ?_)
  have : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  omega

theorem cochain_zero_of (E : Spc) {U V : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (K : Cx R) (k : ℤ)
    (γ : Cochain ((chains R).obj E) K k)
    (hU : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0)
    (hV : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) :
    γ = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : 0 < p
  · exact (chains_isZero (R := R) E p hp).eq_of_src _ _
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
  have hφ : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q hpq = 0 := by
    have := hc.2.2 (op (SimplexCategory.mk N))
    rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
      ((free R).map (g.app (op (SimplexCategory.mk N))))), Limits.comp_zero]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hU N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
    · rw [biprod.inr_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hV N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
  rw [← Iso.hom_inv_id_assoc (chainsXIso R E N) (γ.v _ _ hpq), hφ, Limits.comp_zero]

end LateralTheory.E.LeafCochainVanishPf

theorem LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := by
  intro R _ U V E f g hc K k γ hU hV
  exact LateralTheory.E.LeafCochainVanishPf.cochain_zero_of E f g hc K k γ hU hV
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPfExt
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable (q : ℕ) (k : ℤ)

instance resKInj : (res (ZMod q) (tw q k)).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem ext_homotopy {S T L : Cx (ZMod q)} (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ L) [L.IsKInjective] :
    ∃ u : T ⟶ L, Nonempty (Homotopy (ε ≫ u) a) := by
  let _ := HasDerivedCategory.standard (Shv (ZMod q))
  let Φ := DerivedCategory.quotientCompQhIso (Shv (ZMod q))
  obtain ⟨g, hg⟩ := (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj T) L).2
    (Φ.hom.app T ≫ inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map a ≫ Φ.inv.app L)
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj S) L).1
  have nat : ∀ {X Y : Cx (ZMod q)} (f : X ⟶ Y), DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) =
      Φ.hom.app X ≫ DerivedCategory.Q.map f ≫ Φ.inv.app Y := by
    intro X Y f
    have := Φ.hom.naturality f
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this]
    simp
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map (ε ≫ u)) = _
  rw [Functor.map_comp, Functor.map_comp, hg, nat ε, nat a]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id_assoc]

theorem leafTwResExt : LeafTwResExt := by
  intro q _ k T e ⟨_, ε, hε, he⟩
  obtain ⟨u, ⟨H⟩⟩ := ext_homotopy q (ε := ε) (a := resAug (tw q k))
  refine ⟨u, fun U ζ => ?_⟩
  have h0 : ε.f 0 ≫ u.f 0 = (resAug (tw q k)).f 0 := by
    have hc := H.comm 0
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at hc
    have z1 : IsZero ((sgl (tw q k)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
    have z2 : IsZero ((res (ZMod q) (tw q k)).X (-1)) := by
      unfold res InjectiveResolution.cochainComplex
      exact HomologicalComplex.isZero_extend_X _ _ _ (by
        intro n hn
        change ((n : ℕ) : ℤ) = -1 at hn
        omega)
    have e1 : H.hom 1 0 = 0 := z1.eq_of_src _ _
    have e2 : H.hom 0 (-1) = 0 := z2.eq_of_tgt _ _
    rw [e1, e2] at hc
    simpa using hc
  rw [← he U ζ, map_map, map_map, h0]
  rfl

theorem LeafTwPairExists_of' (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) : LateralTheory.E.CupProductRingLaws.LeafTwPairExists :=
  LeafTwPairExists_of h1 h2 leafTwResExt

end LateralTheory.E.LeafTwPairExistsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FibCovPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.FibCovPf

open LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

theorem qaic_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : QAIC q W') : QAIC q W := by
  obtain ⟨B, i1, i2, I, hB, hq, ⟨e'⟩⟩ := h
  exact ⟨B, i1, i2, I, hB, hq, ⟨e ≪≫ e'⟩⟩

theorem qaic_empty (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (hB : AIC B) (hq : IsUnit (q : B))
    {W : Scheme.{0}} [IsEmpty W] : QAIC q W := by
  have : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have : IsEmpty (Spec (CommRingCat.of (B ⧸ (⊤ : Ideal B)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ (⊤ : Ideal B))))
  exact ⟨B, inferInstance, inferInstance, ⊤, hB, hq, ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty⟩⟩

theorem qaic_good (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) (B0 : Type) [CommRing B0]
    [IsDomain B0] (hB0 : AIC B0) (hq0 : IsUnit (q : B0)) {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A))
    (hw : Good w) : QAIC q (pullback w (cpt A)) := by
  rcases hw with hE | ⟨B, i1, i2, i3, hB, e, he⟩
  · have : IsEmpty ↥(pullback w (cpt A) : Scheme.{0}) := ⟨fun x => hE.elim ((pullback.fst w (cpt A)).base x)⟩
    exact qaic_empty q B0 hB0 hq0
  · subst he
    refine ⟨B, i1, i2, (IsLocalRing.maximalIdeal A).map (algebraMap A B), hB, ?_, ?_⟩
    · simpa using hq.map (algebraMap A B)
    · obtain ⟨e2⟩ := fibre_affine A B
      exact ⟨(pullbackRightPullbackFstIso _ (cpt A) e.hom).symm ≪≫ asIso (pullback.snd e.hom _) ≪≫ e2⟩

theorem exists_absolutely_integrally_closed_domain_with_q_unit (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (hZ : AICSch Z) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B), AIC B ∧ IsUnit (q : B) := by
  obtain ⟨hI, hA⟩ := hZ
  obtain ⟨x⟩ : Nonempty Z := hI.nonempty
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Z.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨Γ(Z, U), inferInstance, IsIntegral.component_integral U, hA U hU ⟨x, hxU⟩, ?_⟩
  have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top).hom
  simpa using this

theorem FibCov_of : FibCov := by
  intro q A _ _ hq Z p hZ U V f g _ _ hc hU hV hW
  obtain ⟨B0, _, _, hB0, hq0⟩ := exists_absolutely_integrally_closed_domain_with_q_unit q A hq p hZ
  refine ⟨pullback f (pullback.fst p (cpt A)), pullback g (pullback.fst p (cpt A)),
    pullback.snd f (pullback.fst p (cpt A)), pullback.snd g (pullback.fst p (cpt A)),
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hc, Set.preimage_univ]
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) f) (qaic_good q A hq B0 hB0 hq0 _ hU)
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) g) (qaic_good q A hq B0 hB0 hq0 _ hV)
  · refine qaic_of_iso ?_ (qaic_good q A hq B0 hB0 hq0 _ hW)
    exact pullbackLeftPullbackSndIso f (pullback.fst p (cpt A)) (pullback.snd g (pullback.fst p (cpt A))) ≪≫
      pullback.congrHom rfl pullback.condition.symm ≪≫
      (pullbackLeftPullbackSndIso f g (pullback.fst g (pullback.fst p (cpt A)))).symm ≪≫
      pullbackRightPullbackFstIso g (pullback.fst p (cpt A)) (pullback.snd f g) ≪≫
      pullback.congrHom pullback.condition.symm rfl ≪≫
      pullbackRightPullbackFstIso p (cpt A) (pullback.fst f g ≫ f) ≪≫
      pullback.congrHom (Category.assoc _ _ _) rfl

end LateralTheory.E.FibCovPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChainsDiscCoprodPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ChainsDiscCoprodPf

variable (R : Type) [CommRing R]

theorem chains_disc_f {P Q : PSh} (f : P ⟶ Q) (n : ℕ) :
    ((chains R).map (disc.map f)).f (-(n : ℤ)) =
      (chainsXIso R (disc.obj P) n).hom ≫ (free R).map f ≫ (chainsXIso R (disc.obj Q) n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem isZero_chains_X (E : Spc) (i : ℤ) (hi : ∀ n : ℕ, -(n : ℤ) ≠ i) :
    IsZero (((chains R).obj E).X i) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat i (fun n => hi n)

theorem cofan_of_isos {C : Type*} [Category C] {ι : Type} {A A' : ι → C} {B B' : C}
    (a : ∀ j, A' j ≅ A j) (b : B' ≅ B) (f : ∀ j, A j ⟶ B) (f' : ∀ j, A' j ⟶ B')
    (hf : ∀ j, f' j = (a j).hom ≫ f j ≫ b.inv) (hc : IsColimit (Cofan.mk B f)) :
    Nonempty (IsColimit (Cofan.mk B' f')) := by
  refine ⟨Cofan.IsColimit.mk _ (fun s => b.hom ≫ hc.desc (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j)) ?_ ?_⟩
  · intro s j
    have := hc.fac (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) ⟨j⟩
    simp only [Cofan.mk_ι_app] at this
    change f' j ≫ _ = _
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc, this, Iso.hom_inv_id_assoc]
  · intro s m hm
    rw [← Iso.inv_comp_eq]
    refine hc.uniq (Cofan.mk s.pt fun j => (a j).inv ≫ s.inj j) _ ?_
    rintro ⟨j⟩
    change f j ≫ b.inv ≫ m = (a j).inv ≫ s.inj j
    rw [← hm j]
    change f j ≫ b.inv ≫ m = (a j).inv ≫ f' j ≫ m
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc]

theorem cofan_of_zero {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type} {A : ι → C} {B : C}
    (hA : ∀ j, IsZero (A j)) (hB : IsZero B) (f : ∀ j, A j ⟶ B) :
    Nonempty (IsColimit (Cofan.mk B f)) :=
  ⟨Cofan.IsColimit.mk _ (fun _ => 0) (fun _ j => (hA j).eq_of_src _ _) (fun _ _ _ => hB.eq_of_src _ _)⟩

theorem degColimit {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q)
    (hc : IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) (i : ℤ) :
    Nonempty (IsColimit ((HomologicalComplex.eval _ _ i).mapCocone
      (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))) := by
  rw [(isColimitMapCoconeCofanMkEquiv _ _ _).nonempty_congr]
  by_cases h : 0 < i
  · have h' : ∀ n : ℕ, -(n : ℤ) ≠ i := fun n => by omega
    exact cofan_of_zero (fun j => isZero_chains_X R _ i h') (isZero_chains_X R _ i h') _
  · have hi : i = -(((-i).toNat : ℕ) : ℤ) := by omega
    rw [hi]
    generalize (-i).toNat = n
    exact cofan_of_isos (fun j => chainsXIso R (disc.obj (P j)) n) (chainsXIso R (disc.obj Q) n)
      (fun j => (free R).map (p j)) _ (fun j => chains_disc_f R (p j) n) hc

theorem ChainsDiscCoprod_of : LateralTheory.E.CoprodPf.ChainsDiscCoprod := by
  intro R _ ι P Q p ⟨hc⟩
  exact ⟨HomologicalComplex.isColimitOfEval _ _ (fun i => (degColimit R P Q p hc i).some)⟩

end LateralTheory.E.ChainsDiscCoprodPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PiecesPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.PiecesPf

lemma sq1 {T S C' C : Type} [CommRing T] [CommRing S] [CommRing C'] [CommRing C]
    (a : T →+* C') (π : T →+* S) (ρ : C' →+* C) (b : S →+* C) (hρ : Function.Surjective ρ) (hπ : Function.Surjective π)
    (hcomm : ρ.comp a = b.comp π) (hker : RingHom.ker ρ = (RingHom.ker π).map a) :
    IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom π) (CommRingCat.ofHom ρ) (CommRingCat.ofHom b) := by
  have w : CommRingCat.ofHom a ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom π ≫ CommRingCat.ofHom b := by
    ext x; exact congrArg (fun f : T →+* C => f x) hcomm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w ?_ ?_ ?_ ?_)
  · intro s
    refine CommRingCat.ofHom (ρ.liftOfSurjective hρ ⟨s.inl.hom, ?_⟩)
    rw [hker, Ideal.map_le_iff_le_comap]
    intro t ht
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    simp only [Ideal.mem_comap, RingHom.mem_ker] at ht ⊢
    rw [h1, ht, map_zero]
  · intro s
    ext x
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    exact RingHom.liftOfSurjective_comp_apply ρ hρ _ x
  · intro s
    ext x
    obtain ⟨t, rfl⟩ := hπ x
    have h1 := congrArg (fun f => f.hom t) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 ⊢
    rw [← RingHom.comp_apply b π, ← hcomm, RingHom.comp_apply, RingHom.liftOfSurjective_comp_apply]
    exact h1
  · intro s m hm _
    ext x
    obtain ⟨y, rfl⟩ := hρ x
    simp only [CommRingCat.hom_ofHom]
    rw [RingHom.liftOfSurjective_comp_apply]
    have := congrArg (fun f => f.hom y) hm
    simpa using this

theorem Pieces_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) :
    LateralTheory.E.FinEtSectionPf.Pieces := by
  intro _ _ S C _ _ _ _ hQA
  obtain ⟨T, _, _, π, hAIC, hπ⟩ := hQA
  obtain ⟨C', _, _, ρ, hEt, hρ, hcomm, hker⟩ := hL T S C π hπ
  have := hEt
  obtain ⟨n, e', he', hoi⟩ := hA T C' hAIC
  refine ⟨n, ρ ∘ e', he'.map ρ, fun j => ?_⟩
  let fₘ : Localization.Away (e' j) →+* Localization.Away (ρ (e' j)) :=
    IsLocalization.Away.map _ _ ρ (e' j)
  have : IsLocalization ((Submonoid.powers (e' j)).map ρ) (Localization.Away (ρ (e' j))) := by
    rw [Submonoid.map_powers]; infer_instance
  have H : fₘ.comp (algebraMap C' _) = (algebraMap C _).comp ρ := IsLocalization.map_comp _
  have sq2 := CommRingCat.isPushout_of_isLocalization ρ fₘ H (Submonoid.powers (e' j))
  have sq := (sq1 (algebraMap T C') π ρ (algebraMap S C) hρ hπ hcomm hker).paste_horiz sq2.flip
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ sq
  have hj := hoi j
  rw [CommRingCat.ofHom_comp] at hj
  have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) pb hj
  rw [CommRingCat.ofHom_comp]
  exact this

end LateralTheory.E.PiecesPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.RootAICPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace LateralTheory.E.RootAICPf

open LateralTheory.E.t_E2Cut

theorem evalMap {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) (q : ℕ) (a : R) :
    φ ((cyclotomic q R).eval a) = (cyclotomic q K).eval (φ a) := by
  rw [← map_cyclotomic q φ, Polynomial.eval_map, Polynomial.eval₂_hom]

theorem aeval_eq {R : Type} [CommRing R] (q : ℕ) (a : R) :
    aeval a (cyclotomic q ℤ) = (cyclotomic q R).eval a := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

theorem localRoot {q : ℕ} {X : Scheme.{0}} [IsIntegral X] (hX : AICSch X) (hq : q ≠ 0)
    (hK : ((q : ℕ) : X.functionField) ≠ 0) (V : X.Opens) (hV : IsAffineOpen V) [hne : Nonempty V] :
    ∃ ζ : Γ(X, V), IsPrimitiveRoot (X.germToFunctionField V ζ) q := by
  have hA := hX.2 V hV (by obtain ⟨x⟩ := hne; exact ⟨x.1, x.2⟩)
  obtain ⟨a, ha⟩ := hA (cyclotomic q Γ(X, V)) (cyclotomic.monic q _)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  refine ⟨a, ?_⟩
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [← isRoot_cyclotomic_iff]
  show (cyclotomic q _).eval _ = 0
  rw [← evalMap, ha, map_zero]

theorem RootAIC_of : LateralTheory.E.HZeroPf.RootAIC := by
  intro q X hX hq
  haveI := hX.1
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x0, trivial⟩⟩
  have hK : ((q : ℕ) : X.functionField) ≠ 0 := by
    intro h
    have := hq.map (X.germToFunctionField ⊤).hom
    rw [map_natCast] at this
    rw [h] at this
    exact not_isUnit_zero this
  have hq0 : q ≠ 0 := by rintro rfl; exact hK (by simp)
  haveI : NeZero q := ⟨hq0⟩
  have hnb : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hx⟩
  obtain ⟨V0, hV0, hx0⟩ := hnb x0
  haveI : Nonempty V0 := ⟨⟨x0, hx0⟩⟩
  obtain ⟨ζ0, hζ0⟩ := localRoot hX hq0 hK V0 hV0
  obtain ⟨s, hs⟩ := GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally (⊤ : X.Opens)
    (X.germToFunctionField V0 ζ0) (fun x _ => by
      obtain ⟨V, hV, hx⟩ := hnb x
      haveI hne : Nonempty V := ⟨⟨x, hx⟩⟩
      obtain ⟨ζ, hζ⟩ := localRoot hX hq0 hK V hV
      obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hζ0.pow_eq_one
      exact ⟨V, hne, ζ ^ k, hx, le_top, by rw [map_pow]; exact hk⟩)
  refine ⟨⟨s, hq, ?_⟩⟩
  apply Scheme.germToFunctionField_injective X ⊤
  have : NeZero ((q : ℕ) : X.functionField) := ⟨hK⟩
  rw [aeval_eq, map_zero]
  show (X.germToFunctionField ⊤).hom _ = 0
  rw [evalMap]
  show (cyclotomic q _).eval ((X.germToFunctionField ⊤) s) = 0
  rw [hs]
  exact (isRoot_cyclotomic_iff.mpr hζ0)

end LateralTheory.E.RootAICPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntFibPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntFibPf

lemma eqv_comp {R : Type} [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n := by
    funext x; exact pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

lemma eqv_iso {R : Type} [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

lemma isPushout_quot (A : Type) [CommRing A] [IsLocalRing A] {B : CommRingCat.{0}} (ψ : CommRingCat.of A ⟶ B) :
    IsPushout ψ (CommRingCat.ofHom (IsLocalRing.residue A))
      (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map
        : IsLocalRing.ResidueField A →+* _)) := by
  have w : CommSq ψ (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom)))
      (CommRingCat.ofHom (Ideal.quotientMap ((IsLocalRing.maximalIdeal A).map ψ.hom) ψ.hom Ideal.le_comap_map : IsLocalRing.ResidueField A →+* _)) := by
    constructor; ext a; rfl
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom
      (Ideal.Quotient.lift ((IsLocalRing.maximalIdeal A).map ψ.hom) s.inl.hom ?_)) ?_ ?_ ?_)
  · rename_i s; intro a ha
    have hle : ((IsLocalRing.maximalIdeal A).map ψ.hom) ≤ RingHom.ker s.inl.hom := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
      have h1 := congrArg (fun f => f.hom x) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
      simp only [Ideal.mem_comap, RingHom.mem_ker, h1,
        (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
    exact hle ha
  · intro s; ext b; rfl
  · intro s; ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    have h1 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    exact h1
  · intro s m h1 h2
    ext b
    have := congrArg (fun f => f.hom b) h1
    exact this

theorem IntFib_of : LateralTheory.E.IntPBPf.IntFib := by
  intro A _ _ X p hp
  have : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  refine ⟨Γ(X, ⊤), inferInstance, ψ.hom, ?_, ?_⟩
  · rw [← IsIntegralHom.SpecMap_iff, hψ]; infer_instance
  · intro q i h
    have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot A ψ)
    have hP' : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map ψ.hom))) ≫ X.isoSpec.inv) _ p
        (LateralTheory.E.t_E2Cut.cpt A) :=
      hP.of_iso (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        (by simp [hψ]) (by simp)
    rw [← hP'.isoPullback_inv_fst, Functor.map_comp, Functor.map_comp]
    exact eqv_comp _ _ _ (eqv_iso (sch.mapIso hP'.isoPullback.symm) _)
      (eqv_comp _ _ _ h (eqv_iso (sch.mapIso X.isoSpec.symm) _))

end LateralTheory.E.IntFibPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StepPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.AICAcycPf

namespace LateralTheory.E.StepPf

theorem empty_case {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hc : Set.range f ∪ Set.range g = Set.univ) [IrreducibleSpace X] (hW : ¬ Nonempty ↥(pullback f g : Scheme.{0})) :
    Set.range f = Set.univ ∨ Set.range g = Set.univ := by
  by_contra hne
  push Not at hne
  have hfne : (Set.range f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.2 (by simpa [h] using hc)
  have hgne : (Set.range g).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.1 (by simpa [h] using hc)
  have hirr : IsPreirreducible (Set.univ : Set X) := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
  obtain ⟨x, -, hxf, hxg⟩ := hirr _ _ f.isOpenEmbedding.isOpen_range g.isOpenEmbedding.isOpen_range
    (by simpa using hfne) (by simpa using hgne)
  obtain ⟨u, rfl⟩ := hxf
  obtain ⟨v, hv⟩ := hxg
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u v hv.symm
  exact hW ⟨z⟩

theorem acyc_of_surj (q : ℕ) {V X : Scheme.{0}} (g : V ⟶ X) [IsOpenImmersion g] (hg : Set.range g = Set.univ)
    (h : Acyc q (sch.obj V)) : Acyc q (sch.obj X) := by
  have : Surjective g := ⟨Set.range_eq_univ.mp hg⟩
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, inferInstance⟩
  exact acyc_of_iso q (asIso g).symm h

theorem Step_of : Step := by
  intro hyp hMV hZ q U V X f g _ _ hc hX hU hV hq hAU hAV hAW
  have hXi : IsIntegral X := hX.1
  by_cases hW : Nonempty ↥(pullback f g : Scheme.{0})
  · have hAW' := hAW hW
    have : IsIntegral U := hU.1
    have := hW
    have : IsIntegral (pullback f g : Scheme.{0}) := isIntegral_of_isOpenImmersion (pullback.fst f g ≫ f)
    have hqU : IsUnit (q : Γ(U, ⊤)) := by
      have := hq.map f.appTop.hom
      simpa using this
    intro n i hn
    obtain ⟨δ, hex, -⟩ := hMV hyp (ZMod q) (tw q i)
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
    have hsU := hAU (m + 1) i hn
    have hsV := hAV (m + 1) i hn
    obtain ⟨-, h2, h3⟩ := hex f g hc m
    constructor
    suffices h0 : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 by
      intro a b; rw [h0 a, h0 b]
    intro x
    obtain ⟨w, hw⟩ := (h3 x).mp ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw]
    rcases lt_or_eq_of_le (show (0 : ℤ) ≤ m by omega) with hm | hm
    · have hsW := hAW' m i hm
      rw [Subsingleton.elim w 0, map_zero]
    · subst hm
      rw [h2]
      obtain ⟨a, ha⟩ := (hZ hyp q (pullback.fst f g) hU inferInstance hqU i).2 w
      exact ⟨a, 0, by rw [map_zero, sub_zero]; exact ha.symm⟩
  · rcases empty_case f g hc hW with h | h
    · exact acyc_of_surj q f h hAU
    · exact acyc_of_surj q g h hAV

end LateralTheory.E.StepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChartAcycPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartAcycPf

theorem acyc_of_iso {q : ℕ} {E E' : Spc} (e : E ≅ E') (h : Acyc q E') : Acyc q E := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q E n i, z = pull _ e.hom (tw q i) n (pull _ e.inv (tw q i) n z) := by
    intro z
    rw [← pull_comp, e.hom_inv_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull _ e.inv (tw q i) n x) (pull _ e.inv (tw q i) n y)]

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h2 : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    rw [Polynomial.map_map]; ext n; simp
  rw [← h2]
  change Polynomial.eval (e.toRingHom a) _ = 0
  rw [Polynomial.eval_map_apply, ha, map_zero]

theorem fib_iso_quot {A : Type} [CommRing A] [IsLocalRing A] {U : Scheme.{0}} [IsAffine U]
    (f : U ⟶ Spec (CommRingCat.of A)) :
    ∃ (φ : A →+* Γ(U, ⊤)), Nonempty (fib f ≅ Spec (CommRingCat.of
      (Γ(U, ⊤) ⧸ (IsLocalRing.maximalIdeal A).map φ))) := by
  let e := U.isoSpec
  let φ := Spec.preimage (e.inv ≫ f)
  have hf : f = e.hom ≫ Spec.map φ := by
    rw [Spec.map_preimage]; simp
  letI : Algebra A Γ(U, ⊤) := φ.hom.toAlgebra
  refine ⟨φ.hom, ⟨?_⟩⟩
  refine (pullback.congrHom hf rfl) ≪≫
    (asIso (pullback.map (e.hom ≫ Spec.map φ) (cpt A) (Spec.map φ) (cpt A) e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))) ≪≫ ?_
  refine (pullbackSpecIso A Γ(U, ⊤) (IsLocalRing.ResidueField A)) ≪≫ ?_
  let i := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := A) Γ(U, ⊤)
    (IsLocalRing.maximalIdeal A)).toRingEquiv.toCommRingCatIso
  exact Scheme.Spec.mapIso i.op

theorem ChartAcyc_of (hQ : QuotAcyc) : ChartAcyc := by
  intro H q A _ _ Z U p ι hι hU hZ hq
  have : IsIntegral Z := hZ.1
  by_cases hne : Nonempty U
  · have : IsIntegral U := isIntegral_of_isOpenImmersion ι
    obtain ⟨φ, ⟨e⟩⟩ := fib_iso_quot (ι ≫ p)
    have hdom : IsDomain Γ(U, ⊤) := inferInstance
    have haff : IsAffineOpen (ι ''ᵁ (⊤ : U.Opens)) := (isAffineOpen_top U).image_of_isOpenImmersion ι
    have hnV : ((ι ''ᵁ (⊤ : U.Opens) : Z.Opens) : Set Z).Nonempty := by
      obtain ⟨x⟩ := hne
      exact ⟨ι x, x, trivial, rfl⟩
    have haic : AIC Γ(U, ⊤) :=
      aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ haff hnV)
    have hqB : IsUnit (q : Γ(U, ⊤)) := by
      simpa using hq.map φ
    exact acyc_of_iso (sch.mapIso e) (hQ H q Γ(U, ⊤) _ haic hqB)
  · rw [not_nonempty_iff] at hne
    obtain ⟨x⟩ : Nonempty Z := inferInstance
    obtain ⟨V, ⟨W, hW, rfl⟩, hxW, -⟩ := (Z.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hWne : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hdom : IsDomain Γ(Z, W) := inferInstance
    have haic : AIC Γ(Z, W) := hZ.2 W hW ⟨x, hxW⟩
    let ψ : CommRingCat.of A ⟶ Γ(Z, W) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
    have hqC : IsUnit (q : Γ(Z, W)) := by
      simpa using hq.map ψ.hom
    have h1 := hQ H q Γ(Z, W) ⊤ haic hqC
    have : IsEmpty (fib (ι ≫ p)) := ⟨fun y => hne.elim ((pullback.fst (ι ≫ p) (cpt A)) y)⟩
    have : Subsingleton (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have : IsEmpty (Spec (CommRingCat.of (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))))) :=
      ⟨fun y => (show PrimeSpectrum (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) from y).isPrime.ne_top (Subsingleton.elim _ _)⟩
    exact acyc_of_iso (sch.mapIso (isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty)) h1

end LateralTheory.E.ChartAcycPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.HKCoprodPf
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.HKCoprodPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {K : ι → CochainComplex C ℤ} (c : Cofan K)
  (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {L : CochainComplex C ℤ}

include hc in
theorem hom_ext_v {p q : ℤ} {a b : c.pt.X p ⟶ L.X q} (h : ∀ j, (c.inj j).f p ≫ a = (c.inj j).f p ≫ b) : a = b :=
  (hc p).hom_ext fun ⟨j⟩ => h j

include hc in
theorem cochain_ext {n : ℤ} {x y : Cochain c.pt L n}
    (h : ∀ j, (Cochain.ofHom (c.inj j)).comp x (zero_add n) = (Cochain.ofHom (c.inj j)).comp y (zero_add n)) : x = y := by
  ext p q hpq
  refine hom_ext_v c hc fun j => ?_
  have := congrArg (fun z => Cochain.v z p q hpq) (h j)
  simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this

def cof (L : CochainComplex C ℤ) {n : ℤ} (b : ∀ j, Cochain (K j) L n) (p q : ℤ) (hpq : p + n = q) :
    Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p) where
  pt := L.X q
  ι := Discrete.natTrans fun k => (b k.as).v p q hpq

def glue (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {n : ℤ}
    (b : ∀ j, Cochain (K j) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hc p).desc (cof L b p q hpq)

theorem restr_glue {n : ℤ} (b : ∀ j, Cochain (K j) L n) (j : ι) :
    (Cochain.ofHom (c.inj j)).comp (glue c hc b) (zero_add n) = b j := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (hc p).fac (cof L b p q hpq) ⟨j⟩

include hc in
theorem bij (n : ℤ) : Function.Bijective fun (x : CohomologyClass c.pt L n) (j : ι) =>
    cpre (Cocycle.ofHom (c.inj j)) L n n (zero_add n) x := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    have hj : ∀ j, ∃ β : Cochain (K j) L (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj j)).comp (x - y : Cocycle c.pt L n).1 (zero_add n) := by
      intro j
      have h := congrFun hxy j
      simp only [cpre_mk] at h
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)] at h
      obtain ⟨β, hβ⟩ := h
      refine ⟨β, ?_⟩
      rw [hβ]
      simp [zcomp, Cochain.comp_sub]
    choose β hβ using hj
    refine ⟨glue c hc β, cochain_ext c hc fun j => ?_⟩
    rw [← δ_ofHom_comp, restr_glue, hβ]
  · intro y
    choose z hz using fun j => (y j).mk_surjective
    have hδ : δ n (n + 1) (glue c hc fun j => (z j).1) = 0 := cochain_ext c hc fun j => by
      rw [← δ_ofHom_comp, restr_glue, Cocycle.δ_eq_zero]; simp
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hδ), funext fun j => ?_⟩
    simp only [cpre_mk]
    rw [← hz j]
    congr 1
    exact Cocycle.ext (restr_glue c hc (fun j => (z j).1) j)

end General

set_option synthInstance.maxHeartbeats 400000 in
theorem HKCoprod_of : LateralTheory.E.CoprodPf.HKCoprod := by
  intro R _ ι K c hc F n
  have h1 : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits.{1} (Shv R)
  have h0 : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} (Shv R)
  have : HasColimitsOfShape (Discrete ι) (Shv R) := inferInstance
  exact bij c (fun p => isColimitOfPreserves (HomologicalComplex.eval _ _ p) hc) n

end LateralTheory.E.HKCoprodPf
end
end
