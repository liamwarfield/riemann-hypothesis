module

public import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ModuleFiniteIntegralClosureFiniteExtPerfect
private theorem UpperTheory.finite_of_finite_comp_injective_noetherian {P B C : Type*} [CommRing P] [CommRing B] [CommRing C]
    [IsNoetherianRing P] (f : P →+* B) (g : B →+* C) (hg : Function.Injective g)
    (h : (g.comp f).Finite) : f.Finite := by
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  have hC : Module.Finite P C := h
  let gl : B →ₗ[P] C :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.comp_apply,
          RingHom.id_apply] }
  haveI : IsNoetherian P C := isNoetherian_of_isNoetherianRing_of_finite P C
  haveI : IsNoetherian P B := isNoetherian_of_injective gl hg
  exact Module.IsNoetherian.finite P B

private theorem UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect (k : Type*) [Field k] (p : ℕ) [ExpChar k p] [PerfectRing k p]
    (ι : Type*) [Finite ι] [ExpChar (MvPolynomial ι k) p] (e : ℕ) :
    (iterateFrobenius (MvPolynomial ι k) p e).Finite := by
  rw [RingHom.finite_iff_isIntegral_and_finiteType]
  constructor
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_pos k p).ne')
    · simp [Polynomial.eval₂_sub, iterateFrobenius_def]
  · apply RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
    have hc : (iterateFrobenius (MvPolynomial ι k) p e).comp MvPolynomial.C
        = MvPolynomial.C.comp (iterateFrobenius k p e) := by
      ext a
      simp [iterateFrobenius_def, map_pow]
    rw [hc]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (bijective_iterateFrobenius k p e).2)

private theorem UpperTheory.module_finite_integralClosure_of_frobenius_finite (P L F : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [Field L] [Algebra P L] [IsFractionRing P L] [Field F] [Algebra P F]
    [Algebra L F] [IsScalarTower P L F] [FiniteDimensional L F] (p : ℕ) [ExpChar P p]
    [ExpChar F p] (hσ : ∀ e, (iterateFrobenius P p e).Finite) :
    Module.Finite P (integralClosure P F) := by
  let E := separableClosure L F
  haveI : FiniteDimensional E F := FiniteDimensional.right L E F
  haveI : IsPurelyInseparable E F := separableClosure.isPurelyInseparable L F
  haveI : ExpChar E p := IntermediateField.expChar' E p
  haveI : IsScalarTower P E F := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply P L E r, ← IsScalarTower.algebraMap_apply L E F,
      IsScalarTower.algebraMap_apply P L F])
  set e := IsPurelyInseparable.exponent E F
  have hpow : ∀ x : F, x ^ p ^ e ∈ E := fun x => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p x
    rw [← hy]
    exact y.2
  haveI : Module.Finite P (integralClosure P E) :=
    IsIntegralClosure.finite P L E (integralClosure P E)
  have hq : p ^ e ≠ 0 := pow_ne_zero _ (expChar_pos F p).ne'
  let fr : integralClosure P F →+* integralClosure P E :=
    { toFun := fun b => ⟨⟨b.1 ^ p ^ e, hpow b.1⟩, by
        rw [mem_integralClosure_iff,
          ← isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) (algebraMap E F).injective]
        exact b.2.pow _⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [mul_pow]
      map_zero' := by
        apply Subtype.ext; apply Subtype.ext; simp [zero_pow hq]
      map_add' := fun a b => by
        apply Subtype.ext; apply Subtype.ext; simp [add_pow_expChar_pow] }
  have hinj : Function.Injective fr := by
    intro a b h
    have h' : a.1 ^ p ^ e = b.1 ^ p ^ e :=
      congrArg (fun y : integralClosure P E => ((y.1 : E) : F)) h
    apply Subtype.ext
    apply (iterateFrobenius F p e).injective
    simpa [iterateFrobenius_def] using h'
  have hcomp : fr.comp (algebraMap P (integralClosure P F)) =
      (algebraMap P (integralClosure P E)).comp (iterateFrobenius P p e) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    apply Subtype.ext
    simp only [fr, iterateFrobenius_def, map_pow, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    have h1 : ((algebraMap P (integralClosure P F) r : integralClosure P F) : F) =
        algebraMap P F r := rfl
    have h2 : (((algebraMap P (integralClosure P E) r : integralClosure P E) : E) : F) =
        algebraMap P F r := by
      rw [IsScalarTower.algebraMap_apply P E F]
      rfl
    simp only [SubmonoidClass.coe_pow, h1, h2]
  have hf := UpperTheory.finite_of_finite_comp_injective_noetherian (algebraMap P (integralClosure P F)) fr hinj (by
    rw [hcomp]
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp (hσ e))
  exact RingHom.finite_algebraMap.mp hf

theorem UpperTheory.module_finite_integralClosure_finiteExt_perfect :
    ∀ (k A K F : Type) [Field k] [PerfectField k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
        [Field K] [Algebra A K] [IsFractionRing A K] [Field F] [Algebra K F] [Algebra A F] [IsScalarTower A K F]
        [FiniteDimensional K F], Module.Finite A (integralClosure A F) := by
  intro k A K F
  intros
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  obtain ⟨p, hp⟩ := ExpChar.exists k
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hgfin
  letI : Algebra (MvPolynomial (Fin s) k) F := ((algebraMap A F).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin s) k) A F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hAF : Function.Injective (algebraMap A F) := by
    rw [IsScalarTower.algebraMap_eq A K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective A K)
  haveI : FaithfulSMul A F := (faithfulSMul_iff_algebraMap_injective A F).mpr hAF
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hginj
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) F :=
    (faithfulSMul_iff_algebraMap_injective _ F).mpr (hAF.comp hginj)
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) F := FractionRing.liftAlgebra _ F
  letI : Algebra (FractionRing A) F := FractionRing.liftAlgebra A F
  letI : Algebra (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    FractionRing.liftAlgebra _ (FractionRing A)
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) :=
    inferInstance
  haveI : FiniteDimensional (FractionRing A) F := by
    refine Module.Finite.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (RingEquiv.refl F) ?_
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, RingEquiv.refl_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A) F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (Fin s) k))
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) F,
      ← IsScalarTower.algebraMap_apply _ (FractionRing (MvPolynomial (Fin s) k)) (FractionRing A),
      IsScalarTower.algebraMap_apply _ A (FractionRing A),
      ← IsScalarTower.algebraMap_apply A (FractionRing A) F,
      ← IsScalarTower.algebraMap_apply _ A F]
  haveI : FiniteDimensional (FractionRing (MvPolynomial (Fin s) k)) F :=
    Module.Finite.trans (FractionRing A) F
  haveI : ExpChar A p := expChar_of_injective_algebraMap (algebraMap k A).injective p
  haveI : ExpChar F p := expChar_of_injective_algebraMap hAF p
  haveI : ExpChar (MvPolynomial (Fin s) k) p :=
    expChar_of_injective_algebraMap (algebraMap k (MvPolynomial (Fin s) k)).injective p
  have hP := UpperTheory.module_finite_integralClosure_of_frobenius_finite (MvPolynomial (Fin s) k) (FractionRing (MvPolynomial (Fin s) k)) F p
    (UpperTheory.finite_iterateFrobenius_mvPolynomial_perfect k p (Fin s))
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.of_finite _ A
  let φ : integralClosure (MvPolynomial (Fin s) k) F →ₗ[MvPolynomial (Fin s) k]
      integralClosure A F :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := fun y =>
    ⟨⟨y.1, isIntegral_trans (R := MvPolynomial (Fin s) k) y.1 y.2⟩, rfl⟩
  haveI : Module.Finite (MvPolynomial (Fin s) k) (integralClosure A F) :=
    Module.Finite.of_surjective φ hφ
  exact Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin s) k) A (integralClosure A F)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SmoothOfNormalCurvePerfectField
open IsLocalRing AlgebraicGeometry CategoryTheory

namespace UpperTheory.LocallyOfRingHomAway

private theorem exists_away (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    [Algebra Ω R] [Algebra.FiniteType Ω R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) (m : Ideal R) [hm : m.IsMaximal] :
    ∃ f ∉ m, Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) := by
  have hnoeth : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Ω R
  have hkd : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact_mod_cast hdim
  have hdl : Ring.DimensionLEOne R :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have hded : IsDedekindDomain R := { }
  have hmbot : m ≠ ⊥ := by
    intro h
    apply hnf
    rw [Ring.isField_iff_maximal_bot]
    rw [← h]
    exact hm
  let S := Localization.AtPrime m
  have hdvr : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hmbot S
  have hreg : IsRegularLocalRing S := inferInstance
  have hsm : Algebra.FormallySmooth Ω S :=
    GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField Ω S
  have het : Algebra.FormallyEtale Ω (ResidueField S) :=
    GlobalTheory.formallyEtale_residueField_of_isMaximal Ω Ω m S
  obtain ⟨_, hrk⟩ := GlobalTheory.free_and_finrank_kaehler_eq_finrank_cotangentSpace Ω S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace S).mp hreg
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one S] at h1
    exact_mod_cast h1
  have hfp : Algebra.FinitePresentation Ω R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsa : Algebra.IsSmoothAt Ω m := hsm
  exact GlobalTheory.exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt Ω m (hrk.trans hcot)

private theorem locally_of_ringHom (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [IsDomain R]
    (ψ : Ω →+* R) (hft : ψ.FiniteType) (hic : IsIntegrallyClosed R)
    (hdim : ringKrullDim R ≤ 1) (hnf : ¬ IsField R) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) ψ := by
  letI : Algebra Ω R := ψ.toAlgebra
  haveI : Algebra.FiniteType Ω R := hft
  refine ⟨{t | RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap R (Localization.Away t)).comp ψ)}, ?_, fun t ht => ht⟩
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, hsm⟩ := exists_away Ω R hdim hnf M
  apply hf
  apply hle
  apply Ideal.subset_span
  have heq : ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra =
      (inferInstance : Algebra Ω (Localization.Away f)) :=
    Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply Ω R _ r).symm)
  show @Algebra.IsStandardSmoothOfRelativeDimension 1 Ω (Localization.Away f) _ _
    ((algebraMap R (Localization.Away f)).comp ψ).toAlgebra
  rw [heq]
  exact hsm

end UpperTheory.LocallyOfRingHomAway

theorem UpperTheory.smooth_of_normal_curve_perfectField :
    LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := by
  intro Ω _ _ C c hint hlft hic hdim
  have key : ∀ (V : C.Opens) (hV : IsAffineOpen V) (a b : C), a ∈ V → b ∈ V → a ≠ b →
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
        (c.appLE ⊤ V (by simp)).hom := by
    intro V hV a b ha hb hab
    haveI : Nonempty V := ⟨⟨a, ha⟩⟩
    have hdom : IsDomain Γ(C, V) := inferInstance
    let ι := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
    let ψ : Ω →+* Γ(C, V) := (c.appLE ⊤ V (by simp)).hom.comp ι.symm.toRingHom
    have hφ : (c.appLE ⊤ V (by simp)).hom = ψ.comp ι.toRingHom := by
      ext r
      simp [ψ]
    rw [hφ]
    apply (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).right
    apply UpperTheory.LocallyOfRingHomAway.locally_of_ringHom Ω Γ(C, V) ψ
    · have hft : (c.appLE ⊤ V (by simp)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType c hlft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact hft.comp (RingHom.FiniteType.of_surjective _ ι.symm.surjective)
    · refine IsIntegrallyClosed.of_localization_maximal (fun p _ hp => ?_)
      let y : PrimeSpectrum Γ(C, V) := ⟨p, hp.isPrime⟩
      have hy : hV.fromSpec y ∈ V := by
        have : hV.fromSpec y ∈ Set.range hV.fromSpec := ⟨y, rfl⟩
        rwa [hV.range_fromSpec] at this
      letI := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨hV.fromSpec y, hy⟩
      haveI hloc : IsLocalization p.primeCompl (C.presheaf.stalk (hV.fromSpec y)) :=
        hV.isLocalization_stalk' y hy
      exact (hic (hV.fromSpec y)).of_equiv
        (IsLocalization.algEquiv p.primeCompl (C.presheaf.stalk (hV.fromSpec y))
          (Localization.AtPrime p)).toRingEquiv
    · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(C, V)]
      change topologicalKrullDim (Spec Γ(C, V)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le C V).trans hdim.le
    · intro hf
      letI := hf.toField
      have ha' : a ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact ha
      have hb' : b ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hb
      obtain ⟨pa, rfl⟩ := ha'
      obtain ⟨pb, rfl⟩ := hb'
      have hss : Subsingleton (PrimeSpectrum Γ(C, V)) := inferInstance
      exact hab (congrArg _ (hss.elim pa pb))
  have hgen : ∀ (W : C.Opens) (z : C), z ∈ W → genericPoint C ∈ W := by
    intro W z hz
    exact ((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr ⟨z, trivial, hz⟩
  have hexists : ∃ z : C, z ≠ genericPoint C := by
    by_contra h
    push_neg at h
    have hsub : Subsingleton (TopologicalSpace.IrreducibleCloseds C) := by
      refine ⟨fun s t => ?_⟩
      obtain ⟨p, hp⟩ := s.isIrreducible.nonempty
      obtain ⟨q, hq⟩ := t.isIrreducible.nonempty
      ext y
      rw [h y]
      exact ⟨fun _ => h q ▸ hq, fun _ => h p ▸ hp⟩
    have h0 := Order.krullDim_nonpos_of_subsingleton (α := TopologicalSpace.IrreducibleCloseds C)
    unfold topologicalKrullDim at hdim
    rw [hdim] at h0
    exact absurd h0 (by norm_num)
  rw [HasRingHomProperty.iff_exists_appLE (P := @SmoothOfRelativeDimension 1)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource
      (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).left)]
  intro x
  by_cases hx : x = genericPoint C
  · obtain ⟨z, hz⟩ := hexists
    obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ z)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hx ▸ hgen W z hzW, by simp, ?_⟩
    exact key W hW z (genericPoint C) hzW (hgen W z hzW) hz
  · obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
    refine ⟨⟨⊤, isAffineOpen_top _⟩, ⟨W, hW⟩, hxW, by simp, ?_⟩
    exact key W hW x (genericPoint C) hxW (hgen W x hxW) hx
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4
open GroundTheory.Heights₂.Heights.Model (genericSpecMap)

private theorem objIso {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F] [Algebra C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] [Algebra Γ(C, U) F]
    [IsScalarTower Γ(C, U) C.functionField F] :
    ∃ E : Γ((genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization ⁻¹ᵁ U) ≅
        CommRingCat.of (integralClosure Γ(C, U) F),
      (genericSpecMap C F).fromNormalization.app U ≫ E.hom =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) := by
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hmem : genericSpecMap C F (IsLocalRing.closedPoint F) ∈ U := by
    rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_closedPoint]
    exact hη
  have key := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_app_iso C F U hη hmem
  letI : Algebra Γ(C, U) Γ(Spec (CommRingCat.of F), genericSpecMap C F ⁻¹ᵁ U) :=
    ((genericSpecMap C F).app U).hom.toAlgebra
  let eR := ((Spec (CommRingCat.of F)).presheaf.mapIso (eqToIso
    (Scheme.preimage_eq_top_of_closedPoint_mem _ hmem).symm).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of F), genericSpecMap C F ⁻¹ᵁ U) ≃ₐ[Γ(C, U)] F :=
    AlgEquiv.ofRingEquiv (f := eR) fun x => by
      rw [IsScalarTower.algebraMap_apply Γ(C, U) C.functionField F]
      exact congrArg (fun φ => φ.hom x) key
  refine ⟨(genericSpecMap C F).normalizationObjIso hU ≪≫
    eA.mapIntegralClosure.toRingEquiv.toCommRingCatIso, ?_⟩
  rw [(genericSpecMap C F).fromNormalization_app hU]
  rw [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  ext x
  exact eA.commutes x

private theorem isFin {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} [IsIntegral C]
    (c : C ⟶ Sp Ω) [LocallyOfFiniteType c] (F : Type) [Field F] [Algebra C.functionField F]
    [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)] :
    IsFinite (genericSpecMap C F).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hN : (U : Set C).Nonempty
  · haveI : Nonempty U := ⟨⟨hN.some, hN.some_mem⟩⟩
    haveI : IsFractionRing Γ(C, U) C.functionField :=
      functionField_isFractionRing_of_isAffineOpen C U hU
    letI : Algebra Ω Γ(C, U) := (GlobalTheory.NormCurve.constHom c U).toAlgebra
    haveI : Algebra.FiniteType Ω Γ(C, U) := GlobalTheory.NormCurve.finiteType_constHom c hU
    letI : Algebra Γ(C, U) F :=
      ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
    haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Module.Finite Γ(C, U) (integralClosure Γ(C, U) F) :=
      UpperTheory.module_finite_integralClosure_finiteExt_perfect Ω Γ(C, U) C.functionField F
    obtain ⟨E, hE⟩ := objIso F U hU
    have h1 : (genericSpecMap C F).fromNormalization.app U =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) ≫ E.inv := by
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h1, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun y => ⟨E.hom y, ?_⟩)
      (RingHom.finite_algebraMap.mpr inferInstance)
    simp
  · have hb : U = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.mp hN)
    subst hb
    have hb' : (genericSpecMap C F).fromNormalization ⁻¹ᵁ (⊥ : C.Opens) = ⊥ := by simp
    haveI : Subsingleton Γ((genericSpecMap C F).normalization,
        (genericSpecMap C F).fromNormalization ⁻¹ᵁ (⊥ : C.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal
        ((genericSpecMap C F).normalization.sheaf.isTerminalOfEqEmpty hb')
    exact RingHom.Finite.of_surjective _ fun y => ⟨0, Subsingleton.elim _ _⟩

private theorem stalkClosed {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F]
    [Algebra C.functionField F] [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    (y : (genericSpecMap C F).normalization) :
    IsIntegrallyClosed ((genericSpecMap C F).normalization.presheaf.stalk y) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (genericSpecMap C F).fromNormalization y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  letI : Algebra Γ(C, U) F :=
    ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
  haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsIntegrallyClosed (integralClosure Γ(C, U) F) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension C.functionField
  obtain ⟨E, -⟩ := objIso F U hU
  have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
    hU.preimage (genericSpecMap C F).fromNormalization
  have hy : y ∈ (genericSpecMap C F).fromNormalization ⁻¹ᵁ U := hxU
  letI iA := TopCat.Presheaf.algebra_section_stalk (genericSpecMap C F).normalization.presheaf
    (⟨y, hy⟩ : (genericSpecMap C F).fromNormalization ⁻¹ᵁ U)
  haveI := hV.isLocalization_stalk ⟨y, hy⟩
  let e := E.commRingCatIsoToRingEquiv
  letI : Algebra (integralClosure Γ(C, U) F) ((genericSpecMap C F).normalization.presheaf.stalk y) :=
    ((algebraMap _ _).comp e.symm.toRingHom).toAlgebra
  haveI := IsLocalization.isLocalization_of_base_ringEquiv
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    ((genericSpecMap C F).normalization.presheaf.stalk y) e
  refine isIntegrallyClosed_of_isLocalization (R := integralClosure Γ(C, U) F) _
    (Submonoid.map e (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
    (le_nonZeroDivisors_of_noZeroDivisors ?_)
  rintro ⟨x, hx, hx0⟩
  rw [map_eq_zero_iff e e.injective] at hx0
  subst hx0
  exact hx (Ideal.zero_mem _)

private theorem dimOne {Ω : Type} [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω)
    (hc : IsCurve c) (F : Type) [Field F]
    [Algebra C.functionField F] [FiniteDimensional C.functionField F]
    [QuasiCompact (genericSpecMap C F)] [QuasiSeparated (genericSpecMap C F)]
    [IsFinite (genericSpecMap C F).fromNormalization] :
    topologicalKrullDim (genericSpecMap C F).normalization = 1 := by
  obtain ⟨p0⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have hemb := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
    (e := (id : (genericSpecMap C F).normalization → (genericSpecMap C F).normalization))
    Topology.IsEmbedding.id (Z := Set.univ) Set.range_id
  rw [← hemb]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := Set.univ)
    ⟨(genericSpecMap C F).toNormalization p0, trivial⟩ fun y _ => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (genericSpecMap C F).fromNormalization y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  letI : Algebra Γ(C, U) F :=
    ((algebraMap C.functionField F).comp (algebraMap Γ(C, U) C.functionField)).toAlgebra
  haveI : IsScalarTower Γ(C, U) C.functionField F := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨E, -⟩ := objIso F U hU
  have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
    hU.preimage (genericSpecMap C F).fromNormalization
  refine ⟨((genericSpecMap C F).fromNormalization ⁻¹ᵁ U : Set _),
    ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U).isOpen, hxU, ?_⟩
  have hinj : Function.Injective (algebraMap Γ(C, U) F) :=
    (algebraMap C.functionField F).injective.comp (IsFractionRing.injective Γ(C, U) C.functionField)
  haveI : FaithfulSMul Γ(C, U) (integralClosure Γ(C, U) F) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h => hinj (congrArg Subtype.val h)
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
    (by rw [hV.range_fromSpec, Set.inter_univ])]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
    Γ((genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization ⁻¹ᵁ U)).trans ?_
  rw [ringKrullDim_eq_of_ringEquiv E.commRingCatIsoToRingEquiv,
    GlobalTheory.ringKrullDim_eq_of_isIntegral Γ(C, U) (integralClosure Γ(C, U) F),
    CurveCut.CoverPf.krullDim_eq_one c hc U hU ⟨_, hxU⟩]
  rfl

private theorem surjNorm {C : Scheme.{0}} [IsIntegral C] (F : Type) [Field F]
    [Algebra C.functionField F] [QuasiCompact (genericSpecMap C F)]
    [QuasiSeparated (genericSpecMap C F)] : Surjective (genericSpecMap C F).fromNormalization := by
  constructor
  have hcl : IsClosedMap (genericSpecMap C F).fromNormalization :=
    (genericSpecMap C F).fromNormalization.isClosedMap
  have hη : genericPoint C ∈ Set.range (genericSpecMap C F).fromNormalization := by
    have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.genericSpecMap_closedPoint C F
    rw [← Scheme.Hom.toNormalization_fromNormalization (genericSpecMap C F)] at h
    exact ⟨_, h⟩
  have hsub : closure ({genericPoint C} : Set C) ⊆ Set.range (genericSpecMap C F).fromNormalization :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hcl.isClosed_range
  intro x
  exact hsub (specializes_iff_mem_closure.mp (genericPoint_specializes x))

private theorem restrictSquare {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) :
    (f ∣_ U) ≫ hU.isoSpec.hom = (hU.preimage f).isoSpec.hom ≫ Spec.map (f.app U) := by
  rw [← cancel_mono hU.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, Category.assoc, Scheme.Hom.app_eq_appLE,
    IsAffineOpen.SpecMap_appLE_fromSpec f hU (hU.preimage f) le_rfl,
    ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]

theorem UpperTheory.exists_finite_surjective_curve_cover_of_functionField_extension :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
        ∀ (hI : IsIntegral C) (F : Type) [Field F] [Algebra C.functionField F] [FiniteDimensional C.functionField F],
        ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧
          ∀ (U : C.Opens) (hU : IsAffineOpen U) (_ : Nonempty U) (_ : Algebra Γ(C, U) F) (_ : IsScalarTower Γ(C, U) C.functionField F),
          ∃ e : (γ ⁻¹ᵁ U).toScheme ≅ Sp (integralClosure Γ(C, U) F),
            (γ ∣_ U) ≫ hU.isoSpec.hom = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F))) := by
  intro Ω _ _ C c hc hI F _ _ _
  haveI : IsProper c := hc.2.1
  haveI : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c
  haveI : IsFinite (genericSpecMap C F).fromNormalization := isFin c F
  refine ⟨(genericSpecMap C F).normalization, (genericSpecMap C F).fromNormalization,
    ⟨inferInstance, inferInstance, ?_⟩, surjNorm F, inferInstance, ?_⟩
  · exact UpperTheory.smooth_of_normal_curve_perfectField Ω ((genericSpecMap C F).fromNormalization ≫ c) inferInstance inferInstance
      (stalkClosed F) (dimOne c hc F)
  · intro U hU hne alg tower
    haveI := hne
    letI := alg
    haveI := tower
    obtain ⟨E, hE⟩ := objIso F U hU
    have hV : IsAffineOpen ((genericSpecMap C F).fromNormalization ⁻¹ᵁ U) :=
      hU.preimage (genericSpecMap C F).fromNormalization
    refine ⟨hV.isoSpec ≪≫ Scheme.Spec.mapIso E.symm.op, ?_⟩
    rw [restrictSquare _ hU, Iso.trans_hom, Category.assoc]
    congr 1
    have h2 : (genericSpecMap C F).fromNormalization.app U =
        CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)) ≫ E.inv := by
      rw [← hE, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h2, Spec.map_comp]
    rfl
