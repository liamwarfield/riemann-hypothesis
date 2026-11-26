module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AutomorphicArithmetic.CommutativeAlgebra.PicData
public import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitEqMultiplicativeGroupSection

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleTrivializationOfTwoInvertibleModuleTo
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem UpperTheory.PicD.Data.Triv.mapAlg (P : Data) {A : Type} [CommRing A]
    {z : P.S1.obj (CommRingCat.of A)} {M : Type} [AddCommGroup M] [Module A M]
    {C E : Type} [CommRing C] [Algebra A C] [CommRing E] [Algebra A E]
    {w : P.S0.obj (CommRingCat.of C)} {g : (C ⊗[A] C)ˣ} {t : M →ₗ[A] C}
    (h : P.Triv z M C w g t) (f : C →ₐ[A] E) :
    P.Triv z M E (P.r0 f.toRingHom w)
      (Units.map (Algebra.TensorProduct.map f f).toRingHom.toMonoidHom g) (f.toLinearMap ∘ₗ t) := by
  have e0 : f.toRingHom.comp (algebraMap A C) = algebraMap A E := f.comp_algebraMap
  have e1 : (Algebra.TensorProduct.map f f).toRingHom.comp (i1 A C).toRingHom
      = (i1 A E).toRingHom.comp f.toRingHom := by
    ext x <;> simp
  have e2 : (Algebra.TensorProduct.map f f).toRingHom.comp (i2 A C).toRingHom
      = (i2 A E).toRingHom.comp f.toRingHom := by
    ext x <;> simp
  have key : ∀ (c : C) (x : C ⊗[A] C), Algebra.TensorProduct.map f f (c • x)
      = f c • Algebra.TensorProduct.map f f x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.smul_tmul']
    | add a b ha hb => simp [smul_add, ha, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P.diff_mapDegZero, h.dw, P.mapDegOne_comp, e0]
  · rw [← P.mapDegZero_ofUnit, h.hg, map_sub, P.mapDegZero_comp, P.mapDegZero_comp, P.mapDegZero_comp, P.mapDegZero_comp, e1, e2]
  · intro m
    have := congrArg (Algebra.TensorProduct.map f f) (h.ht m)
    rw [key] at this
    simpa using this
  · letI : Algebra C E := f.toRingHom.toAlgebra
    haveI : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq' e0.symm
    have hb1 : IsBaseChange C t :=
      IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h.bij) (fun x => by simp)
    have hb2 := hb1.comp (IsBaseChange.linearMap C E)
    have : LinearMap.liftBaseChange E (f.toLinearMap ∘ₗ t) = hb2.equiv.toLinearMap := by
      ext m
      simp [IsBaseChange.equiv_tmul]
      rfl
    rw [this]
    exact hb2.equiv.bijective

theorem UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' →
        ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
          ∃ (w : P.S0.obj (CommRingCat.of C)) (g : (C ⊗[A] C)ˣ) (t : M →ₗ[A] C)
            (w' : P.S0.obj (CommRingCat.of C)) (g' : (C ⊗[A] C)ˣ) (t' : M' →ₗ[A] C),
            P.Triv z M C w g t ∧ P.Triv z' M' C w' g' t' := by
  intro P A _ z z' M M' _ _ _ _ hM hM'
  obtain ⟨C, _, _, hf, he, w, g, t, h⟩ := hM
  obtain ⟨C', _, _, hf', he', w', g', t', h'⟩ := hM'
  exact ⟨C ⊗[A] C', inferInstance, inferInstance, Module.FaithfullyFlat.trans A C _,
    Algebra.Etale.comp A C _, _, _, _, _, _, _,
    UpperTheory.PicD.Data.Triv.mapAlg P h Algebra.TensorProduct.includeLeft,
    UpperTheory.PicD.Data.Triv.mapAlg P h' Algebra.TensorProduct.includeRight⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.MultiplicativeGroupOneCocycleEtaleLocallyCobound
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SectionsSpecPiBijectiveProdSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private noncomputable abbrev sι {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))

private lemma sι_eq {n : ℕ} (C : Fin n → Type) [∀ i, CommRing (C i)] (i : Fin n) :
    sι C i = Sigma.ι (fun i => Spec (CommRingCat.of (C i))) i ≫ sigmaSpec (fun i => CommRingCat.of (C i)) :=
  (ι_sigmaSpec (fun i => CommRingCat.of (C i)) i).symm

private theorem bijective_sheaf_sigma_restrict {P : Scheme.{0}ᵒᵖ ⥤ Type 1}
    (hP : Presieve.IsSheaf Scheme.zariskiTopology P) {n : ℕ} (X : Fin n → Scheme.{0}) :
    Function.Bijective (fun (s : P.obj (op (∐ X))) (i : Fin n) => P.map (Sigma.ι X i).op s) := by
  have hcov := hP.isSheafFor _ (sigmaOpenCover X).mem_grothendieckTopology
  rw [Presieve.isSheafFor_arrows_iff] at hcov
  have hcomp : ∀ x : ∀ i, P.obj (op (X i)), Presieve.Arrows.Compatible P (Sigma.ι X) x := by
    intro x i j Z gi gj h
    by_cases hij : i = j
    · subst hij
      rw [cancel_mono] at h
      rw [h]
    · haveI := isEmpty_of_commSq_sigmaι_of_ne ⟨h⟩ hij
      exact (hP (⊥ : Sieve Z) (Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext
        (fun _ _ hf => hf.elim)
  constructor
  · intro s t hst
    exact (hcov (fun i => P.map (Sigma.ι X i).op s) (hcomp _)).unique (fun i => rfl)
      (fun i => (congr_fun hst i).symm)
  · intro y
    obtain ⟨t, ht, -⟩ := hcov y (hcomp y)
    exact ⟨t, funext ht⟩

theorem UpperTheory.sections_specPi_bijective_prod_sections :
    ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℕ) (C : Fin n → Type) [∀ i, CommRing (C i)],
        Function.Bijective (fun (s : Sec F (Spec (CommRingCat.of (∀ i, C i)))) (i : Fin n) =>
          (Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))) s : Sec F (Spec (CommRingCat.of (C i))))) := by
  intro R _ F n C _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology
      (F.obj ⋙ CategoryTheory.forget (ModuleCat (ULift.{1, 0} R))) := by
    apply Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)).mp F.property
  have key := bijective_sheaf_sigma_restrict hG (fun i => Spec (CommRingCat.of (C i)))
  have hiso : Function.Bijective ((F.obj ⋙ CategoryTheory.forget _).map
      (sigmaSpec (fun i => CommRingCat.of (C i))).op) :=
    (isIso_iff_bijective _).mp inferInstance
  convert key.comp hiso using 1
  funext s i
  rw [show Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) = _ from sι_eq C i]
  simp only [Sec.res, Function.comp_apply, op_comp, Functor.map_comp]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteEtaleFaithfullyFlatCoverOfEtaleLocal
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma exists_local (A : Type) [CommRing A]
    (P : ∀ V : Scheme.{0}, (V ⟶ Spec (CommRingCat.of A)) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V), P V g → P W (k ≫ g))
    (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (hV : IsAffine V) (hg : Etale g)
    (hPV : P V g) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A B))) = Set.range g ∧
      P (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  haveI := hg
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop
  letI : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hg' : g = V.isoSpec.hom ≫ Spec.map φ := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hinv : Spec.map φ = V.isoSpec.inv ≫ g := by
    rw [hg', Iso.inv_hom_id_assoc]
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = Spec.map φ := rfl
  refine ⟨Γ(V, ⊤), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · have he : Etale (Spec.map φ) := by
      rw [hinv]
      infer_instance
    exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp he)
  · rw [hmap, hg']
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨V.isoSpec.inv z, by simp⟩
    · rintro ⟨z, rfl⟩
      exact ⟨V.isoSpec.hom z, rfl⟩
  · rw [hmap, hinv]
    exact hP V _ g V.isoSpec.inv hPV

theorem UpperTheory.exists_finite_etale_faithfullyFlat_cover_of_etaleLocal_affine :
    ∀ (A : Type) [CommRing A] (P : ∀ V : Scheme.{0}, (V ⟶ Spec (CommRingCat.of A)) → Prop),
        (∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V), P V g → P W (k ≫ g)) →
        Loc (Spec (CommRingCat.of A)) P →
        ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra A (C i)),
          Algebra.Etale A (∀ i, C i) ∧ Module.FaithfullyFlat A (∀ i, C i) ∧
          ∀ i, P (Spec (CommRingCat.of (C i))) (Spec.map (CommRingCat.ofHom (algebraMap A (C i)))) := by
  intro A _ P hP hL
  have hx := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover _ P hP).1 hL
  choose V g hVa hge hxm hPx using hx
  have h1 := fun x => exists_local A P hP (V x) (g x) (hVa x) (hge x) (hPx x)
  choose B iB aB hBe hBr hBP using h1
  letI : ∀ x, CommRing (B x) := iB
  letI : ∀ x, Algebra A (B x) := aB
  have hopen : ∀ x, IsOpen (Set.range (g x)) := fun x => by
    haveI := hge x
    exact IsOpenMap.isOpen_range (g x).isOpenMap
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (g x)) hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxm x⟩)
  let e : Fin t.card ≃ t := t.equivFin.symm
  haveI : ∀ i, Algebra.Etale A (B (e i)) := fun i => hBe _
  refine ⟨t.card, fun i => B (e i), fun i => inferInstance, fun i => inferInstance,
    inferInstance, ?_, fun i => hBP _⟩
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  obtain ⟨i, hi⟩ := e.surjective ⟨x, hxt⟩
  have hpi : p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (B (e i))))) := by
    rw [hBr, hi]
    exact hpx
  obtain ⟨q, hq⟩ := hpi
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j => B (e j)) i) q, ?_⟩
  rw [← hq]
  rfl
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma sec_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  change (ModuleCat.Hom.hom (F.obj.map k.op)) ((ModuleCat.Hom.hom (F.obj.map g.op)) a) = (ModuleCat.Hom.hom (F.obj.map (k ≫ g).op)) a
  rw [op_comp, Functor.map_comp]
  rfl

private lemma sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (a : Sec F U) : Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom a) h

theorem UpperTheory.multiplicativeGroup_oneCocycle_etaleLocally_coboundary :
    ∀ (A : Type) [CommRing A] (z : Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of A))),
        Sec.map ((res ℤ Gm).d 1 2) z = 0 →
        ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C), Module.FaithfullyFlat A C ∧ Algebra.Etale A C ∧
          ∃ w : Sec ((res ℤ Gm).X 0) (Spec (CommRingCat.of C)),
            Sec.map ((res ℤ Gm).d 0 1) w = Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) z := by
  intro A _ z hz
  have hloc := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec (CommRingCat.of A))).2.2.1 0 1 2 (by norm_num) (by norm_num) z (by norm_num) hz
  have hstab : ∀ (V W : Scheme) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V),
      (∃ y, Sec.map ((res ℤ Gm).d 0 1) y = Sec.res g z) →
      (∃ y, Sec.map ((res ℤ Gm).d 0 1) y = Sec.res (k ≫ g) z) := by
    rintro V W g k ⟨y, hy⟩
    exact ⟨Sec.res k y, by rw [sec_map_res, hy, sec_res_res]⟩
  obtain ⟨n, C, hC, hA, het, hff, hP⟩ := UpperTheory.exists_finite_etale_faithfullyFlat_cover_of_etaleLocal_affine A _ hstab hloc
  obtain ⟨w, hw⟩ := (UpperTheory.sections_specPi_bijective_prod_sections ℤ ((res ℤ Gm).X 0) n C).2 (fun i => (hP i).choose)
  refine ⟨(i : Fin n) → C i, inferInstance, inferInstance, hff, het, w, ?_⟩
  apply (UpperTheory.sections_specPi_bijective_prod_sections ℤ ((res ℤ Gm).X 1) n C).1
  funext i
  have hwi := congrFun hw i
  dsimp only at hwi
  show Sec.res _ (Sec.map _ w) = Sec.res _ (Sec.res _ z)
  rw [← sec_map_res, hwi, (hP i).choose_spec, sec_res_res, ← Spec.map_comp]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.UnitSectionsMultiplicativeGroupBijectiveAffine
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.UnitsInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def ofLine {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.UnitsInj

private theorem unitsInj_ofLine_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.UnitsInj.ofLine (UpperTheory.UnitsInj.toLine a) = a := by
  unfold UpperTheory.UnitsInj.ofLine UpperTheory.UnitsInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.UnitsInj.evalT]

private theorem comp_unitsInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.UnitsInj.toLine a = UpperTheory.UnitsInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.UnitsInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.UnitsInj.evalT]
  · simp [UpperTheory.UnitsInj.evalT]

theorem UpperTheory.unitSections_multiplicativeGroup_bijective_affine :
    ∀ (R : Type) [CommRing R], Function.Bijective
        (unitSec : (Γ(Spec (CommRingCat.of R), ⊤))ˣ → Sec Gm (Spec (CommRingCat.of R))) := by
  intro R _
  refine ⟨?_, fun b => UpperTheory.exists_unit_eq_multiplicativeGroup_section _ b⟩
  intro u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op (Spec (CommRingCat.of R)))
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)) =
      UpperTheory.UnitsInj.toLine (v : Γ(Spec (CommRingCat.of R), ⊤)) := by
    refine (UpperTheory.UnitsInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.UnitsInj.toLine _ = f ≫ UpperTheory.UnitsInj.toLine _
    rw [comp_unitsInj_toLine, comp_unitsInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(Spec (CommRingCat.of R), ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.UnitsInj.ofLine key
  rw [unitsInj_ofLine_toLine, unitsInj_ofLine_toLine] at h4
  exact Units.ext h4
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.PicMain
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.InvertibleModuleEquivOfSameCocycle
open CategoryTheory TensorProduct UpperTheory.PicD

namespace UpperTheory.PicD

private theorem smul_eq_tmul_mul {A C : Type} [CommRing A] [CommRing C] [Algebra A C] (c : C) (x : C ⊗[A] C) :
    c • x = (c ⊗ₜ[A] (1 : C)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, mul_add, hx, hy]
  | tmul a b => simp [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]

private theorem injective_and_range {A C M : Type} [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [AddCommGroup M] [Module A M]
    (g : C ⊗[A] C) (t : M →ₗ[A] C) (ht : ∀ m, t m • g = (1 : C) ⊗ₜ[A] t m)
    (bij : Function.Bijective (LinearMap.liftBaseChange C t)) :
    Function.Injective t ∧ LinearMap.range t = Mg g := by
  have hψ : ∀ m, LinearMap.liftBaseChange C t ((1 : C) ⊗ₜ[A] m) = t m := fun m => by simp
  refine ⟨fun a b hab => ?_, ?_⟩
  · apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := C) M
    apply bij.1
    simpa [hψ] using hab
  · ext b
    constructor
    · rintro ⟨m, rfl⟩
      exact GlobalTheory.FlatDescent.mem_invariants.2 (ht m)
    · intro hb
      have hb' : b • g = (1 : C) ⊗ₜ[A] b := GlobalTheory.FlatDescent.mem_invariants.1 hb
      obtain ⟨s, rfl⟩ := bij.2 b
      have hinj : Function.Injective
          (((LinearMap.liftBaseChange C t).restrictScalars A).lTensor C) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ bij.1
      have hcan : ∀ x : C ⊗[A] M,
          ((LinearMap.liftBaseChange C t).restrictScalars A).lTensor C (GlobalTheory.FlatDescent.canonical C M x) =
            (LinearMap.liftBaseChange C t x) • g := by
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add (f := _), hx, hy, add_smul]
        | tmul c m =>
          have h1 : c ⊗ₜ[A] t m = c • ((1 : C) ⊗ₜ[A] t m) := by simp [smul_tmul']
          simp [GlobalTheory.FlatDescent.canonical, h1, ← ht m, mul_smul]
      have hs : GlobalTheory.FlatDescent.canonical C M s = (1 : C) ⊗ₜ[A] s := by
        apply hinj
        rw [hcan, hb']
        simp
      have hd : GlobalTheory.FlatDescent.amitsurDiff C M s = 0 := by
        simp [GlobalTheory.FlatDescent.amitsurDiff, hs]
      obtain ⟨m, rfl⟩ := ((GlobalTheory.FlatDescent.amitsur_exact (A := A) C M).2 s).1 hd
      exact ⟨m, by simp⟩

end UpperTheory.PicD

theorem UpperTheory.invertibleModule_equiv_of_same_cocycle :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z M' → Nonempty (M ≃ₗ[A] M') := by
  intro P A _ z M M' _ _ _ _ h h'
  obtain ⟨C, iC, iA, hff, het, w, g, t, w', g', t', T, T'⟩ := UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z M M' h h'
  have hd : P.dd C (w' - w) = 0 := by rw [map_sub, T.dw, T'.dw, sub_self]
  obtain ⟨u, hu⟩ := (P.dd_eq_zero _).1 hd
  have hg : g' * Units.map (i1 A C).toRingHom.toMonoidHom u =
      g * Units.map (i2 A C).toRingHom.toMonoidHom u := by
    apply P.un_injective
    rw [P.un_mul, P.un_mul, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, hu, T.hg, T'.hg, map_sub, map_sub]
    abel
  have hg' : (g' : C ⊗[A] C) * ((u : C) ⊗ₜ[A] (1 : C)) = (g : C ⊗[A] C) * ((1 : C) ⊗ₜ[A] (u : C)) := by
    simpa using congrArg Units.val hg
  let t₁ : M →ₗ[A] C := LinearMap.mulLeft A (u : C) ∘ₗ t
  have ht₁ : ∀ m, t₁ m • (g' : C ⊗[A] C) = (1 : C) ⊗ₜ[A] t₁ m := by
    intro m
    have h1 := T.ht m
    rw [smul_eq_tmul_mul] at h1 ⊢
    have h2 : ((u : C) * t m) ⊗ₜ[A] (1 : C) = ((u : C) ⊗ₜ[A] (1 : C)) * (t m ⊗ₜ[A] (1 : C)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    have h3 : (1 : C) ⊗ₜ[A] ((u : C) * t m) = ((1 : C) ⊗ₜ[A] t m) * ((1 : C) ⊗ₜ[A] (u : C)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    simp only [t₁, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [h2, h3, ← h1]
    linear_combination (t m ⊗ₜ[A] (1 : C)) * hg'
  have hψ : ∀ x : C ⊗[A] M, LinearMap.liftBaseChange C t₁ x = (u : C) * LinearMap.liftBaseChange C t x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]
    | tmul c m => simp [t₁, mul_left_comm]
  have hbij : Function.Bijective (LinearMap.liftBaseChange C t₁) := by
    have : (LinearMap.liftBaseChange C t₁ : C ⊗[A] M → C) =
        (fun x => (u : C) * x) ∘ (LinearMap.liftBaseChange C t) := funext hψ
    rw [this]
    exact (Units.mulLeft_bijective u).comp T.bij
  obtain ⟨i₁, r₁⟩ := injective_and_range (g' : C ⊗[A] C) t₁ ht₁ hbij
  obtain ⟨i₂, r₂⟩ := injective_and_range (g' : C ⊗[A] C) t' T'.ht T'.bij
  exact ⟨LinearEquiv.ofInjective t₁ i₁ ≪≫ₗ LinearEquiv.ofEq _ _ (r₁.trans r₂.symm) ≪≫ₗ
    (LinearEquiv.ofInjective t' i₂).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.RelAddTensorProductOfRel
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem cotangentAtUnit_tangentBijection {A C M M' : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (t : M →ₗ[A] C) (t' : M' →ₗ[A] C)
    (h : Function.Bijective (LinearMap.liftBaseChange C t))
    (h' : Function.Bijective (LinearMap.liftBaseChange C t')) :
    Function.Bijective (LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) := by
  let e := LinearEquiv.ofBijective _ h
  let e' := LinearEquiv.ofBijective _ h'
  let F : C ⊗[A] (M ⊗[A] M') ≃ₗ[C] C :=
    TensorProduct.AlgebraTensorModule.distribBaseChange A C M M' ≪≫ₗ TensorProduct.congr e e' ≪≫ₗ
      TensorProduct.lid C C
  have hF : ∀ x, F x = LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y1 y2 h1 h2 => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), h1, h2]
      | tmul m m' =>
        simp [F, e, e', LinearMap.liftBaseChange_tmul, smul_eq_mul, mul_assoc]
  have : ⇑(LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) = F := by
    funext x
    exact (hF x).symm
  rw [this]
  exact F.bijective

theorem UpperTheory.rel_add_tensorProduct_of_rel :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' → P.Rel (z + z') (M ⊗[A] M') := by
  intro P A _ z z' M M' _ _ _ _ hz hz'
  obtain ⟨C, i1, i2, hff, het, w, g, t, w', g', t', T, T'⟩ := UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z' M M' hz hz'
  refine ⟨C, i1, i2, hff, het, w + w', g * g',
    (Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t', ?_⟩
  refine ⟨?_, ?_, ?_, cotangentAtUnit_tangentBijection t t' T.bij T'.bij⟩
  · rw [map_add (f := _), map_add (f := _), T.dw, T'.dw]
  · rw [P.un_mul, T.hg, T'.hg, map_add (f := _), map_add (f := _)]
    abel
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), add_smul, hx, hy, TensorProduct.tmul_add]
    | tmul m m' =>
      have h1 := T.ht m
      have h2 := T'.ht m'
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, Units.val_mul]
      rw [Algebra.smul_def] at h1 h2 ⊢
      rw [map_mul, show ∀ a b c d : C ⊗[A] C, a * b * (c * d) = (a * c) * (b * d) from
        fun a b c d => by ring, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsInvertibleModuleOfLocallyTrivialCocycle
open CategoryTheory TensorProduct UpperTheory.PicD

namespace UpperTheory.PicD

section
variable {A C : Type} [CommRing A] [CommRing C] [Algebra A C]

private theorem smul_eq_left_inclusion (b : C) (x : C ⊗[A] C) : b • x = i1 A C b * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, mul_add, hx, hy]
  | tmul p q => simp [smul_tmul']

private theorem act_eq (x : C ⊗[A] C) :
    GlobalTheory.FlatDescent.act A C C x = Algebra.TensorProduct.lmul' A x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul p q => simp

private theorem lTensor_theta (g x : C ⊗[A] C) :
    ((theta g).restrictScalars A).lTensor C x = c12 A C x * c23 A C g := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  | tmul p q =>
    simp [smul_eq_left_inclusion, Algebra.TensorProduct.tmul_mul_tmul]

private theorem lTensor_mk (x : C ⊗[A] C) :
    (TensorProduct.mk A C C 1).lTensor C x = c13 A C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul p q => simp

private theorem isDescentDatum_theta (g : C ⊗[A] C)
    (hc : c12 A C g * c23 A C g = c13 A C g) (hu : Algebra.TensorProduct.lmul' A g = (1 : C)) :
    GlobalTheory.FlatDescent.IsDescentDatum (theta g) := by
  constructor
  · intro b
    rw [theta_apply, map_smul, act_eq, hu]
    simp
  · intro b
    rw [theta_apply, lTensor_theta, lTensor_mk, smul_eq_left_inclusion, map_mul, map_mul, mul_assoc, hc]
    congr 1

end

end UpperTheory.PicD

theorem UpperTheory.exists_invertibleModule_of_locallyTrivial_cocycle :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)), P.LocEx z →
        ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M), Module.Invertible A M ∧ P.Rel z M := by
  intro P A _ z hz
  obtain ⟨C, _, _, hff, het, w, hw⟩ := hz
  have hdx : P.dd _ (P.r0 (i2 A C).toRingHom w - P.r0 (i1 A C).toRingHom w) = 0 := by
    have hcomp : (i2 A C).toRingHom.comp (algebraMap A C) = (i1 A C).toRingHom.comp (algebraMap A C) :=
      RingHom.ext fun a => ((i2 A C).commutes a).trans ((i1 A C).commutes a).symm
    rw [map_sub, P.diff_mapDegZero, P.diff_mapDegZero, hw, P.mapDegOne_comp, P.mapDegOne_comp, hcomp, sub_self]
  obtain ⟨g, hg⟩ := (P.dd_eq_zero _).1 hdx
  have q1 : (c12 A C).toRingHom.comp (i1 A C).toRingHom = (c13 A C).toRingHom.comp (i1 A C).toRingHom := by
    ext b <;> simp
  have q2 : (c12 A C).toRingHom.comp (i2 A C).toRingHom = (c23 A C).toRingHom.comp (i1 A C).toRingHom := by
    ext b <;> simp
  have q3 : (c13 A C).toRingHom.comp (i2 A C).toRingHom = (c23 A C).toRingHom.comp (i2 A C).toRingHom := by
    ext b <;> simp
  have hcoc : Units.map (c12 A C).toRingHom.toMonoidHom g * Units.map (c23 A C).toRingHom.toMonoidHom g =
      Units.map (c13 A C).toRingHom.toMonoidHom g := by
    apply P.un_injective
    rw [P.un_mul, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, ← P.mapDegZero_ofUnit, hg]
    simp only [map_sub, P.mapDegZero_comp]
    rw [q1, q2, q3]
    abel
  have hcount : Units.map (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.toMonoidHom g = 1 := by
    apply P.un_injective
    have hcomp : (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (i2 A C).toRingHom =
        (Algebra.TensorProduct.lmul' A (S := C)).toRingHom.comp (i1 A C).toRingHom := by
      ext b <;> simp
    rw [← P.mapDegZero_ofUnit, hg, P.un_one]
    simp only [map_sub, P.mapDegZero_comp]
    rw [hcomp, sub_self]
  have hdd : GlobalTheory.FlatDescent.IsDescentDatum (theta (g : C ⊗[A] C)) := by
    refine isDescentDatum_theta _ ?_ ?_
    · simpa using congrArg Units.val hcoc
    · simpa using congrArg Units.val hcount
  refine ⟨↥(Mg (g : C ⊗[A] C)), inferInstance, inferInstance, hdd.invertible_invariants, ?_⟩
  exact ⟨C, _, _, hff, het, w, g, (Mg (g : C ⊗[A] C)).subtype,
    ⟨hw, hg, fun m => GlobalTheory.FlatDescent.mem_invariants.1 m.2, hdd.bijective_extend⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TorsorRelSelfIffExistsCoboundary
open CategoryTheory TensorProduct UpperTheory.PicD

private theorem unit_of_surj {A C : Type} [CommRing A] [CommRing C] [Algebra A C] (t : A →ₗ[A] C)
    (hs : Function.Surjective (LinearMap.liftBaseChange C t)) : ∃ c : C, c * t 1 = 1 := by
  have key : ∀ x : C ⊗[A] A, ∃ c : C, LinearMap.liftBaseChange C t x = c * t 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a =>
      refine ⟨c * algebraMap A C a, ?_⟩
      rw [LinearMap.liftBaseChange_tmul]
      have e : t a = a • t 1 := by rw [← map_smul, smul_eq_mul, mul_one]
      rw [e]
      simp only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def, smul_eq_mul]
      ring
    | add x y hx hy =>
      obtain ⟨c1, h1⟩ := hx
      obtain ⟨c2, h2⟩ := hy
      exact ⟨c1 + c2, by rw [map_add (f := _), h1, h2, add_mul]⟩
  obtain ⟨x, hx⟩ := hs 1
  obtain ⟨c, hc⟩ := key x
  exact ⟨c, by rw [← hc, hx]⟩

private theorem tensor_inclusions_eq (A : Type) [CommRing A] : (i1 A A).toRingHom = (i2 A A).toRingHom := by
  ext a
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  calc a ⊗ₜ[A] (1 : A) = (a • (1 : A)) ⊗ₜ[A] (1 : A) := by rw [smul_eq_mul, mul_one]
    _ = (1 : A) ⊗ₜ[A] (a • (1 : A)) := TensorProduct.smul_tmul _ _ _
    _ = (1 : A) ⊗ₜ[A] a := by rw [smul_eq_mul, mul_one]

theorem UpperTheory.torsorRel_self_iff_exists_coboundary :
    ∀ (P : Data) (A : Type) [CommRing A] (z : P.S1.obj (CommRingCat.of A)),
        P.Rel z A ↔ ∃ y : P.S0.obj (CommRingCat.of A), P.dd A y = z := by
  intro P A _ z
  constructor
  · rintro ⟨C, _, _, _, _, w, g, t, hT⟩
    obtain ⟨c', hc'⟩ := unit_of_surj t hT.bij.2
    let u : Cˣ := ⟨t 1, c', by rw [mul_comm, hc'], hc'⟩
    have hgu : Units.map ((i1 A C).toRingHom : C →* C ⊗[A] C) u * g
        = Units.map ((i2 A C).toRingHom : C →* C ⊗[A] C) u := by
      ext
      have h := hT.ht 1
      rw [Algebra.smul_def] at h
      simpa using h
    have hun : P.un g = P.r0 (i2 A C).toRingHom (P.un u) - P.r0 (i1 A C).toRingHom (P.un u) := by
      rw [Data.mapDegZero_ofUnit, Data.mapDegZero_ofUnit, eq_sub_iff_add_eq, add_comm, ← Data.un_mul]
      congr 1
    have hg := hT.hg
    rw [hun] at hg
    obtain ⟨y, hy⟩ := P.glue A C (w - P.un u) (by
      change P.r0 (i1 A C).toRingHom (w - P.un u) = P.r0 (i2 A C).toRingHom (w - P.un u)
      rw [map_sub, map_sub, sub_eq_sub_iff_sub_eq_sub,
        ← neg_sub (P.r0 (i2 A C).toRingHom w), ← hg, neg_sub])
    have hy' : P.r0 (algebraMap A C) y = w - P.un u := hy
    refine ⟨y, P.sep A C ?_⟩
    change P.r1 (algebraMap A C) (P.dd A y) = P.r1 (algebraMap A C) z
    rw [← Data.diff_mapDegZero, hy', map_sub, hT.dw]
    have e : P.dd C (P.un u) = 0 := (Data.dd_eq_zero P _).mpr ⟨u, rfl⟩
    rw [e, sub_zero]
  · rintro ⟨y, rfl⟩
    refine ⟨A, inferInstance, Algebra.id A, inferInstance, inferInstance,
      P.r0 (algebraMap A A) y, 1, LinearMap.id, ?_⟩
    refine ⟨Data.diff_mapDegZero P _ y, ?_, ?_, ?_⟩
    · rw [Data.un_one, tensor_inclusions_eq, sub_self]
    · intro m
      have e := congrArg (fun f => f m) (tensor_inclusions_eq A)
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply] at e
      rw [LinearMap.id_apply, Units.val_one, Algebra.smul_def, mul_one]
      exact e
    · have e : ⇑(LinearMap.liftBaseChange A (LinearMap.id : A →ₗ[A] A)) = ⇑(TensorProduct.lid A A) := by
        funext x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      rw [e]
      exact (TensorProduct.lid A A).bijective
end

open CategoryTheory TensorProduct

namespace UpperTheory.PicD.Data
variable (P : Data)

theorem Rel.congr {A : Type} [CommRing A] {z : P.S1.obj (CommRingCat.of A)} {M M' : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : P.Rel z M) (e : M ≃ₗ[A] M') : P.Rel z M' := by
  obtain ⟨C, i1, i2, hff, het, w, g, t, ht⟩ := h
  refine ⟨C, i1, i2, hff, het, w, g, t ∘ₗ e.symm.toLinearMap, ?_⟩
  have hfun : ⇑(LinearMap.liftBaseChange C (t ∘ₗ e.symm.toLinearMap)) =
      ⇑(LinearMap.liftBaseChange C t) ∘ ⇑(LinearEquiv.baseChange A C M' M e.symm) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp [LinearMap.liftBaseChange_tmul]
    | add x y hx hy =>
      simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢
      rw [hx, hy]
  refine Triv.mk ht.dw ht.hg (fun m => ht.ht (e.symm m)) ?_
  rw [hfun]
  exact ht.bij.comp (LinearEquiv.bijective _)

theorem main (A : Type) [CommRing A] (Z : AddSubgroup (P.S1.obj (CommRingCat.of A))) (hZ : ∀ z ∈ Z, P.LocEx z) :
    ∃ φ : Z →+ Additive (CommRing.Pic A), ∀ z : Z, φ z = 0 ↔ ∃ y, P.dd A y = z.1 := by
  classical
  have hex : ∀ z : Z, ∃ N : CommRing.Pic A, P.Rel z.1 N := by
    intro z
    obtain ⟨M, i1, i2, hinv, hrel⟩ := UpperTheory.exists_invertibleModule_of_locallyTrivial_cocycle P A z.1 (hZ z.1 z.2)
    exact ⟨CommRing.Pic.mk A M, Rel.congr P hrel (CommRing.Pic.mk.linearEquiv A M).symm⟩
  choose f hf using hex
  have hone : ∀ z : Z, f z = 1 ↔ P.Rel z.1 A := by
    intro z
    rw [← CommRing.Pic.mk_eq_self (M := f z), CommRing.Pic.mk_eq_one_iff]
    constructor
    · rintro ⟨e⟩
      exact Rel.congr P (hf z) e
    · intro hA
      exact UpperTheory.invertibleModule_equiv_of_same_cocycle P A z.1 _ _ (hf z) hA
  have hmul : ∀ x y : Z, f (x + y) = f x * f y := by
    intro x y
    rw [CommRing.Pic.mul_eq_tensor]
    exact ((CommRing.Pic.mk_eq_iff).mpr
      (UpperTheory.invertibleModule_equiv_of_same_cocycle P A (x + y).1 _ _ (UpperTheory.rel_add_tensorProduct_of_rel P A x.1 y.1 _ _ (hf x) (hf y)) (hf (x + y)))).symm
  refine ⟨{ toFun := fun z => Additive.ofMul (f z), map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · show Additive.ofMul (f 0) = Additive.ofMul 1
    congr 1
    exact (hone 0).mpr ((UpperTheory.torsorRel_self_iff_exists_coboundary P A _).mpr ⟨0, by simp⟩)
  · intro x y
    show Additive.ofMul (f (x + y)) = Additive.ofMul (f x * f y)
    rw [hmul]
  · intro z
    show Additive.ofMul (f z) = 0 ↔ _
    rw [ofMul_eq_zero, hone, UpperTheory.torsorRel_self_iff_exists_coboundary]

end UpperTheory.PicD.Data
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace UpperTheory.PicD

private def SF (F : Shv ℤ) : CommRingCat.{0} ⥤ AddCommGrpCat.{1} :=
  Scheme.Spec.rightOp ⋙ F.obj ⋙ forget₂ (ModuleCat.{1} (ULift.{1} ℤ)) AddCommGrpCat.{1}

private def SFd {F G : Shv ℤ} (φ : F ⟶ G) : SF F ⟶ SF G :=
  Functor.whiskerLeft _ (Functor.whiskerRight φ.hom _)

private theorem res_res (F : Shv ℤ) {R S T : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T) (x : Sec F (Spec R)) :
    (Sec.res (Spec.map g) (Sec.res (Spec.map f) x) : Sec F (Spec T)) = Sec.res (Spec.map (f ≫ g)) x := by
  show (F.obj.map (Spec.map g).op).hom ((F.obj.map (Spec.map f).op).hom x) =
    (F.obj.map (Spec.map (f ≫ g)).op).hom x
  rw [Spec.map_comp, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

private def uS (R : CommRingCat.{0}) (u : Rˣ) : Sec Gm (Spec R) :=
  unitSec (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom u)

private theorem uS_mul (R : CommRingCat.{0}) (u v : Rˣ) : uS R (u * v) = uS R u + uS R v := by
  unfold uS
  rw [map_mul, unitSec_mul]

private theorem uS_res {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Rˣ) :
    Sec.res (Spec.map f) (uS R u) = uS S (Units.map f.hom.toMonoidHom u) := by
  unfold uS
  rw [unitSec_res]
  congr 1
  ext
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom (u : R) =
    (f ≫ (Scheme.ΓSpecIso S).inv).hom (u : R)
  rw [Scheme.ΓSpecIso_inv_naturality]

private theorem uS_bij (R : CommRingCat.{0}) : Function.Bijective (uS R) := by
  have h2 : Function.Bijective (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom) := by
    let e : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
    exact (Units.mapEquiv e.toMulEquiv).bijective
  have h1 : Function.Bijective (unitSec (U := Spec R)) := UpperTheory.unitSections_multiplicativeGroup_bijective_affine R
  exact h1.comp h2

private def PD : Data where
  S0 := SF ((res ℤ Gm).X 0)
  S1 := SF ((res ℤ Gm).X 1)
  d := SFd ((res ℤ Gm).d 0 1)
  ι R := AddMonoidHom.mk' (fun u => (Sec.map (resι ℤ Gm) (uS R u.toMul) : Sec ((res ℤ Gm).X 0) (Spec R)))
    (fun u v => by
      show (Sec.map (resι ℤ Gm) (uS R (u.toMul * v.toMul)) : Sec ((res ℤ Gm).X 0) (Spec R)) = _
      rw [uS_mul]
      exact map_add _ _ _)
  ι_nat {R R'} f u := by
    have h := congrArg (fun φ => φ.hom (uS R u)) ((resι ℤ Gm).hom.naturality (Spec.map f).op)
    refine Eq.trans h.symm ?_
    show (Sec.map (resι ℤ Gm) (Sec.res (Spec.map f) (uS R u)) : Sec ((res ℤ Gm).X 0) (Spec R')) = _
    rw [uS_res]
    rfl
  ι_inj R u v h := by
    have h1 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec R)).2.1 h
    exact Additive.toMul.injective ((uS_bij R).1 h1)
  d_eq_zero R w := by
    have h := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ Gm (Spec R)).1 w
    constructor
    · intro h0
      obtain ⟨a, ha⟩ := h.1 h0
      obtain ⟨u, rfl⟩ := (uS_bij R).2 a
      exact ⟨Additive.ofMul u, ha⟩
    · rintro ⟨u, hu⟩
      exact h.2 ⟨_, hu⟩
  glue A C _ _ _ _ _ w hw := (UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent ℤ ((res ℤ Gm).X 0) A C w hw).exists
  sep A C _ _ _ _ _ y y' hy := by
    refine (UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent ℤ ((res ℤ Gm).X 1) A C _ ?_).unique (y₁ := y) (y₂ := y') rfl hy.symm
    have hc : CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom (i1 A C).toRingHom =
        CommRingCat.ofHom (algebraMap A C) ≫ CommRingCat.ofHom (i2 A C).toRingHom := by
      ext a
      exact ((i1 A C).commutes a).trans ((i2 A C).commutes a).symm
    have hk : ∀ (y0 : Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of A))),
        (Sec.res (Spec.map (CommRingCat.ofHom (i1 A C).toRingHom))
          (Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y0) :
            Sec ((res ℤ Gm).X 1) (Spec (CommRingCat.of (TensorProduct A C C)))) =
        Sec.res (Spec.map (CommRingCat.ofHom (i2 A C).toRingHom))
          (Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y0) := fun y0 => by
      rw [res_res, res_res, hc]
    exact hk y

end UpperTheory.PicD

set_option maxHeartbeats 1000000 in
open UpperTheory.PicD in
theorem UpperTheory.exists_injective_h1_gm_to_pic :
    ∀ (A : Type) [CommRing A], ∃ φ : H ℤ (sp A) Gm 1 →+ Additive (CommRing.Pic A), Function.Injective φ := by
  intro A _
  let X := Spec (CommRingCat.of A)
  let Z : AddSubgroup (PD.S1.obj (CommRingCat.of A)) :=
    ((SFd ((res ℤ Gm).d 1 2)).app (CommRingCat.of A)).hom.ker
  have hZ : ∀ z ∈ Z, PD.LocEx z := fun z hz => UpperTheory.multiplicativeGroup_oneCocycle_etaleLocally_coboundary A z hz
  obtain ⟨ψ, hψ⟩ := PD.main A Z hZ
  have hT := GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff ℤ X (res ℤ Gm) 0 1 2 (by norm_num) (by norm_num)
  let e : Cocycle ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 → Sec ((res ℤ Gm).X 1) X :=
    fun α => ev (α : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1) 0 1 (by norm_num) X (𝟙 X)
  have hmem : ∀ α, e α ∈ Z := fun α => AddMonoidHom.mem_ker.mpr (hT.2 α).1
  let τ : Cocycle ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 →+ Z :=
    { toFun := fun α => ⟨e α, hmem α⟩
      map_zero' := by
        ext
        exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 (0 : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1)
          0 0 1 (by norm_num) X (𝟙 X)).2.2.1
      map_add' := by
        intro α β
        ext
        exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 (α : Cochain ((chains ℤ).obj (sp A)) (res ℤ Gm) 1)
          β 0 1 (by norm_num) X (𝟙 X)).1 }
  have hf : coboundaries ((chains ℤ).obj (sp A)) (res ℤ Gm) 1 ≤ (ψ.comp τ).ker := by
    intro α hα
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hψ]
    exact ((hT.2 α).2.mp ((CohomologyClass.mk_eq_zero_iff α).mpr hα))
  refine ⟨CohomologyClass.descAddMonoidHom (ψ.comp τ) hf, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective c
  rw [CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.comp_apply, hψ] at hc
  exact (hT.2 α).2.mpr hc
