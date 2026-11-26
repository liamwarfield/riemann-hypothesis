module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimits
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContFin

theorem term_preserves (N : CommRingCat.{0} ⥤ AbCx) (hN : PreservesFilteredColimitsOfSize.{0, 0} N) (n : ℤ) :
    PreservesFilteredColimitsOfSize.{0, 0} (term N n) := by
  constructor
  intro J _ _
  unfold term
  have : PreservesColimitsOfShape J N := hN.preserves_filtered_colimits J
  infer_instance

theorem cohomology_filteredColimit : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  intro N hN
  refine ⟨term_preserves N hN, ?_⟩
  intro J _ _ D c hc n
  have E : ∀ m : ℤ, (∀ x : ((N).obj c.pt).X m, ∃ j y, ((N).map (c.ι.app j)).f m y = x) ∧
      ∀ j (y : ((N).obj (D.obj j)).X m), ((N).map (c.ι.app j)).f m y = 0 → ∃ (k : J) (f : j ⟶ k), ((N).map (D.map f)).f m y = 0 :=
    fun m => ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N m)).mp (term_preserves N hN m)) J D c hc

  have nat : ∀ {a b : CommRingCat.{0}} (g : a ⟶ b) (p q : ℤ) (x : ((N).obj a).X p),
      ((N).map g).f q (((N).obj a).d p q x) = ((N).obj b).d p q (((N).map g).f p x) := by
    intro a b g p q x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ((N).map g).comm]
  have mapf : ∀ {j k : J} (f : j ⟶ k) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (c.ι.app k)).f m (((N).map (D.map f)).f m x) = ((N).map (c.ι.app j)).f m x := by
    intro j k f m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, c.w f]
  have mapcomp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      ((N).map (D.map (f ≫ g))).f m x = ((N).map (D.map g)).f m (((N).map (D.map f)).f m x) := by
    intro j k l f g m x
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← D.map_comp]
  constructor
  · intro z hz
    obtain ⟨j, w, hw⟩ := (E n).1 z
    have h1 : ((N).map (c.ι.app j)).f (n + 1) (((N).obj (D.obj j)).d n (n + 1) w) = 0 := by
      rw [nat, hw]
      exact hz
    obtain ⟨k, f, hf⟩ := (E (n + 1)).2 j _ h1
    refine ⟨k, ((N).map (D.map f)).f n w, 0, ?_, ?_⟩
    · rw [← nat, hf]
    · rw [mapf, hw, map_zero, add_zero]
  · intro j w _ ⟨y, hy⟩
    obtain ⟨j', y', rfl⟩ := (E (n - 1)).1 y
    let k := IsFiltered.max j j'
    let fa : j ⟶ k := IsFiltered.leftToMax j j'
    let fb : j' ⟶ k := IsFiltered.rightToMax j j'
    set u := ((N).map (D.map fa)).f n w - ((N).obj (D.obj k)).d (n - 1) n (((N).map (D.map fb)).f (n - 1) y') with hu
    have h0 : ((N).map (c.ι.app k)).f n u = 0 := by
      rw [hu, map_sub, mapf, ← nat, mapf, hy, nat]
      exact sub_self _
    obtain ⟨l, g, hg⟩ := (E n).2 k u h0
    refine ⟨l, fa ≫ g, ((N).map (D.map g)).f (n - 1) (((N).map (D.map fb)).f (n - 1) y'), ?_⟩
    rw [hu, map_sub, sub_eq_zero] at hg
    rw [mapcomp, hg, nat]

end GlobalTheory.EtC.ContFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimitsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexCohomology_commutes_with_filteredColimits : ∀ (N : CommRingCat.{0} ⥤ AbCx), PreservesFilteredColimitsOfSize.{0, 0} N → (∀ n, PreservesFilteredColimitsOfSize.{0, 0} (term N n)) ∧ (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (exact GlobalTheory.EtC.ContFin.cohomology_filteredColimit) | (intros; apply GlobalTheory.EtC.ContFin.cohomology_filteredColimit  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlat
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem preservesColimitsOfShape_spec_yoneda (J : Type) [SmallCategory J] :
    PreservesColimitsOfShape J (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op) := by
  have h1 : PreservesColimitsOfShape J Scheme.Spec.{0}.rightOp := preservesColimitsOfShape_rightOp J _
  have h2 : PreservesColimitsOfShape J (yoneda (C := Scheme.{0})).op := preservesColimitsOfShape_op J _
  infer_instance

theorem hyp_spec_coAug_of_etFF : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  intro R _ A B g hg k
  obtain ⟨h1, h2⟩ := (etFF_basic.2.1 A B g).1 hg
  exact GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective R CommRingCat.{0} (Scheme.Spec.{0}.rightOp ⋙ (yoneda (C := Scheme.{0})).op)
    (fun n => preservesColimitsOfShape_spec_yoneda _) A B g
    (locallySurjective_etale_section_baseChange.1 _ _ (Spec.map g) h1 h2)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveResolutionOfEtaleFaithfullyFlatStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat : ∀ (R : Type) [CommRing R] (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Hyp R (Scheme.Spec.rightOp ⋙ sch.op) (coAug g) := by
  first | (exact @GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (exact GlobalTheory.EtC.hyp_spec_coAug_of_etFF) | (intros; apply GlobalTheory.EtC.hyp_spec_coAug_of_etFF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocycles
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCZero

noncomputable def clHom (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    Cocycle ((chains R).obj E) (res R F) 0 →+ H R E F 0 :=
  AddMonoidHom.mk' (fun c => CohomologyClass.mk c) (fun a b => CohomologyClass.mk_add a b)

theorem cochain_neg_one_eq_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (β : Cochain ((chains R).obj E) (res R F) (-1)) : β = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : 0 < p
  · exact (GlobalTheory.EtC.HCElements.chains_X_isZero R E p hp).eq_of_src _ _
  · exact (GlobalTheory.EtC.HCElements.res_X_isZero R F q (by omega)).eq_of_tgt _ _

theorem clHom_bijective (R : Type) [CommRing R] (F : Shv R) (E : Spc) : Function.Bijective (clHom R F E) := by
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h0 : CohomologyClass.mk (a - b) = 0 := by
      rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 hab
    rw [CohomologyClass.mk_eq_zero_iff] at h0
    obtain ⟨m, hm, β, hβ⟩ := h0
    obtain rfl : m = -1 := by omega
    rw [cochain_neg_one_eq_zero R F E β, δ_zero] at hβ
    rw [← sub_eq_zero]
    exact Cocycle.ext (by simpa using hβ.symm)
  · obtain ⟨c, rfl⟩ := x.mk_surjective
    exact ⟨c, rfl⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  intro R _ F
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  let cE : ∀ X : Scheme.{0}, Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 ≃+ H R (sch.obj X) F 0 :=
    fun X => AddEquiv.ofBijective (clHom R F (sch.obj X)) (clHom_bijective R F (sch.obj X))
  let φ : ∀ X : Scheme.{0}, Sec F X →+ Cochain ((chains R).obj (sch.obj X)) (res R F) 0 :=
    fun X => (AddMonoidHom.mk' (fun c : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0 => c.1) (fun _ _ => rfl)).comp
      ((cE X).symm.toAddMonoidHom.comp (e X).toAddMonoidHom)
  have hφ : ∀ X s, φ X s = ((cE X).symm (e X s)).1 := fun _ _ => rfl
  refine ⟨{ app := fun U => AddCommGrpCat.ofHom (φ U.unop), naturality := ?_ }, fun U => ⟨?_, fun z => ⟨?_, ?_⟩⟩⟩
  · intro U V f
    ext x
    change φ V.unop ((F.obj.map f).hom x) = ((HC R F).map (sch.map f.unop).op).f 0 (φ U.unop x)
    set c := (cE U.unop).symm (e U.unop x) with hc
    have key : (cE V.unop) (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) =
        e V.unop ((F.obj.map f).hom x) := by
      have h1 := he f.unop x
      have h2 : pull R (sch.map f.unop) F 0 (cE U.unop c) =
          CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (sch.map f.unop))) c (zero_add 0)) := rfl
      rw [hc, AddEquiv.apply_symm_apply] at h2
      rw [h2] at h1
      exact h1
    rw [hφ, hφ, ← key, AddEquiv.symm_apply_apply]
    rfl
  · intro a b hab
    change φ U.unop a = φ U.unop b at hab
    rw [hφ, hφ] at hab
    exact (e U.unop).injective ((cE U.unop).symm.injective (Subtype.ext hab))
  · intro hz
    refine ⟨(e U.unop).symm (cE U.unop (Cocycle.mk z (0 + 1) rfl hz)), ?_⟩
    change φ U.unop _ = z
    rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, rfl⟩
    change δ 0 (0 + 1) (φ U.unop x) = 0
    rw [hφ]
    exact ((cE U.unop).symm (e U.unop x)).2

end GlobalTheory.EtC.HCZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsEquivDegreeZeroCocyclesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ ι : F.obj ⋙ forget₂ _ AddCommGrpCat.{1} ⟶ sch.op ⋙ HC R F ⋙ HomologicalComplex.eval _ _ 0, ∀ U : Scheme.{0}ᵒᵖ, Function.Injective (ι.app U) ∧ ∀ z : ((HC R F).obj (op (sch.obj U.unop))).X 0, ((HC R F).obj (op (sch.obj U.unop))).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app U x = z := by
  first | exact @GlobalTheory.EtC.HCZero.main | exact GlobalTheory.EtC.HCZero.main | (intros; apply GlobalTheory.EtC.HCZero.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRings
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FiniteTypeApprox

theorem nat_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ε.naturality, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]

theorem comm_apply {K L : AbCx} (φ : K ⟶ L) (i j : ℤ) (x : K.X i) :
    φ.f j (K.d i j x) = L.d i j (φ.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← φ.comm, ConcreteCategory.comp_apply]

theorem map_comp_apply (N : CommRingCat.{0} ⥤ AbCx) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (x : (N.obj A).X n) : (N.map (f ≫ g)).f n x = (N.map g).f n ((N.map f).f n x) := by
  rw [Functor.map_comp, HomologicalComplex.comp_f, ConcreteCategory.comp_apply]

theorem map_id_apply (N : CommRingCat.{0} ⥤ AbCx) (A : CommRingCat.{0}) (n : ℤ) (x : (N.obj A).X n) :
    (N.map (𝟙 A)).f n x = x := by
  simp

theorem inj_of_iso {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] {x y : X} (h : f x = f y) : x = y :=
  (ConcreteCategory.bijective_of_isIso f).1 h

theorem inv_apply_eq {X Y : AddCommGrpCat.{1}} (f : X ⟶ Y) [IsIso f] (y : Y) : f (inv f y) = y := by
  rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

theorem eq_zero_of_isZero {X : AddCommGrpCat.{1}} (h : IsZero X) (x : X) : x = 0 := by
  have := (AddCommGrpCat.isZero_iff_subsingleton.1 h)
  exact Subsingleton.elim _ _

theorem isIso_f {K L : AbCx} (φ : K ⟶ L) [IsIso φ] (n : ℤ) : IsIso (φ.f n) :=
  (inferInstance : IsIso ((HomologicalComplex.eval _ _ n).map φ))

theorem locInj_of_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  intro N M ε F0 ι hF0 hι hMneg hMpos hN hε
  intro n A c hc hy
  obtain ⟨y, hy⟩ := hy
  obtain ⟨J, _, _, D, ιD, ⟨hcol⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨-, hN2⟩ := GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN
  obtain ⟨⟨hmul, hcob, -⟩, -, hftB⟩ := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties
  obtain ⟨j, w, y', hw, hwc⟩ := (hN2 J D (Cocone.mk A ιD) hcol n).1 c hc
  change (N.map (ιD.app j)).f n w = c + (N.obj A).d (n - 1) n y' at hwc
  have hwv : (M.obj (D.obj j)).d n (n + 1) ((ε.app (D.obj j)).f n w) = 0 := by
    rw [← comm_apply, hw, map_zero]

  have fin : (N.map (ιD.app j)).f n w = 0 → ∃ (V : CommRingCat.{0}) (g : A ⟶ V), EtFF g ∧
      ∃ b : (N.obj V).X (n - 1), (N.obj V).d (n - 1) n b = (N.map g).f n c := by
    intro h0
    refine ⟨A, 𝟙 A, MorphismProperty.id_mem EtFF A, -y', ?_⟩
    rw [map_id_apply, map_neg]
    rw [h0] at hwc
    exact (eq_neg_of_add_eq_zero_left hwc.symm).symm
  rcases lt_trichotomy n 0 with hn | hn | hn
  ·
    apply fin
    haveI := hε _ (hft j)
    haveI := isIso_f (ε.app (D.obj j)) n
    have : w = 0 := inj_of_iso ((ε.app (D.obj j)).f n)
      ((eq_zero_of_isZero (hMneg n hn _) _).trans (map_zero _).symm)
    rw [this, map_zero]
  ·
    subst hn
    apply fin
    have hy0 : y = 0 := eq_zero_of_isZero (hMneg _ (by norm_num) _) y
    rw [hy0, map_zero] at hy
    obtain ⟨x0, hx0⟩ := ((hι (D.obj j)).2 _).1 hwv
    have hιnat : ∀ {B C : CommRingCat.{0}} (g : B ⟶ C) (x : F0.obj B),
        ι.app C (F0.map g x) = (M.map g).f 0 (ι.app B x) := by
      intro B C g x
      rw [← ConcreteCategory.comp_apply, ι.naturality, ConcreteCategory.comp_apply]
      rfl
    have hdie : F0.map (ιD.app j) x0 = 0 := by
      apply (hι A).1
      rw [hιnat, hx0, ← nat_apply, hwc, map_add (f := _), hy, comm_apply,
        eq_zero_of_isZero (hMneg _ (by norm_num) _) ((ε.app A).f (0 - 1) y'), map_zero, add_zero]
      exact (map_zero _).symm
    obtain ⟨-, hF0inj⟩ := (GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A ιD) hcol
    obtain ⟨k, f, hk⟩ := hF0inj j x0 hdie
    haveI := hε _ (hft k)
    haveI := isIso_f (ε.app (D.obj k)) 0
    have hwk : (N.map (D.map f)).f 0 w = 0 := by
      apply inj_of_iso ((ε.app (D.obj k)).f 0)
      rw [nat_apply, ← hx0, ← hιnat, hk, map_zero, map_zero]
    have hcw : ιD.app j = D.map f ≫ ιD.app k := by
      have := ιD.naturality f
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      exact this.symm
    rw [hcw, map_comp_apply, hwk, map_zero]
  ·
    obtain ⟨B0, g0, hg0, y0, hy0⟩ := hMpos n hn _ _ hwv
    have hB0 := hftB _ _ g0 hg0 (hft j)
    haveI := hε _ hB0
    haveI := isIso_f (ε.app B0) n
    haveI := isIso_f (ε.app B0) (n - 1)
    set b0 := inv ((ε.app B0).f (n - 1)) y0 with hb0
    have hdb0 : (N.obj B0).d (n - 1) n b0 = (N.map g0).f n w := by
      apply inj_of_iso ((ε.app B0).f n)
      rw [comm_apply, hb0, inv_apply_eq, hy0, nat_apply]
    haveI := hcob
    have hg : EtFF (pushout.inr g0 (ιD.app j)) := MorphismProperty.pushout_inr _ _ hg0
    refine ⟨pushout g0 (ιD.app j), pushout.inr g0 (ιD.app j), hg,
      (N.map (pushout.inl g0 (ιD.app j))).f (n - 1) b0 - (N.map (pushout.inr g0 (ιD.app j))).f (n - 1) y', ?_⟩
    rw [map_sub, ← comm_apply, ← comm_apply, hdb0, ← map_comp_apply, pushout.condition, map_comp_apply, hwc,
      map_add]
    exact add_sub_cancel_right _ _
end GlobalTheory.EtC.FiniteTypeApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRingsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocInj EtFF ε := by
  first | (exact @GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (exact GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType) | (intros; apply GlobalTheory.EtC.FiniteTypeApprox.locInj_of_finiteType  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximation
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LocSurjFT

theorem etFF_id (A : CommRingCat.{0}) : EtFF (𝟙 A) := by
  refine ⟨?_, ?_⟩
  · change (algebraMap A A).Etale
    exact RingHom.etale_algebraMap.2 inferInstance
  · change (algebraMap A A).FaithfullyFlat
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

theorem locSurj_of_iso_on_finiteType : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  intro N M ε F0 ι hF0 hι hneg hpos _hN hiso n A z hz
  rcases lt_trichotomy n 0 with hn | rfl | hn
  ·
    haveI := AddCommGrpCat.subsingleton_of_isZero (hneg n hn A)
    refine ⟨A, 𝟙 A, etFF_id A, 0, 0, by simp, Subsingleton.elim _ _⟩
  ·
    obtain ⟨x, rfl⟩ := ((hι A).2 z).1 hz
    obtain ⟨J, _, _, D, κ, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    obtain ⟨j, x0, hx0⟩ := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} F0).1 hF0 J D (Cocone.mk A κ) hc).1 x
    haveI := hiso (D.obj j) (hft j)
    set z0 : (M.obj (D.obj j)).X 0 := ι.app (D.obj j) x0 with hz0
    set c0 : (N.obj (D.obj j)).X 0 := (inv (ε.app (D.obj j))).f 0 z0 with hc0
    have hεc0 : (ε.app (D.obj j)).f 0 c0 = z0 := by
      have := congrArg (fun h => (h.f 0).hom z0) (IsIso.inv_hom_id (ε.app (D.obj j)))
      simpa [hc0] using this
    have hdz0 : (M.obj (D.obj j)).d 0 (0 + 1) z0 = 0 := ((hι (D.obj j)).2 z0).2 ⟨x0, rfl⟩
    have hdc0 : (N.obj (D.obj j)).d 0 (0 + 1) c0 = 0 := by
      have := congrArg (fun h => h.hom z0) ((inv (ε.app (D.obj j))).comm 0 (0 + 1))
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
      rw [hc0, this, hdz0, map_zero]
    have h2 : (M.map (κ.app j)).f 0 z0 = ι.app A x := by
      have := ConcreteCategory.congr_hom (ι.naturality (κ.app j)) x0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
      rw [hz0, ← hx0]
      exact this.symm
    clear_value c0 z0
    refine ⟨A, 𝟙 A, etFF_id A, (N.map (κ.app j)).f 0 c0, 0, ?_, ?_⟩
    · have := ConcreteCategory.congr_hom ((N.map (κ.app j)).comm 0 (0 + 1)) c0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hdc0, map_zero] at this
      exact this
    · have h1 := ConcreteCategory.congr_hom (congrArg (fun h => h.f 0) (ε.naturality (κ.app j))) c0
      simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at h1
      have h1' : (ε.app A).f 0 ((N.map (κ.app j)).f 0 c0) = (M.map (κ.app j)).f 0 ((ε.app (D.obj j)).f 0 c0) := h1
      rw [h1', hεc0, h2]
      simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, map_zero, add_zero]
      rfl
  ·
    obtain ⟨B, g, hg, y, hy⟩ := hpos n hn A z hz
    refine ⟨B, g, hg, 0, -y, by simp, ?_⟩
    rw [map_neg, hy]
    simp

end GlobalTheory.EtC.LocSurjFT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximationStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → PreservesFilteredColimitsOfSize.{0, 0} N → (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) → LocSurj EtFF ε := by
  first | (exact @GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (exact GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType) | (intros; apply GlobalTheory.EtC.LocSurjFT.locSurj_of_iso_on_finiteType  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeIntHomFilteredColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem finiteType_int_hom_filteredColimit :
    ∀ (A : CommRingCat.{0}), Algebra.FiniteType ℤ A → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
      (∀ φ : A ⟶ c.pt, ∃ (j : J) (ψ : A ⟶ D.obj j), ψ ≫ c.ι.app j = φ) ∧
      ∀ (j : J) (ψ ψ' : A ⟶ D.obj j), ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j →
        ∃ (k : J) (f : j ⟶ k), ψ ≫ D.map f = ψ' ≫ D.map f := by
  intro A hA J _ _ D c hc
  let R : CommRingCat.{0} := CommRingCat.of ℤ
  let f : R ⟶ A := CommRingCat.ofHom (Int.castRingHom A)
  let α : (Functor.const J).obj R ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom (D.obj i))
      naturality := by
        intro i j g
        ext1
        exact RingHom.ext_int _ _ }
  have hfp : f.hom.FinitePresentation := by
    have h1 : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.mp hA
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FinitePresentation
    rw [e]
    exact h1
  have hft : f.hom.FiniteType := by
    have e : f.hom.toAlgebra = (inferInstance : Algebra ℤ A) := Subsingleton.elim _ _
    unfold RingHom.FiniteType
    rw [e]
    exact hA
  have hR : ∀ {X : CommRingCat.{0}} (u v : R ⟶ X), u = v := by
    intro X u v
    ext1
    exact RingHom.ext_int _ _
  refine ⟨fun φ => ?_, fun j ψ ψ' h => ?_⟩
  · obtain ⟨i, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R D α f c hc
      hfp φ (fun i => hR _ _)
    exact ⟨i, g', hg'.symm⟩
  · obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R D α f c hc
      hft.essFiniteType ψ (hR _ _) ψ' (hR _ _) h
    refine ⟨IsFiltered.coeq hik hjk, hik ≫ IsFiltered.coeqHom hik hjk, ?_⟩
    calc ψ ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk)
        = (ψ ≫ D.map hik) ≫ D.map (IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = (ψ' ≫ D.map hjk) ≫ D.map (IsFiltered.coeqHom hik hjk) := by rw [e]
      _ = ψ' ≫ D.map (hjk ≫ IsFiltered.coeqHom hik hjk) := by
          rw [D.map_comp, Category.assoc]
      _ = ψ' ≫ D.map (hik ≫ IsFiltered.coeqHom hik hjk) := by
          rw [IsFiltered.coeq_condition]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FinExt

def finTypeZ : ObjectProperty CommRingCat.{0} := fun A => Algebra.FiniteType ℤ A

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  (E : finTypeZ.ι.LeftExtension G)

lemma comp_eq_of_fac {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
    {c : Cocone D} (hc : IsColimit c) (s : Cocone (D ⋙ E.right))
    (X : finTypeZ.FullSubcategory) {j j' : J} (ψ : finTypeZ.ι.obj X ⟶ D.obj j)
    (ψ' : finTypeZ.ι.obj X ⟶ D.obj j') (h : ψ ≫ c.ι.app j = ψ' ≫ c.ι.app j') :
    E.hom.app X ≫ E.right.map ψ ≫ s.ι.app j = E.hom.app X ≫ E.right.map ψ' ≫ s.ι.app j' := by
  obtain ⟨k, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j j'
  have hk : (ψ ≫ D.map a) ≫ c.ι.app k = (ψ' ≫ D.map b) ≫ c.ι.app k := by
    simpa only [Category.assoc, Cocone.w] using h
  obtain ⟨l, f, hf⟩ := (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj X) X.property J D c hc).2 k _ _ hk
  have e1 : s.ι.app j = E.right.map (D.map (a ≫ f)) ≫ s.ι.app l := (s.w (a ≫ f)).symm
  have e2 : s.ι.app j' = E.right.map (D.map (b ≫ f)) ≫ s.ι.app l := (s.w (b ≫ f)).symm
  rw [e1, e2, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 3
  simpa only [Functor.map_comp, Category.assoc] using hf

end

section
variable {H : Type*} [Category H] {G : finTypeZ.FullSubcategory ⥤ H}
  {E : finTypeZ.ι.LeftExtension G}

theorem preservesFilteredColimits_of_isPointwiseLeftKanExtension
    (hE : E.IsPointwiseLeftKanExtension) : PreservesFilteredColimitsOfSize.{0, 0} E.right := by
  refine ⟨fun J _ _ => ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  have hfac := fun (g : CostructuredArrow finTypeZ.ι c.pt) =>
    (GlobalTheory.finiteType_int_hom_filteredColimit (finTypeZ.ι.obj g.left) g.left.property J D c hc).1 g.hom
  choose j ψ hψ using hfac
  let t : ∀ s : Cocone (D ⋙ E.right), Cocone (CostructuredArrow.proj finTypeZ.ι c.pt ⋙ G) :=
    fun s =>
    { pt := s.pt
      ι := { app := fun g => E.hom.app g.left ≫ E.right.map (ψ g) ≫ s.ι.app (j g)
             naturality := by
               intro g g' f
               have hn := E.hom.naturality f.left
               dsimp at hn ⊢
               simp only [Category.comp_id]
               change G.map f.left ≫ _ = _
               erw [reassoc_of% hn, ← Functor.map_comp_assoc]
               exact comp_eq_of_fac E hc s g.left _ _
                 (by rw [Category.assoc, hψ g', hψ g]; exact CostructuredArrow.w f) } }
  have ht : ∀ (s : Cocone (D ⋙ E.right)) (X : finTypeZ.FullSubcategory) (φ : finTypeZ.ι.obj X ⟶ c.pt),
      E.hom.app X ≫ E.right.map φ ≫ (hE c.pt).desc (t s) =
        E.hom.app X ≫ E.right.map (ψ (CostructuredArrow.mk φ)) ≫ s.ι.app (j (CostructuredArrow.mk φ)) := by
    intro s X φ
    have := (hE c.pt).fac (t s) (CostructuredArrow.mk φ)
    exact (Category.assoc _ _ _).symm.trans this
  exact
  { desc := fun s => (hE c.pt).desc (t s)
    fac := fun s k => by
      apply (hE (D.obj k)).hom_ext'
      intro X φ
      have h1 := ht s X (φ ≫ c.ι.app k)
      simp only [Functor.mapCocone_ι_app]
      erw [← Functor.map_comp_assoc, h1]
      exact comp_eq_of_fac E hc s X _ _ (hψ _)
    uniq := fun s m hm => by
      apply (hE c.pt).hom_ext'
      intro X φ
      rw [ht s X φ]
      have h2 := hψ (CostructuredArrow.mk φ)
      dsimp at h2
      conv_lhs => rw [← h2, Functor.map_comp, Category.assoc]
      have h3 := hm (j (CostructuredArrow.mk φ))
      simp only [Functor.mapCocone_ι_app] at h3
      rw [h3] }

end

theorem exists_preservesFilteredColimits_isIso :
    ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜),
      ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧
        (∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A)) := by
  intro 𝒜 _ _ M
  haveI : HasColimitsOfSize.{0, 1} 𝒜 := hasColimitsOfSizeShrink.{0, 1, 1, 1} 𝒜
  haveI : finTypeZ.ι.HasPointwiseLeftKanExtension (finTypeZ.ι ⋙ M) := fun _ => inferInstance
  let E := Functor.LeftExtension.mk _ (finTypeZ.ι.pointwiseLeftKanExtensionUnit (finTypeZ.ι ⋙ M))
  have hE : E.IsPointwiseLeftKanExtension :=
    finTypeZ.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _
  let φ := hE.homFrom (Functor.LeftExtension.mk M (𝟙 _))
  refine ⟨E.right, φ.right, preservesFilteredColimits_of_isPointwiseLeftKanExtension hE,
    fun A hA => ?_⟩
  let X : finTypeZ.FullSubcategory := ⟨A, hA⟩
  have h1 : IsIso (E.hom.app X) := (hE (finTypeZ.ι.obj X)).isIso_hom_app
  have h2 : E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X) = 𝟙 _ := by
    have := congr_app (StructuredArrow.w φ) X
    simpa using this
  have h4 : IsIso (E.hom.app X ≫ φ.right.app (finTypeZ.ι.obj X)) := by
    rw [h2]; exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  exact IsIso.of_isIso_comp_left (E.hom.app X) (φ.right.app (finTypeZ.ι.obj X))

end GlobalTheory.FinExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteTypeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType : ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜), ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧ ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A) := by
  first
  | exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | (intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem hom_d_apply {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) :
    φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, HomologicalComplex.Hom.comm]

theorem nat_f_apply {N M : CommRingCat.{0} ⥤ AbCx} (ε : N ⟶ M) {A B : CommRingCat.{0}} (g : A ⟶ B) (n : ℤ)
    (x : (N.obj A).X n) : (ε.app B).f n ((N.map g).f n x) = (M.map g).f n ((ε.app A).f n x) := by
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f, ε.naturality]

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contH_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro N M ε hε hN J _ _ D c hc n
  obtain ⟨hN1, hN2⟩ := hN J D c hc n
  have nat : ∀ (j : J) (m : ℤ) (x : ((N).obj (D.obj j)).X m),
      (ε.app c.pt).f m ((N.map (c.ι.app j)).f m x) = (M.map (c.ι.app j)).f m ((ε.app (D.obj j)).f m x) :=
    fun j m x => nat_f_apply ε (B := c.pt) (c.ι.app j) m x
  have dN : ∀ (j : J) (m m' : ℤ) (x : ((N).obj (D.obj j)).X m),
      (N.map (c.ι.app j)).f m' (((N).obj (D.obj j)).d m m' x) = ((N).obj c.pt).d m m' ((N.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (N).obj c.pt) (N.map (c.ι.app j)) m m' x
  have dM : ∀ (j : J) (m m' : ℤ) (x : ((M).obj (D.obj j)).X m),
      (M.map (c.ι.app j)).f m' (((M).obj (D.obj j)).d m m' x) = ((M).obj c.pt).d m m' ((M.map (c.ι.app j)).f m x) :=
    fun j m m' x => hom_d_apply (D := (M).obj c.pt) (M.map (c.ι.app j)) m m' x
  refine ⟨fun z hz => ?_, fun j w hw ⟨y, hy⟩ => ?_⟩
  · obtain ⟨c', y1, hc', h1⟩ := (hε c.pt).1 n z hz
    obtain ⟨j, w, y2, hw, h2⟩ := hN1 c' hc'
    refine ⟨j, (ε.app (D.obj j)).f n w, y1 + (ε.app c.pt).f (n - 1) y2, ?_, ?_⟩
    · rw [← hom_d_apply, hw, map_zero]
    · rw [← nat, h2, map_add (f := _), h1, map_add (f := _), hom_d_apply]
      abel
  · obtain ⟨c1, y1, hc1, h1⟩ := (hε (D.obj j)).1 n w hw
    have hcz : ((N).obj c.pt).d n (n + 1) ((N.map (c.ι.app j)).f n c1) = 0 := by
      rw [← dN, hc1, map_zero]
    obtain ⟨b, hb⟩ := (hε c.pt).2 n _ hcz ⟨y + (show ((M).obj c.pt).X (n - 1) from (M.map (c.ι.app j)).f (n - 1) y1), by
      rw [nat, h1, map_add (f := _), hy, map_add (f := _), dM]⟩
    obtain ⟨k, f, y2, h2⟩ := hN2 j c1 hc1 ⟨b, hb.symm⟩
    refine ⟨k, f, (ε.app (D.obj k)).f (n - 1) y2 - (M.map (D.map f)).f (n - 1) y1, ?_⟩
    have e1 : w = (ε.app (D.obj j)).f n c1 - ((M).obj (D.obj j)).d (n - 1) n y1 := by
      rw [h1]; abel
    rw [e1, map_sub, map_sub, ← nat_f_apply, h2, hom_d_apply, hom_d_apply]

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filteredColimitCohomology_transport_quasiIso : ∀ (N M : CommRingCat.{0} ⥤ AbCx) (ε : N ⟶ M), (∀ A, SurjH (ε.app A) ∧ InjH (ε.app A)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((N).obj c.pt).X n, ((N).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((N).obj (D.obj j)).X n) (y : ((N).obj c.pt).X (n - 1)), ((N).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((N).map (c.ι.app j)).f n w = z + ((N).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((N).obj (D.obj j)).X n), ((N).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((N).obj c.pt).X (n - 1), ((N).map (c.ι.app j)).f n w = ((N).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((N).obj (D.obj k)).X (n - 1)), ((N).map (D.map f)).f n w = ((N).obj (D.obj k)).d (n - 1) n y) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first | (exact @GlobalTheory.EtC.contH_transport_quasiIso) | (exact GlobalTheory.EtC.contH_transport_quasiIso) | (intros; apply GlobalTheory.EtC.contH_transport_quasiIso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescent
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContAlg

theorem cohomology_filteredColimit_of_descent :
    ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro M F0 ι hF0 hι hneg hloc hdesc
  obtain ⟨N, ε, hN, hiso⟩ := GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType AbCx M
  have hterm := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).1
  have hcontN := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).2
  haveI : EtFF.IsStableUnderComposition := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.1.1.toIsStableUnderComposition

  have hNneg : ∀ n : ℤ, n < 0 → ∀ A, IsZero ((N.obj A).X n) := by
    intro n hn A
    obtain ⟨J, _, _, D, ιA, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    have hel := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N n)).1 (hterm n)) J D _ hc
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro x y
    suffices h : ∀ x : (N.obj A).X n, x = 0 by rw [h x, h y]
    intro x
    obtain ⟨j, w, rfl⟩ := hel.1 x
    have hz : IsZero ((N.obj (D.obj j)).X n) := by
      haveI := hiso (D.obj j) (hft j)
      have e : (N.obj (D.obj j)).X n ≅ (M.obj (D.obj j)).X n :=
        (HomologicalComplex.eval _ _ n).mapIso (asIso (ε.app (D.obj j)))
      exact (hneg n hn (D.obj j)).of_iso e
    have : w = 0 := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hz
      exact @Subsingleton.elim _ hz _ _
    subst this
    exact map_zero _
  have hqis := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent CommRingCat.{0} EtFF N M ε
    ⟨0, fun n hn U => ⟨hNneg n hn U, hneg n hn U⟩⟩
    (GlobalTheory.T.coveringsRefine_of_cechConerve_property CommRingCat.{0} EtFF _ (fun A B g hg n =>
      ⟨GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits (term N n) (term M n) (Functor.whiskerRight ε (HomologicalComplex.eval _ _ n)) (hterm n)
        (fun A' hA' => by
          haveI := hiso A' hA'
          change IsIso ((HomologicalComplex.eval _ _ n).map (ε.app A'))
          infer_instance)
        (fun A' B' g' hg' => hdesc A' B' g' hg' n) A B g hg,
       hdesc A B g hg n⟩))
    (GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation N M ε F0 ι hF0 hι hneg hloc hN hiso)
    (GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings N M ε F0 ι hF0 hι hneg hloc hN hiso)
  exact GlobalTheory.T.filteredColimitCohomology_transport_quasiIso N M ε hqis hcontN

end GlobalTheory.EtC.ContAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFilteredColimitOfEtaleDescentStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent : ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent
  | exact GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent
  | (intros; apply GlobalTheory.EtC.ContAlg.cohomology_filteredColimit_of_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RingCont

abbrev MC (R : Type) [CommRing R] (F : Shv R) : CommRingCat.{0} ⥤ AbCx := Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F

theorem locVan (R : Type) [CommRing R] (F : Shv R) : ∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : ((MC R F).obj A).X n),
    ((MC R F).obj A).d n (n + 1) z = 0 →
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : ((MC R F).obj B).X (n - 1),
      ((MC R F).obj B).d (n - 1) n y = ((MC R F).map g).f n z := by
  intro n hn A z hz
  obtain ⟨_, cl, -, -, hcl0, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover R (Spec A) F n hn (cl (sch.obj (Spec A)) n z hz)
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection A Y f hfe hfs
  refine ⟨B, g, hg, ?_⟩
  obtain ⟨h', hh'⟩ := hpull (sch.obj (Spec B)) (sch.obj (Spec A)) (sch.map (Spec.map g)) n z hz
  have h0 : pull R (sch.map (Spec.map g)) F n (cl (sch.obj (Spec A)) n z hz) = 0 := by
    rw [← hhf, Functor.map_comp, pull_comp, hx, map_zero]
  rw [hh', hcl0] at h0
  obtain ⟨y, hy⟩ := h0
  exact ⟨y, hy.symm⟩

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨ι, hι⟩ := GlobalTheory.T.etaleSheafSections_equiv_degreeZeroCocycles R F
  have hF0 : PreservesFilteredColimitsOfSize.{0, 0} (onRings F ⋙ forget₂ _ AddCommGrpCat.{1}) :=
    ((GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} R) (onRings F)).1.1 hF)
  exact GlobalTheory.T.cohomology_filteredColimit_of_etaleDescent (MC R F) (onRings F ⋙ forget₂ _ AddCommGrpCat.{1})
    (Functor.whiskerLeft Scheme.Spec.rightOp ι) hF0
    (fun A => hι (op (Spec A)))
    (fun n hn A => (GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F).1 _ n hn)
    (locVan R F)
    (fun A B g hg n => GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F CommRingCat.{0} (Scheme.Spec.rightOp ⋙ sch.op) A _ (coAug g)
      (GlobalTheory.T.cechConerve_resolution_of_etaleFaithfullyFlat R A B g hg) n)
    J D c hc n

end GlobalTheory.EtC.RingCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCohomologyComplexContinuousFilteredColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X n, (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 ∧ (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = z + (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).X n), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).X (n - 1), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (c.ι.app j)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).X (n - 1)), (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).map (D.map f)).f n w = (((Scheme.Spec.rightOp ⋙ sch.op ⋙ HC R F)).obj (D.obj k)).d (n - 1) n y) := by
  first
  | exact @GlobalTheory.EtC.RingCont.main
  | exact GlobalTheory.EtC.RingCont.main
  | (intros; apply GlobalTheory.EtC.RingCont.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.RingContH

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨_, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit R F hF J D c hc n
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj (sp c.pt) n x
    obtain ⟨j, w, y, hw, hwy⟩ := h1 z hz
    refine ⟨j, cl _ n w hw, ?_⟩
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, heq]
    exact ⟨y, hwy⟩
  · obtain ⟨w, hw, rfl⟩ := hsurj (sp (D.obj j)) n y
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, hzero] at hy
    obtain ⟨k, f, y', hy'⟩ := h2 j w hw hy
    refine ⟨k, f, ?_⟩
    obtain ⟨h', hh'⟩ := hpull (sp (D.obj k)) (sp (D.obj j)) (spMap (D.map f).hom) n w hw
    rw [hh', hzero]
    exact ⟨y', hy'⟩

end GlobalTheory.EtC.RingContH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.RingContH.main
  | exact GlobalTheory.EtC.RingContH.main
  | (intros; apply GlobalTheory.EtC.RingContH.main <;> assumption)
end
