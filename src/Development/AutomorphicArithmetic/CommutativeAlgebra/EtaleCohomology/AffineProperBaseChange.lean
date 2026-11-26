module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.HenselianIdempotents
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.EquivalenceQuasiAffine
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.CechLevels
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SpecAbsolutelyIntegrallyClosedCohomology

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.stupidPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.stupidPf

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.ofHom_comp]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  exact Cochain.id_comp _

theorem cpull_iso {R : Type} [CommRing R] {K L : Cx R} (e : K ≅ L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, e.inv_hom_id, cpull_id]
  · rw [← cpull_comp, e.hom_inv_id, cpull_id]

def trunc0 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ∃ (eK : tr K 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (K.X (-((0 : ℕ) : ℤ))))
    (eL : tr L 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (L.X (-((0 : ℕ) : ℤ)))),
    trm g 0 ≫ eL.hom = eK.hom ≫ (CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))

def incl : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0] {K L : Cx R} (g : K ⟶ L) (N : ℕ),
  ∃ (ιK : tr K N ⟶ K) (ιL : tr L N ⟶ L), trm g N ≫ ιL = ιK ≫ g ∧
    ∀ n : ℤ, n + 1 ≤ (N : ℤ) → Function.Bijective (cpull ιK I n) ∧ Function.Bijective (cpull ιL I n)

theorem stupid_of (h0 : trunc0) (hI : incl) : LateralTheory.E.CxDescPf.stupid := by
  intro R _ I _ _ K L _ _ g
  refine ⟨fun hb j => ?_, fun m N hN hG => ?_⟩
  · obtain ⟨eK, eL, hsq⟩ := h0 R g
    have hc : (cpull (trm g 0) I j) ∘ (cpull eL.hom I j) =
        (cpull eK.hom I j) ∘ (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j) := by
      funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    have hb' : Function.Bijective ((cpull (trm g 0) I j) ∘ (cpull eL.hom I j)) := by
      rw [hc]; exact (cpull_iso eK I j).comp (hb j)
    exact (Function.Bijective.of_comp_iff _ (cpull_iso eL I j)).1 hb'
  · obtain ⟨ιK, ιL, hsq, hbij⟩ := hI R I g N
    have hc : ∀ j, (cpull ιK I j) ∘ (cpull g I j) = (cpull (trm g N) I j) ∘ (cpull ιL I j) := by
      intro j; funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    refine ⟨fun j hj => ?_, ?_⟩
    · have hb' : Function.Bijective ((cpull ιK I j) ∘ (cpull g I j)) := by
        rw [hc]; exact (hG.1 j hj).comp (hbij j (by omega)).2
      exact (Function.Bijective.of_comp_iff' (hbij j (by omega)).1 _).1 hb'
    · have hi : Function.Injective ((cpull ιK I m) ∘ (cpull g I m)) := by
        rw [hc]; exact hG.2.comp (hbij m hN).2.1
      exact Function.Injective.of_comp hi

end LateralTheory.E.stupidPf
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.DescentSteps
section -- merged from Development.EtaleCohomology.EtaleSheaves.longPfSes
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.longPfSes
open LateralTheory.E.CxDescPf

variable {R : Type} [CommRing R]

theorem eF (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (ComplexShape.embeddingUpIntGE (-(N : ℤ))).f (i + N).toNat = i := by
  show -(N : ℤ) + (((i + N).toNat : ℕ) : ℤ) = i; omega

def trX (K : Cx R) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (tr K N).X i ≅ K.X i := K.stupidTruncXIso _ (eF N i h)

theorem trZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i < -(N : ℤ)) : IsZero ((tr K N).X i) :=
  K.isZero_stupidTrunc_X _ i (by intro k; show -(N : ℤ) + (k : ℤ) ≠ i; omega)

theorem tr_d (K : Cx R) (N : ℕ) (i j : ℤ) (hi : -(N : ℤ) ≤ i) (hj : -(N : ℤ) ≤ j) :
    (tr K N).d i j = (trX K N i hi).hom ≫ K.d i j ≫ (trX K N j hj).inv := by
  have h1 := eF N i hi
  have h2 := eF N j hj
  simp only [trX, HomologicalComplex.stupidTruncXIso, tr, HomologicalComplex.stupidTrunc, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rw [HomologicalComplex.extend_d_eq _ _ h1 h2, HomologicalComplex.restriction_d_eq _ _ h1 h2]
  simp [HomologicalComplex.restrictionXIso]

theorem trm_f {K L : Cx R} (g : K ⟶ L) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) :
    (trm g N).f i = (trX K N i h).hom ≫ g.f i ≫ (trX L N i h).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom g _ (eF N i h)

abbrev Sg (K : Cx R) (N : ℕ) : Cx R :=
  (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ)))

theorem SgZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i ≠ -((N + 1 : ℕ) : ℤ)) : IsZero ((Sg K N).X i) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

def ιf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K N).X i ⟶ (tr K (N + 1)).X i :=
  if h : -(N : ℤ) ≤ i then (trX K N i h).hom ≫ (trX K (N + 1) i (by push_cast; omega)).inv else 0

def ι (K : Cx R) (N : ℕ) : tr K N ⟶ tr K (N + 1) where
  f := ιf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h : -(N : ℤ) ≤ i
    · have hj : -(N : ℤ) ≤ j := by omega
      rw [ιf, dite_eq_left h, ιf, dite_eq_left hj, tr_d K N i j h hj, tr_d K (N + 1) i j (by push_cast; omega) (by push_cast; omega)]
      simp
    · rw [ιf, dite_eq_right h, zero_comp]
      exact (trZ K N i (by omega)).eq_of_src _ _

def pf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K (N + 1)).X i ⟶ (Sg K N).X i :=
  if h : i = -((N + 1 : ℕ) : ℤ) then
    (trX K (N + 1) i (by omega)).hom ≫ eqToHom (by rw [h]) ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) _ (K.X (-((N + 1 : ℕ) : ℤ))) i h).inv
  else 0

def pp (K : Cx R) (N : ℕ) : tr K (N + 1) ⟶ Sg K N where
  f := pf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hj : j = -((N + 1 : ℕ) : ℤ)
    · exact (trZ K (N + 1) i (by push_cast at hj ⊢; omega)).eq_of_src _ _
    · exact (SgZ K N j hj).eq_of_tgt _ _

theorem ιp (K : Cx R) (N : ℕ) : ι K N ≫ pp K N = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  by_cases h : -(N : ℤ) ≤ i
  · exact (SgZ K N i (by push_cast; omega)).eq_of_tgt _ _
  · show ιf K N i ≫ _ = 0
    rw [ιf, dite_eq_right h, zero_comp]

theorem nat1 {K L : Cx R} (g : K ⟶ L) (N : ℕ) : ι K N ≫ trm g (N + 1) = trm g N ≫ ι L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : -(N : ℤ) ≤ i
  · show ιf K N i ≫ _ = _ ≫ ιf L N i
    rw [ιf, dite_eq_left h, ιf, dite_eq_left h, trm_f g N i h, trm_f g (N + 1) i (by push_cast; omega)]
    simp
  · exact (trZ K N i (by omega)).eq_of_src _ _

theorem nat2 {K L : Cx R} (g : K ⟶ L) (N : ℕ) :
    pp K N ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) =
      trm g (N + 1) ≫ pp L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : i = -((N + 1 : ℕ) : ℤ)
  · subst h
    show pf K N _ ≫ _ = _ ≫ pf L N _
    rw [pf, dite_eq_left rfl, pf, dite_eq_left rfl, trm_f g (N + 1) _ (by omega)]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleObjXSelf]
  · exact (SgZ L N i h).eq_of_tgt _ _

theorem sesK (K : Cx R) (N : ℕ) : (ShortComplex.mk (ι K N) (pp K N) (ιp K N)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h : -(N : ℤ) ≤ i
  · have hz : IsZero ((Sg K N).X i) := SgZ K N i (by push_cast; omega)
    have : IsIso (ιf K N i) := by rw [ιf, dite_eq_left h]; infer_instance
    have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).f := this
    refine ShortComplex.ShortExact.mk' ?_ inferInstance (hz.epi _)
    rw [ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)]
    infer_instance
  · by_cases h' : i = -((N + 1 : ℕ) : ℤ)
    · have hz : IsZero ((tr K N).X i) := trZ K N i (by omega)
      have : IsIso (pf K N i) := by subst h'; rw [pf, dite_eq_left rfl]; exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))
      have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).g := this
      refine ShortComplex.ShortExact.mk' ?_ (hz.mono _) inferInstance
      rw [ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)]
      infer_instance
    · have hz2 : IsZero ((tr K (N + 1)).X i) := trZ K (N + 1) i (by push_cast at h' ⊢; omega)
      have hz1 : IsZero ((tr K N).X i) := trZ K N i (by omega)
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz2) (hz1.mono _) ((SgZ K N i h').epi _)

theorem ses : LateralTheory.E.longPf.Ses := fun _ _ N =>
  ⟨fun K => ι K N, fun K => pp K N, fun K => ιp K N, fun K => sesK K N, fun g => ⟨nat1 g N, nat2 g N⟩⟩

theorem long_of (hLES : LateralTheory.E.longPf.LES) : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPf.long_of hLES ses

end LateralTheory.E.longPfSes
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CochainComplexSingleFunctorZeroMapFZero
noncomputable section
open CategoryTheory Limits ZeroObject

namespace LateralTheory.E.trunc0Pf

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

lemma isZero_tr (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE 0)).X i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · apply HomologicalComplex.isZero_stupidTrunc_X
    intro j; simp; omega
  · exact (K.isZero_of_isStrictlyLE 0 i h).of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := i.toNat) (by simp; omega))

lemma cochainComplex_singleFunctor_zero_map_f_zero {A B : C} (f : A ⟶ B) :
    ((CochainComplex.singleFunctor C 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
  HomologicalComplex.single_map_f_self _ _ f

def eIso (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE 0) ≅ (CochainComplex.singleFunctor C 0).obj (K.X 0) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => if h : i = 0 then (by
        subst h
        exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp) ≪≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).symm)
      else (isZero_tr K i h).iso (HomologicalComplex.isZero_single_obj_X _ 0 _ i h))
    (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      by_cases hj : j = 0
      · exact (isZero_tr K i (by omega)).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_tgt _ _)

lemma stupidTruncGEZeroIsoSingle_hom_f_zero (K : CochainComplex C ℤ) [K.IsStrictlyLE 0] :
    (eIso K).hom.f 0 = (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) (by simp)).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)).inv := by
  simp [eIso]

lemma nat {K L : CochainComplex C ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE 0) ≫ (eIso L).hom =
      (eIso K).hom ≫ (CochainComplex.singleFunctor C 0).map (g.f 0) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst h
    simp only [HomologicalComplex.comp_f, stupidTruncGEZeroIsoSingle_hom_f_zero, cochainComplex_singleFunctor_zero_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc]
    erw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X _ 0 _ i h).eq_of_tgt _ _

theorem trunc0_of : LateralTheory.E.stupidPf.trunc0 := by
  intro R _ K L _ _ g
  exact ⟨eIso K, eIso L, nat g⟩

end LateralTheory.E.trunc0Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.inclPf
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.inclPf

universe v u

set_option linter.dupNamespace false in
abbrev E (M : ℤ) := ComplexShape.embeddingUpIntGE M

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (M : ℤ)

lemma xiso_indep {i j : ℕ} {p : ℤ} (hi : (E M).f i = p) (hj : (E M).f j = p) :
    K.stupidTruncXIso (E M) hi = K.stupidTruncXIso (E M) hj := by
  obtain rfl : i = j := (E M).injective_f (hi.trans hj.symm)
  rfl

lemma trd (i j : ℕ) :
    (K.stupidTrunc (E M)).d ((E M).f i) ((E M).f j) ≫ (K.stupidTruncXIso (E M) (i := j) rfl).hom =
      (K.stupidTruncXIso (E M) (i := i) rfl).hom ≫ K.d ((E M).f i) ((E M).f j) := by
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    HomologicalComplex.extend_d_eq _ _ rfl rfl, HomologicalComplex.restriction]


open Classical in
def iotaf (p : ℤ) : (K.stupidTrunc (E M)).X p ⟶ K.X p :=
  if h : ∃ i, (E M).f i = p then (K.stupidTruncXIso (E M) h.choose_spec).hom else 0

lemma iotaf_eq (i : ℕ) : iotaf K M ((E M).f i) = (K.stupidTruncXIso (E M) (i := i) rfl).hom := by
  have h : ∃ j, (E M).f j = (E M).f i := ⟨i, rfl⟩
  rw [iotaf, dite_eq_left h, xiso_indep K M h.choose_spec rfl]

lemma stupidTruncation_GE_isZero_below_bound (p : ℤ) (hp : p < M) : IsZero ((K.stupidTrunc (E M)).X p) :=
  HomologicalComplex.isZero_stupidTrunc_X _ _ _ (fun i h => by simp [E] at h; omega)

lemma mem (p : ℤ) (hp : M ≤ p) : (E M).f (p - M).toNat = p := by simp [E]; omega

def iota : K.stupidTrunc (E M) ⟶ K where
  f := iotaf K M
  comm' p q hpq := by
    simp only [ComplexShape.up_Rel] at hpq
    by_cases hp : M ≤ p
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, (E M).f j = q := ⟨i + 1, by simp [E] at hpq ⊢; omega⟩
      rw [iotaf_eq, iotaf_eq]
      exact (trd K M i j).symm
    · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _

lemma iota_iso (p : ℤ) (hp : M ≤ p) : IsIso ((iota K M).f p) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
  show IsIso (iotaf K M _)
  rw [iotaf_eq]; infer_instance

lemma iota_nat {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    HomologicalComplex.stupidTruncMap g (E M) ≫ iota L M = iota K M ≫ g := by
  ext p
  simp only [HomologicalComplex.comp_f]
  by_cases hp : M ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (E M).f i = p := ⟨_, mem M p hp⟩
    show _ ≫ iotaf L M _ = iotaf K M _ ≫ _
    rw [iotaf_eq, iotaf_eq]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom _ _ rfl
  · exact (stupidTruncation_GE_isZero_below_bound K M p (by omega)).eq_of_src _ _
end

section
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {A B I : CochainComplex C ℤ} (φ : A ⟶ B) (M : ℤ)

def P (m : ℤ) (c : Cochain B I m) : Cochain A I m := (Cochain.ofHom φ).comp c (zero_add m)

lemma precomp_injective [I.IsStrictlyGE 0] (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (m : ℤ) (hm : m + M ≤ 0) :
    Function.Injective (P (I := I) φ m) := by
  intro c c' h
  ext p q hpq
  by_cases hp : M ≤ p
  · have := hiso p hp
    have h' := congrArg (fun x : Cochain A I m => x.v p q hpq) h
    simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h'
    exact (cancel_epi _).1 h'
  · exact (I.isZero_of_isStrictlyGE 0 q (by omega)).eq_of_tgt _ _

lemma precomp_surjective₂ (hiso : ∀ p, M ≤ p → IsIso (φ.f p)) (hz : ∀ p, p < M → IsZero (A.X p)) (m : ℤ) :
    Function.Surjective (P (I := I) φ m) := by
  intro d
  refine ⟨Cochain.mk (fun p q hpq => if h : M ≤ p then (haveI := hiso p h; inv (φ.f p)) ≫ d.v p q hpq else 0), ?_⟩
  ext p q hpq
  simp only [P, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  by_cases hp : M ≤ p
  · rw [dite_eq_left hp]; simp
  · exact (hz p (by omega)).eq_of_src _ _
end

section
variable {R : Type} [CommRing R] {A B I : Cx R} (φ : A ⟶ B)

lemma cpull_mk (n : ℤ) (z : Cocycle B I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (Cocycle.mk (P φ n z) (n + 1) rfl
      (by simp [P, Cocycle.δ_eq_zero])) := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1

lemma cpull_bij [I.IsStrictlyGE 0] (M : ℤ) (hiso : ∀ p, M ≤ p → IsIso (φ.f p))
    (hz : ∀ p, p < M → IsZero (A.X p)) (n : ℤ) (hn : n + 1 + M ≤ 0) :
    Function.Bijective (cpull φ I n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := precomp_surjective₂ φ M hiso hz (n - 1) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨β', precomp_injective φ M hiso n (by omega) ?_⟩
    rw [Cocycle.mk_coe] at hβ
    rw [← hβ, P, P, δ_ofHom_comp]
  · intro x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨c, hc⟩ := precomp_surjective₂ φ M hiso hz n (z : Cochain A I n)
    have hδ : δ n (n + 1) c = 0 := by
      apply precomp_injective φ M hiso (n + 1) (by omega)
      have : P φ (n + 1) (δ n (n + 1) c) = δ n (n + 1) (P φ n c) := by simp [P]
      rw [this, hc, Cocycle.δ_eq_zero]; simp [P]
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hδ), ?_⟩
    rw [cpull_mk]
    congr 1
    apply Cocycle.ext
    simp only [Cocycle.mk_coe]
    exact hc
end

theorem incl_of : LateralTheory.E.stupidPf.incl := by
  intro R _ I _ K L g N
  refine ⟨iota K (-(N : ℤ)), iota L (-(N : ℤ)), iota_nat _ g, fun n hn => ⟨?_, ?_⟩⟩
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso K _) (stupidTruncation_GE_isZero_below_bound K _) n (by omega)
  · exact cpull_bij _ (-(N : ℤ)) (iota_iso L _) (stupidTruncation_GE_isZero_below_bound L _) n (by omega)

end LateralTheory.E.inclPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.shiftPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.shiftPf

theorem conj_iff {α β γ δ : Type*} (F : α → β) (G : γ → δ) (e1 : α ≃ γ) (e2 : β ≃ δ)
    (h : ∀ x, G (e1 x) = e2 (F x)) :
    (Function.Bijective F ↔ Function.Bijective G) ∧ (Function.Injective F ↔ Function.Injective G) := by
  have hG : G = e2 ∘ F ∘ e1.symm := funext fun y => by simpa using h (e1.symm y)
  have hF : F = e2.symm ∘ G ∘ e1 := funext fun x => by simp [h]
  refine ⟨⟨fun hb => ?_, fun hb => ?_⟩, ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rw [hG]; exact e2.bijective.comp (hb.comp e1.symm.bijective)
  · rw [hF]; exact e2.symm.bijective.comp (hb.comp e1.bijective)
  · rw [hG]; exact e2.injective.comp (hb.comp e1.symm.injective)
  · rw [hF]; exact e2.symm.injective.comp (hb.comp e1.injective)

section Cat
variable {C : Type*} [Category C]

abbrev pre {X X' : C} (u : X ⟶ X') (Y : C) : (X' ⟶ Y) → (X ⟶ Y) := fun h => u ≫ h

theorem pre_conj {W W' X X' : C} (u' : W ⟶ W') (u : X ⟶ X') (a : W ≅ X) (b : W' ≅ X')
    (h : u' ≫ b.hom = a.hom ≫ u) (Y : C) :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u' Y)) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u' Y)) :=
  conj_iff _ _ ((Iso.homCongr b.symm (Iso.refl Y))) ((Iso.homCongr a.symm (Iso.refl Y))) (fun x => by
    simp only [pre, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, h, Category.assoc])

theorem pre_target {X X' Y Y' : C} (u : X ⟶ X') (e : Y ≅ Y') :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u Y')) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u Y')) :=
  conj_iff _ _ (Iso.homCongr (Iso.refl X') e) (Iso.homCongr (Iso.refl X) e) (fun x => by
    simp [pre, Iso.homCongr_apply])

theorem pre_shift [HasShift C ℤ] {X X' : C} (u : X ⟶ X') (p : ℤ) (Y : C) :
    (Function.Bijective (pre (u⟦p⟧') Y) ↔ Function.Bijective (pre u (Y⟦-p⟧))) ∧
      (Function.Injective (pre (u⟦p⟧') Y) ↔ Function.Injective (pre u (Y⟦-p⟧))) :=
  conj_iff _ _ ((shiftEquiv C p).toAdjunction.homEquiv X' Y) ((shiftEquiv C p).toAdjunction.homEquiv X Y) (fun x => by
    simp only [pre]
    exact ((shiftEquiv C p).toAdjunction.homEquiv_naturality_left u x).symm)

end Cat

variable {R : Type} [CommRing R]

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

theorem toHom_cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    CohomologyClass.toHom (cpull f I n x) = (Qt R).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  rw [cpull, cpre_mk, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_precomp]
  congr 2

theorem cpull_iff {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull f I n) ↔ Function.Bijective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) ∧
      (Function.Injective (cpull f I n) ↔ Function.Injective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) :=
  conj_iff _ _ (CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).toEquiv
    (CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)).toEquiv (fun x => by
      simp [toHom_cpull])

theorem main_iff (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (P j : ℤ) :
    (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) ∧
    (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) := by
  let s0 := (CochainComplex.singleFunctor (Shv R) 0).map φ
  let sp := (CochainComplex.singleFunctor (Shv R) (-P)).map φ
  let E := (CochainComplex.singleFunctors (Shv R)).shiftIso P (-P) 0 (by omega)
  obtain ⟨b1, i1⟩ := cpull_iff sp I j
  obtain ⟨b2, i2⟩ := pre_conj ((Qt R).map sp) ((Qt R).map (s0⟦P⟧'))
    ((Qt R).mapIso (E.symm.app A)) ((Qt R).mapIso (E.symm.app B)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact E.inv.naturality φ) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b3, i3⟩ := pre_conj ((Qt R).map (s0⟦P⟧')) (((Qt R).map s0)⟦P⟧')
    (((Qt R).commShiftIso P).app _) (((Qt R).commShiftIso P).app _)
    (((Qt R).commShiftIso P).hom.naturality s0) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b4, i4⟩ := pre_shift ((Qt R).map s0) P ((Qt R).obj (I⟦j⟧))
  obtain ⟨b5, i5⟩ := pre_target ((Qt R).map s0)
    ((((Qt R).commShiftIso (-P)).symm.app (I⟦j⟧)) ≪≫
      (Qt R).mapIso ((shiftFunctorAdd' (Cx R) j (-P) (j - P) (by omega)).symm.app I))
  obtain ⟨b6, i6⟩ := cpull_iff s0 I (j - P)
  exact ⟨b6.trans (b5.symm.trans (b4.symm.trans (b3.trans (b2.trans b1.symm)))),
    i6.trans (i5.symm.trans (i4.symm.trans (i3.trans (i2.trans i1.symm))))⟩

theorem shift_of : LateralTheory.E.CxDescPf.shift := by
  intro R _ I A B φ p j
  obtain ⟨hb, hi⟩ := main_iff I φ (p : ℤ) j
  exact ⟨hb.1, hi.1⟩

end LateralTheory.E.shiftPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DescentInduction.Bounds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.E.DescStepPf

theorem bounds_le (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 := by
  show CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0
  infer_instance

theorem Bounds_holds : Bounds := fun R _ F E =>
  ⟨bounds_le R E, by unfold res; infer_instance,
    fun m => by unfold res; exact InjectiveResolution.instInjectiveXIntCochainComplex (injectiveResolution F) m⟩

theorem etale_descent_induction_of_levelwise_identity_and_complex_descent (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep :=
  DescStep_of Bounds_holds hL hX

end LateralTheory.E.DescStepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LevelIdentPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LevelIdentPf

def FreeSingleHomotopyEquivDiscreteChains : Prop := ∀ (R : Type) [CommRing R], ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)),
  (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧
  ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) =
    (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp _ x _) = CohomologyClass.mk (zcomp _ x _)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, n.negOnePow • (Cochain.ofHomotopy h).comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp _ _ (by omega) 0 (n + 1) n (by omega) (by omega) (by omega), δ_ofHomotopy]
  simp [zcomp, Cocycle.δ_eq_zero, Cochain.sub_comp, smul_smul, Int.units_mul_self]

theorem cpull_iso_bij {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, cpull_homotopy e.homotopyInvHomId, cpull_id]
  · rw [← cpull_comp, cpull_homotopy e.homotopyHomInvId, cpull_id]

theorem sq_iff {A B C D : Type*} {a : B → D} {b : A → B} {c : C → D} {d : A → C}
    (w : ∀ x, a (b x) = c (d x)) (ha : Function.Bijective a) (hd : Function.Bijective d) :
    (Function.Bijective b ↔ Function.Bijective c) ∧ (Function.Injective b ↔ Function.Injective c) := by
  have w' : a ∘ b = c ∘ d := funext w
  obtain ⟨d', hd1, hd2⟩ := Function.bijective_iff_has_inverse.1 hd
  have hc : c = a ∘ b ∘ d' := by
    funext y; simp only [Function.comp_apply, w, hd2 y]
  have hd'b : Function.Bijective d' := Function.bijective_iff_has_inverse.2 ⟨d, hd2, hd1⟩
  refine ⟨⟨fun hb => hc ▸ ha.comp (hb.comp hd'b), fun hc' => ?_⟩, ⟨fun hb => hc ▸ ha.1.comp (hb.comp hd'b.1), fun hc' => ?_⟩⟩
  · have : a ∘ b = c ∘ d := w'
    have hab : Function.Bijective (a ∘ b) := this ▸ hc'.comp hd
    obtain ⟨a', ha1, ha2⟩ := Function.bijective_iff_has_inverse.1 ha
    have : b = a' ∘ (a ∘ b) := by funext x; simp [ha1 (b x)]
    rw [this]; exact (Function.bijective_iff_has_inverse.2 ⟨a, ha2, ha1⟩).comp hab
  · intro x y hxy
    apply hd.1; apply hc'
    rw [← w, ← w, hxy]

theorem chains_f {E E' : Spc} (f : E ⟶ E') (n : ℕ) : ((chains R).map f).f (-(n : ℤ)) =
    (chainsXIso R E n).hom ≫ (free R).map (f.app (op (SimplexCategory.mk n))) ≫ (chainsXIso R E' n).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := n) rfl]
  rfl

theorem cpull_isoHom_bij {K L : Cx R} (i : K ≅ L) (I : Cx R) (n : ℤ) : Function.Bijective (cpull i.hom I n) :=
  cpull_iso_bij (HomotopyEquiv.ofIso i) I n

theorem pull_eq {E E' : Spc} (f : E ⟶ E') (F : Shv R) (n : ℤ) (x : H R E' F n) :
    pull R f F n x = cpull ((chains R).map f) (res R F) n x := rfl

theorem LevelIdent_of (hS : FreeSingleHomotopyEquivDiscreteChains) : LateralTheory.E.DescStepPf.LevelIdent := by
  intro R _ F E E' f p j
  obtain ⟨e, -, he⟩ := hS R
  let S := CochainComplex.singleFunctor (Shv R) 0
  let g := f.app (op (SimplexCategory.mk p))
  have sq1 : S.map (((chains R).map f).f (-(p : ℤ))) ≫ S.map (chainsXIso R E' p).hom =
      S.map (chainsXIso R E p).hom ≫ S.map ((free R).map g) := by
    rw [← S.map_comp, ← S.map_comp, chains_f]; simp [g]
  have w1 : ∀ x, cpull (S.map (chainsXIso R E p).hom) (res R F) j (cpull (S.map ((free R).map g)) (res R F) j x) =
      cpull (S.map (((chains R).map f).f (-(p : ℤ)))) (res R F) j (cpull (S.map (chainsXIso R E' p).hom) (res R F) j x) := by
    intro x; rw [← cpull_comp, ← cpull_comp, sq1]
  have w2 : ∀ x, cpull (e (E.obj (op (SimplexCategory.mk p)))).hom (res R F) j (pull R (disc.map g) F j x) =
      cpull (S.map ((free R).map g)) (res R F) j (cpull (e (E'.obj (op (SimplexCategory.mk p)))).hom (res R F) j x) := by
    intro x; rw [pull_eq, ← cpull_comp, ← cpull_comp, he g]
  obtain ⟨b1, i1⟩ := sq_iff w1 (cpull_isoHom_bij (S.mapIso (chainsXIso R E p)) _ _)
    (cpull_isoHom_bij (S.mapIso (chainsXIso R E' p)) _ _)
  obtain ⟨b2, i2⟩ := sq_iff w2 (cpull_iso_bij _ _ _) (cpull_iso_bij _ _ _)
  exact ⟨b2.trans b1, i2.trans i1⟩

end LateralTheory.E.LevelIdentPf
end
end

namespace UpperTheory.Et.EtaleDescentEtaleAxioms

theorem a0 : LateralTheory.E.LevelIdentPf.FreeSingleHomotopyEquivDiscreteChains := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf
theorem a1 : LateralTheory.E.DescStepPf.LevelIdent := LateralTheory.E.LevelIdentPf.LevelIdent_of a0
theorem a2 : LateralTheory.E.stupidPf.trunc0 := LateralTheory.E.trunc0Pf.trunc0_of
theorem a3 : LateralTheory.E.stupidPf.incl := LateralTheory.E.inclPf.incl_of
theorem a4 : LateralTheory.E.CxDescPf.stupid := LateralTheory.E.stupidPf.stupid_of a2 a3
theorem a5 : LateralTheory.E.longPf.LES := GlobalTheory.T.hypercohomology_longExact_first_of_injective
theorem a6 : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPfSes.long_of a5
theorem a7 : LateralTheory.E.CxDescPf.shift := LateralTheory.E.shiftPf.shift_of
theorem a8 : LateralTheory.E.DescStepPf.CxDesc := LateralTheory.E.CxDescPf.CxDesc_of a4 a6 a7
theorem a9 : LateralTheory.E.t_E1Cut.DescStep := LateralTheory.E.DescStepPf.etale_descent_induction_of_levelwise_identity_and_complex_descent a1 a8

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.DescStep := a9

end UpperTheory.Et.EtaleDescentEtaleAxioms
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.EtaleCovers
section -- merged from Development.EtaleCohomology.EtaleSheaves.CoverIntegralClosure
noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.CoverIntegralClosure

theorem inj_sub (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) :=
  Subtype.val_injective

theorem aic_integralClosure (P : Type) [CommRing P] [IsDomain P] :
    AIC (integralClosure P (AlgebraicClosure (FractionRing P))) := by
  intro p hp hdeg
  have hdeg' : (p.map (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P)))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (inj_sub P)]
    intro h
    rw [Polynomial.degree_eq_natDegree hp.ne_zero] at h
    norm_cast at h
    omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg'
  have hTa : IsIntegral (integralClosure P (AlgebraicClosure (FractionRing P))) a :=
    ⟨p, hp, by simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha⟩
  have hPa : IsIntegral P a := isIntegral_trans a hTa
  have ha' : Polynomial.eval₂ (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) a p = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha
  refine ⟨⟨a, hPa⟩, ?_⟩
  apply inj_sub P
  rw [map_zero, ← Polynomial.eval₂_at_apply]
  exact ha'

theorem inj_P (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap P (integralClosure P (AlgebraicClosure (FractionRing P)))) := by
  have h : Function.Injective (algebraMap P (AlgebraicClosure (FractionRing P))) := by
    rw [IsScalarTower.algebraMap_eq P (FractionRing P) (AlgebraicClosure (FractionRing P))]
    exact (algebraMap (FractionRing P) _).injective.comp (IsFractionRing.injective P _)
  rw [IsScalarTower.algebraMap_eq P (integralClosure P (AlgebraicClosure (FractionRing P)))
    (AlgebraicClosure (FractionRing P))] at h
  exact fun x y hxy => h (by simp only [RingHom.comp_apply, hxy])

theorem Cover_of : LateralTheory.E.t_E1Cut.Cover := by
  intro A _
  let π : MvPolynomial A ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hπ : Function.Surjective π := fun a => ⟨MvPolynomial.X a, by simp [π]⟩
  let T := integralClosure (MvPolynomial A ℤ) (AlgebraicClosure (FractionRing (MvPolynomial A ℤ)))
  let I : Ideal T := (RingHom.ker π).map (algebraMap (MvPolynomial A ℤ) T)
  let ψ : MvPolynomial A ℤ ⧸ RingHom.ker π →+* T ⧸ I :=
    Ideal.quotientMap I (algebraMap (MvPolynomial A ℤ) T) Ideal.le_comap_map
  let φ : A →+* T ⧸ I := ψ.comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hcomp : φ.comp π = (Ideal.Quotient.mk I).comp (algebraMap (MvPolynomial A ℤ) T) := by
    apply RingHom.ext
    intro x
    simp [φ, ψ, Ideal.quotientMap_mk]
  refine ⟨T ⧸ I, inferInstance, φ, ?_, ?_, ?_⟩
  · apply RingHom.IsIntegral.tower_top π φ
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  · intro p
    have : (Ideal.comap π p.asIdeal).IsPrime := Ideal.comap_isPrime π p.asIdeal
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T)
      (Ideal.comap π p.asIdeal) (⊥ : Ideal T) (by
        rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (inj_P _)]
        exact bot_le)
    rw [Ideal.under_def] at hQc
    have hIQ : I ≤ Q := by
      apply Ideal.map_le_iff_le_comap.2
      rw [hQc]
      intro x hx
      simp [RingHom.mem_ker.1 hx]
    have hQ' : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨Q.map (Ideal.Quotient.mk I), hQ'⟩, ?_⟩
    ext1
    apply Ideal.comap_injective_of_surjective π hπ
    simp only [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIQ, hQc]
  · exact ⟨T, inferInstance, inferInstance, Ideal.Quotient.mk I, aic_integralClosure _,
      Ideal.Quotient.mk_surjective⟩

end LateralTheory.E.CoverIntegralClosure
end
end

namespace UpperTheory.Et.EtaleCovers

theorem a0 : LateralTheory.E.t_E1Cut.Cover := LateralTheory.E.CoverIntegralClosure.Cover_of

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.Cover := a0

end UpperTheory.Et.EtaleCovers
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyDescentOfCechCover
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

private theorem conn_neg (a9 : A9) {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) :
    Conn R f F (-1) := by
  have hs := (a9 R F).1
  refine ⟨fun j hj => ?_, ?_⟩
  · haveI := hs E j (by omega)
    haveI := hs E' j (by omega)
    exact ⟨Function.injective_of_subsingleton _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · haveI := hs E' (-1) (by omega)
    exact Function.injective_of_subsingleton _

private theorem conn_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (n : ℤ) :
    Conn R (disc.map f) F n ↔ Conn R (disc.map g) F n := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact conn_sq R w (eqv_iso R _ F) (eqv_iso R _ F) n

private theorem eqv_level {R : Type} [CommRing R] {P P' Q Q' : PSh} {f : P ⟶ P'} {g : Q ⟶ Q'}
    (e : Arrow.mk f ≅ Arrow.mk g) (F : Shv R) (h : Eqv R (disc.map g) F) : Eqv R (disc.map f) F := by
  obtain ⟨a, b, ha, hb, w⟩ := arr_w e
  exact fun n => ((sq R w (eqv_iso R _ F) (eqv_iso R _ F) n).1).2 (h n)

private theorem conn_all (a1 : A1) (a9 : A9) (b1 : B1) (b2 : B2) (b4 : B4) (hC : Cover) (hE : EqvQA)
    (hD : DescStep) (hL : CechLevels) (q : ℕ) [NeZero q] (i : ℤ) (m : ℕ) :
    ∀ (B : Type) [CommRing B] (J : Ideal B), IsUnit (q : B) →
      (∀ (C : Type) [CommRing C] (χ : B →+* C), χ.IsIntegral → Good C (J.map χ)) →
      Conn (ZMod q) (spMap (Ideal.Quotient.mk J)) (tw q i) ((m : ℤ) - 1) := by
  induction m with
  | zero =>
    intro B _ J _ _
    rw [Nat.cast_zero, zero_sub]
    exact conn_neg a9 _ _
  | succ m ih =>
    intro B _ J hq hG
    obtain ⟨A', _, φ, hφ, hsurj, hQA⟩ := hC B
    obtain ⟨⟨h1, h2, h3, h4⟩, ψ, hψ, hlev, h0⟩ := hL B A' φ J hφ hsurj
    have hψc : Conn (ZMod q) ψ (tw q i) ((m : ℤ) - 1 + 1) := by
      apply hD a1 (ZMod q) (tw q i) ψ ((m : ℤ) - 1)
      · intro p
        obtain ⟨C, _, χ, hχ, ⟨e⟩⟩ := hlev p
        rw [conn_level e]
        apply ih C (J.map χ) (by simpa using hq.map χ)
        intro C' _ χ' hχ'
        rw [Ideal.map_map]
        exact hG C' (χ'.comp χ) (RingHom.IsIntegral.trans _ _ hχ hχ')
      · obtain ⟨e⟩ := h0
        apply eqv_level e
        exact hE a1 a9 b1 b2 q A' (J.map φ) hQA (hG A' φ hφ) (by simpa using hq.map φ) i
    have hmm : ((m : ℤ) - 1 + 1) = ((m + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [hmm] at hψc
    have hqJ : IsUnit ((q : ℕ) : B ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
    have ea := @b4 q _ _ (Spec.map (CommRingCat.ofHom φ)) h1 h2 (unit_spec (A := B) hq) i
    have eb := @b4 q _ _ _ h3 h4 (unit_spec (A := B ⧸ J) hqJ) i
    exact (conn_sq (ZMod q) hψ eb ea _).1 hψc

theorem UpperTheory.etaleCohomology_descent_of_cech_cover :
    A1 → A9 → B1 → B2 → B4 → Cover → HensIdem → EqvQA → DescStep → CechLevels → E1 := by
  intro a1 a9 b1 b2 b4 hC hH hE hD hL q A _ I _ hq i
  by_cases hq0 : q = 0
  · subst hq0
    have h01 : (0 : A) = 1 := isUnit_zero_iff.mp (by simpa using hq)
    haveI : Subsingleton A := subsingleton_of_zero_eq_one h01
    have hb : Function.Bijective (Ideal.Quotient.mk I) :=
      ⟨fun x y _ => Subsingleton.elim x y, Ideal.Quotient.mk_surjective⟩
    haveI : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
      (RingEquiv.ofBijective (Ideal.Quotient.mk I) hb).toCommRingCatIso.isIso_hom
    exact eqv_iso _ _ _
  · haveI : NeZero q := ⟨hq0⟩
    intro n
    have hc := conn_all a1 a9 b1 b2 b4 hC hE hD hL q i (n.toNat + 2) A I hq
      (fun C _ χ hχ => hH A I C χ hχ)
    exact hc.1 n (by push_cast; omega)

end
end

namespace UpperTheory.Et

theorem affine_proper_base_change : GlobalTheory.EtC.E1 :=
  UpperTheory.etaleCohomology_descent_of_cech_cover GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf GlobalTheory.T.integralSurjection_cechDescent_tateTwist EtaleCovers.intersectionNumber_baseChange HenselianIdempotents.intersectionNumber_baseChange QuasiAffineEquivalence.intersectionNumber_baseChange EtaleDescentEtaleAxioms.intersectionNumber_baseChange CechLevelsEtaleAxioms.intersectionNumber_baseChange

theorem proper_base_change : GlobalTheory.EtC.E2 :=
  E2.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.etaleCohomology_coefficient_longExactSequence, GlobalTheory.T.etaleCohomology_coefficientRing_invariance, GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, GlobalTheory.T.etaleCohomology_bijective_of_support_bijective, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf, GlobalTheory.T.etC_b3, GlobalTheory.T.integralSurjection_cechDescent_tateTwist, GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic, affine_proper_base_change⟩

end UpperTheory.Et
