module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsMonHomSplitTorusOfSqEqBot
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)

namespace GlobalTheory.TorusDefect

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.SqZero GlobalTheory.Diag

variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']

theorem algHom_ext' {φ ψ : AddMonoidAlgebra A X →ₐ[A] C}
    (h : ∀ x, φ (single x 1) = ψ (single x 1)) : φ = ψ := AddMonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)

theorem charVal_spMap (φ : C →ₐ[A] C') (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) (x : X) :
    charVal (spMap φ ≫ w) x = φ (charVal w x) := by
  refine (GlobalTheory.Diag.left_eq_iff (g := Spec.map (CommRingCat.ofHom (algebraMap A C))) φ.toRingHom ?_
    (spMap φ ≫ w) w).1 ?_ x
  · have h := Over.w (spMap φ)
    rw [spMap_left] at h
    exact h.symm
  · rw [Over.comp_left, spMap_left]


variable (A X) in
def univ : sp (AddMonoidAlgebra A X) ⟶ splitTorus (Spec (CommRingCat.of A)) X :=
  ofVal _ (AddMonoidAlgebra.of A X)

theorem charVal_univ (φ : AddMonoidAlgebra A X →ₐ[A] C) (x : X) :
    charVal (spMap φ ≫ univ A X) x = φ (single x 1) := by
  rw [charVal_spMap, univ, GlobalTheory.Diag.charVal_ofVal, AddMonoidAlgebra.of_apply, toAdd_ofAdd]

def valHom (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) : Multiplicative X →* C where
  toFun x := charVal w x.toAdd
  map_one' := charVal_zero w
  map_mul' _ _ := charVal_add w _ _

theorem exists_eq_univ (w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) :
    ∃ φ : AddMonoidAlgebra A X →ₐ[A] C, spMap φ ≫ univ A X = w := by
  refine ⟨AddMonoidAlgebra.lift A C X (valHom w), GlobalTheory.Diag.charVal_ext fun x => ?_⟩
  rw [charVal_univ, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem exists_eq_univ₂ (v w : sp C ⟶ splitTorus (Spec (CommRingCat.of A)) X) :
    ∃ φ : AddMonoidAlgebra A (X × X) →ₐ[A] C,
      spMap (φ.comp (mapDomainAlgHom A A (AddMonoidHom.inl X X))) ≫ univ A X = v ∧
      spMap (φ.comp (mapDomainAlgHom A A (AddMonoidHom.inr X X))) ≫ univ A X = w := by
  let F : Multiplicative (X × X) →* C :=
    (valHom v).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X X)) *
      (valHom w).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X X))
  refine ⟨AddMonoidAlgebra.lift A C (X × X) F, GlobalTheory.Diag.charVal_ext fun x => ?_,
    GlobalTheory.Diag.charVal_ext fun x => ?_⟩ <;>
  · rw [charVal_univ]
    simp [F, valHom, GlobalTheory.Diag.charVal_zero]

theorem univ_add (φ : AddMonoidAlgebra A Y →ₐ[A] C) (u v : X →+ Y) :
    spMap (φ.comp (mapDomainAlgHom A A (u + v))) ≫ univ A X =
      spMap (φ.comp (mapDomainAlgHom A A u)) ≫ univ A X *
        spMap (φ.comp (mapDomainAlgHom A A v)) ≫ univ A X := by
  refine GlobalTheory.Diag.charVal_ext fun x => ?_
  rw [GlobalTheory.Diag.charVal_mul, charVal_univ, charVal_univ, charVal_univ]
  simp only [AlgHom.comp_apply]
  rw [← map_mul]
  congr 1
  simp [AddMonoidAlgebra.single_mul_single]

theorem exists_affinization (Z : Over (Spec (CommRingCat.of A))) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (p : Z ⟶ sp C),
      (∀ a : Z ⟶ splitTorus (Spec (CommRingCat.of A)) X, ∃ a', p ≫ a' = a) ∧
      ∀ (J : Ideal A) (s : Z.left ⟶ Spec (CommRingCat.of (A ⧸ J))),
        Z.hom = s ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) →
        ∀ j ∈ J, algebraMap A C j = 0 := by
  let inst : Algebra A Γ(Z.left, ⊤) :=
    (Z.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).toAlgebra
  have e : CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ Z.hom.appTop := rfl
  have hw : Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤))) = Z.hom := by
    rw [e, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine ⟨Γ(Z.left, ⊤), inferInstance, inst, Over.homMk Z.left.toSpecΓ hw, ?_, ?_⟩
  · intro a
    let F : Multiplicative X →* Γ(Z.left, ⊤) :=
      { toFun := fun x => SplitTorus.val a x.toAdd
        map_one' := SplitTorus.val_zero a
        map_mul' := fun x y => SplitTorus.val_add a x.toAdd y.toAdd }
    refine ⟨GlobalTheory.Diag.ofVal _ F, SplitTorus.hom_ext fun x => ?_⟩
    have h1 := GlobalTheory.Diag.charVal_ofVal
      (g := Spec.map (CommRingCat.ofHom (algebraMap A Γ(Z.left, ⊤)))) F x
    unfold GlobalTheory.Diag.charVal at h1
    rw [SplitTorus.val_comp, SplitTorus.val_eq]
    change (Z.left.toSpecΓ.appTop).hom _ = _
    rw [Scheme.toSpecΓ_appTop]
    exact h1
  · intro J s hs j hj
    show Z.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom j) = 0
    rw [hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      SplitTorus.specMap_appTop_apply, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 hj,
      map_zero, map_zero]

theorem exists_inv_univ : ∃ r : splitTorus (Spec (CommRingCat.of A)) X ⟶ sp (AddMonoidAlgebra A X),
    r ≫ univ A X = 𝟙 _ ∧ univ A X ≫ r = 𝟙 _ := by
  obtain ⟨C, _, _, p, hp, -⟩ := exists_affinization (A := A) (X := X) (splitTorus (Spec (CommRingCat.of A)) X)
  obtain ⟨a', ha'⟩ := hp (𝟙 _)
  obtain ⟨φ, hφ⟩ := exists_eq_univ a'
  refine ⟨p ≫ spMap φ, by rw [Category.assoc, hφ, ha'], ?_⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SqZero.exists_spMap (univ A X ≫ p ≫ spMap φ)
  have h1 : spMap α ≫ univ A X = spMap (AlgHom.id A (AddMonoidAlgebra A X)) ≫ univ A X := by
    rw [spMap_id, Category.id_comp, ← hα, Category.assoc, Category.assoc, hφ, ha', Category.comp_id]
  have h2 : α = AlgHom.id A _ := algHom_ext' fun x => by
    have h3 := congrArg (fun w => charVal w x) h1
    simpa only [charVal_univ] using h3
  rw [hα, h2, spMap_id]

theorem mul_comp_of_pullback {S S' : Scheme.{0}} (i : S' ⟶ S) {G H : Over S} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom ((Over.pullback i).map f)] {W : Scheme.{0}} (s : W ⟶ S') (z : W ⟶ S)
    (hz : z = s ≫ i) (a b : Over.mk z ⟶ G) : (a * b) ≫ f = a ≫ f * b ≫ f := by
  subst hz
  obtain ⟨a', ha'⟩ : ∃ a' : Over.mk s ⟶ (Over.pullback i).obj G,
      a'.left ≫ pullback.fst G.hom i = a.left :=
    ⟨Over.homMk (pullback.lift a.left s (Over.w a)) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Over.mk s ⟶ (Over.pullback i).obj G,
      b'.left ≫ pullback.fst G.hom i = b.left :=
    ⟨Over.homMk (pullback.lift b.left s (Over.w b)) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  have hpf : ((Over.pullback i).map f).left ≫ pullback.fst H.hom i = pullback.fst G.hom i ≫ f.left :=
    pullback.lift_fst _ _ _
  have h1 := SplitTorus.mul_left_comp_fst G i a' b' a b ha'.symm hb'.symm
  have h2 := SplitTorus.mul_left_comp_fst H i (a' ≫ (Over.pullback i).map f)
    (b' ≫ (Over.pullback i).map f) (a ≫ f) (b ≫ f)
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc, ha'])
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc, hb'])
  apply Over.OverMorphism.ext
  rw [h2, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, hpf, ← Category.assoc,
    ← h1]

theorem mem_map_iff (J : Ideal A) (b : AddMonoidAlgebra A X) :
    b ∈ J.map (algebraMap A (AddMonoidAlgebra A X)) ↔ ∀ x, b.coeff x ∈ J := by
  constructor
  · intro hb x
    have h0 : b ∈ RingHom.ker (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk J)) := by
      refine (Ideal.map_le_iff_le_comap.2 ?_) hb
      intro a ha
      simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapRingHom_single,
        Ideal.Quotient.eq_zero_iff_mem, ha]
    have h1 := congrArg (fun c => c.coeff x) (RingHom.mem_ker.1 h0)
    simpa [AddMonoidAlgebra.coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem] using h1
  · intro hb
    rw [← AddMonoidAlgebra.sum_coeff_single b, Finsupp.sum]
    refine Ideal.sum_mem _ fun x _ => ?_
    have hx : single x (b.coeff x) =
        algebraMap A (AddMonoidAlgebra A X) (b.coeff x) * single x 1 := by
      rw [← Algebra.smul_def, AddMonoidAlgebra.smul_single', _root_.mul_one]
    rw [hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hb x))

theorem map_mem_map {J : Ideal A} (φ : C →ₐ[A] C') :
    ∀ a ∈ J.map (algebraMap A C), φ a ∈ J.map (algebraMap A C') := fun a ha => by
  have h := Ideal.mem_map_of_mem (φ : C →+* C') ha
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at h

theorem map_algebraMap_sq {J : Ideal A} (hJ : J ^ 2 = ⊥) : J.map (algebraMap A C) ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]

section Cocycle

variable {G : Over (Spec (CommRingCat.of A))} [GrpObj G] {J : Ideal A}
  {Z : Type} [AddCommGroup Z]

def pull (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (u : X →+ Y) :
    (sp (AddMonoidAlgebra A X) ⟶ G) →* (sp (AddMonoidAlgebra A Y) ⟶ G) :=
  pointsMap G (mapDomainAlgHom A A u)

theorem pull_pull (u : X →+ Y) (v : Y →+ Z) (y : sp (AddMonoidAlgebra A X) ⟶ G) :
    pull G v (pull G u y) = pull G (v.comp u) y := by
  rw [pull, pull, pull, ptsMap_apply, ptsMap_apply, ptsMap_apply, ← Category.assoc, spMap_comp,
    AddMonoidAlgebra.mapDomainAlgHom_comp]

def pullKer (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (J : Ideal A) (u : X →+ Y) :
    redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))) →*
      redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A Y))) :=
  ((pull G u).comp (Subgroup.subtype _)).codRestrict _ fun y =>
    comp_mem_redKer y.2 _ (map_mem_map _)

theorem coe_pullKer (u : X →+ Y)
    (y : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X)))) :
    (pullKer G J u y).1 = pull G u y.1 := rfl

variable [IsCommMonObj G] [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR A ⟶ G)}

theorem kerEquiv_pullKer (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) (u : X →+ Y)
    (y : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X)))) (i : Fin n) :
    (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul (pullKer G J u y)) i :
      AddMonoidAlgebra A Y) =
      AddMonoidAlgebra.mapDomain u (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul y) i :
        AddMonoidAlgebra A X) := by
  have h := kerEquiv_map hv (map_algebraMap_sq hJ) (map_algebraMap_sq hJ) (mapDomainAlgHom A A u)
    (map_mem_map _) y i
  have e : pullKer G J u y = ⟨spMap (mapDomainAlgHom A A u) ≫ y.1,
      comp_mem_redKer y.2 (mapDomainAlgHom A A u) (map_mem_map _)⟩ := Subtype.ext (coe_pullKer u y)
  rw [e, h]
  simp


open AddMonoidHom in
theorem exists_coboundary (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥)
    (δ : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))))
    (hδ : pullKer G J (inr X (X × X)) δ / pullKer G J ((AddMonoidHom.fst X X).prod (AddMonoidHom.id _)) δ *
      pullKer G J ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))) δ /
      pullKer G J (prodMap (AddMonoidHom.id X) (inl X X)) δ = 1) :
    ∃ κ : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))),
      pullKer G J (inr X X) κ / pullKer G J (inl X X + inr X X) κ * pullKer G J (inl X X) κ = δ := by
  set f : Fin n → AddMonoidAlgebra A (X × X) :=
    fun i => ((kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul δ) i : AddMonoidAlgebra A (X × X))) with hf
  have hcoc : ∀ i, AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) (f i) -
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) (f i) +
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) (f i) -
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) (f i) = 0 := by
    intro i
    have h := congrArg (fun z => ((kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul z) i :
      AddMonoidAlgebra A (X × (X × X))))) hδ
    simp only [ofMul_div, ofMul_mul, ofMul_one, map_sub, map_add (f := _), map_zero, Pi.sub_apply,
      Pi.add_apply, Pi.zero_apply, AddSubgroupClass.coe_sub, AddMemClass.coe_add,
      ZeroMemClass.coe_zero] at h
    rw [kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ,
      kerEquiv_pullKer hv hJ] at h
    exact h
  have key : ∀ i, ∃ g : AddMonoidAlgebra A X,
      AddMonoidAlgebra.mapDomain (fun y : X => ((0 : X), y)) g -
        AddMonoidAlgebra.mapDomain (fun y : X => (y, y)) g +
        AddMonoidAlgebra.mapDomain (fun y : X => (y, (0 : X))) g = f i :=
    fun i => (addMonoidAlgebra_existsUnique_coboundary (f i) (hcoc i)).exists
  choose g hg using key
  have hmem : ∀ i, g i ∈ J.map (algebraMap A (AddMonoidAlgebra A X)) := by
    intro i
    rw [mem_map_iff]
    intro x
    rw [(addMonoidAlgebra_coboundary_eq_iff (f i) (hcoc i) (g i)).1 (hg i) x]
    exact (mem_map_iff J (f i)).1 (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul δ) i).2 (0, x)
  refine ⟨Additive.toMul ((kerEquiv hv (map_algebraMap_sq hJ)).symm fun i => ⟨g i, hmem i⟩), ?_⟩
  apply Additive.ofMul.injective
  apply (kerEquiv hv (map_algebraMap_sq hJ)).injective
  funext i
  apply Subtype.ext
  have e2 : (⇑(AddMonoidHom.inl X X + AddMonoidHom.inr X X) : X → X × X) = fun y => (y, y) :=
    funext fun y => by simp
  simp only [ofMul_div, ofMul_mul, map_sub, map_add (f := _), Pi.sub_apply, Pi.add_apply,
    AddSubgroupClass.coe_sub, AddMemClass.coe_add]
  rw [kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ, kerEquiv_pullKer hv hJ]
  simp only [ofMul_toMul, AddEquiv.apply_symm_apply, e2]
  exact hg i


open AddMonoidHom in
theorem exists_correction (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) (h : sp (AddMonoidAlgebra A X) ⟶ G)
    (hh : pull G (inr X X) h / pull G (inl X X + inr X X) h * pull G (inl X X) h ∈
      redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A (X × X))))) :
    ∃ κ ∈ redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X))),
      pull G (inl X X + inr X X) (h / κ) = pull G (inl X X) (h / κ) * pull G (inr X X) (h / κ) := by
  have e1 : ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))).comp (AddMonoidHom.inr X X) =
      (AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inr X X) := AddMonoidHom.ext fun y => by simp
  have e2 : ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))).comp
      (AddMonoidHom.inr X X) = (AddMonoidHom.inr X (X × X)).comp
        (AddMonoidHom.inl X X + AddMonoidHom.inr X X) := AddMonoidHom.ext fun y => by simp
  have e3 : (prodMap (AddMonoidHom.id X) (AddMonoidHom.inl X X)).comp (AddMonoidHom.inr X X) =
      (AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inl X X) := AddMonoidHom.ext fun y => by simp
  have e4 : ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))).comp
      (AddMonoidHom.inl X X + AddMonoidHom.inr X X) =
      ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))).comp
        (AddMonoidHom.inl X X + AddMonoidHom.inr X X) := AddMonoidHom.ext fun y => by simp
  have e5 : (prodMap (AddMonoidHom.id X) (AddMonoidHom.inl X X)).comp
      (AddMonoidHom.inl X X + AddMonoidHom.inr X X) =
      ((AddMonoidHom.fst X X).prod (AddMonoidHom.id (X × X))).comp (AddMonoidHom.inl X X) :=
    AddMonoidHom.ext fun y => by simp
  have e6 : (prodMap (AddMonoidHom.id X) (AddMonoidHom.inl X X)).comp (AddMonoidHom.inl X X) =
      ((AddMonoidHom.fst X X).prod ((AddMonoidHom.snd X X).prod (AddMonoidHom.snd X X))).comp
        (AddMonoidHom.inl X X) := AddMonoidHom.ext fun y => by simp
  obtain ⟨κ, hκ⟩ := exists_coboundary hv hJ ⟨_, hh⟩ (by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_div, Subgroup.coe_one, coe_pullKer, map_mul, map_div,
      pull_pull]
    rw [e1, e2, e3, e4, e5, e6]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul, ofMul_one]
    abel)
  refine ⟨κ.1, κ.2, ?_⟩
  have h1 := congrArg (fun z => Additive.ofMul (Subtype.val z)) hκ
  simp only [Subgroup.coe_mul, Subgroup.coe_div, coe_pullKer, ofMul_div, ofMul_mul] at h1
  rw [map_div, map_div, map_div]
  apply Additive.ofMul.injective
  simp only [ofMul_div, ofMul_mul]
  rw [← sub_eq_zero] at h1 ⊢
  rw [← h1]
  abel

end Cocycle

end GlobalTheory.TorusDefect

namespace GlobalTheory

open SqZero TorusDefect

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_isMonHom_splitTorus_of_sq_eq_bot (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (X : Type) [AddCommGroup X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G)
    (hf : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f)) :
    ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f' =
        (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f := by
  have hL : ∃ (n : ℕ) (v : Fin n → (epsR A ⟶ G)), IsLieBasis v :=
    ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G inferInstance
  obtain ⟨r, hr1, hr2⟩ := TorusDefect.exists_inv_univ (A := A) (X := X)
  obtain ⟨n, v, hv⟩ := hL
  have hur : ∀ {W : Over (Spec (CommRingCat.of A))} (q : sp (AddMonoidAlgebra A X) ⟶ W),
      univ A X ≫ r ≫ q = q := fun q => by rw [← Category.assoc, hr2, Category.id_comp]

  have hh : pull G (AddMonoidHom.inr X X) (univ A X ≫ f) /
      pull G (AddMonoidHom.inl X X + AddMonoidHom.inr X X) (univ A X ≫ f) *
      pull G (AddMonoidHom.inl X X) (univ A X ≫ f) ∈
      redKer G (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))) := by
    rw [mem_redKer]
    have hx : ∀ u : X →+ X × X,
        spMap (Ideal.Quotient.mkₐ A (J.map (algebraMap A (AddMonoidAlgebra A (X × X))))) ≫
          pull G u (univ A X ≫ f) =
        (spMap ((Ideal.Quotient.mkₐ A (J.map (algebraMap A (AddMonoidAlgebra A (X × X))))).comp
          (mapDomainAlgHom A A u)) ≫ univ A X) ≫ f := fun u => by
      rw [pull, ptsMap_apply, ← Category.assoc, spMap_comp, Category.assoc]
    have hz : Spec.map (CommRingCat.ofHom (algebraMap A
        (AddMonoidAlgebra A (X × X) ⧸ J.map (algebraMap A (AddMonoidAlgebra A (X × X)))))) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap
          (J.map (algebraMap A (AddMonoidAlgebra A (X × X)))) (algebraMap A _) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [MonObj.comp_mul, GrpObj.comp_div, hx, hx, hx, univ_add,
      mul_comp_of_pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) f _ _ hz]
    apply Additive.ofMul.injective
    simp only [ofMul_div, ofMul_mul, ofMul_one]
    abel
  obtain ⟨κ, hκ, hmul⟩ := TorusDefect.exists_correction hv hJ (univ A X ≫ f) hh
  have hpull : ∀ {C : Type} [CommRing C] [Algebra A C] (φ : AddMonoidAlgebra A (X × X) →ₐ[A] C)
      (u : X →+ X × X), spMap (φ.comp (mapDomainAlgHom A A u)) ≫ (univ A X ≫ f / κ) =
        spMap φ ≫ pull G u (univ A X ≫ f / κ) := fun φ u => by
    rw [pull, ptsMap_apply, ← Category.assoc, spMap_comp]
  refine ⟨r ≫ (univ A X ≫ f / κ), ?_, ?_⟩
  · refine isMonHom_of_mul _ fun T x y => ?_
    obtain ⟨C, _, _, p, hp, -⟩ := TorusDefect.exists_affinization (X := X) T
    obtain ⟨x', rfl⟩ := hp x
    obtain ⟨y', rfl⟩ := hp y
    obtain ⟨φ, rfl, rfl⟩ := TorusDefect.exists_eq_univ₂ x' y'
    rw [← MonObj.comp_mul, ← univ_add]
    simp only [Category.assoc, hur]
    rw [← MonObj.comp_mul, hpull, hpull, hpull, hmul]
    congr 1
    exact MonObj.comp_mul _ _ _
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      obtain ⟨a, ha⟩ : ∃ a : Over.mk (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⟶ splitTorus (Spec (CommRingCat.of A)) X,
          a.left = pullback.fst _ _ := ⟨Over.homMk _ pullback.condition, rfl⟩
      obtain ⟨C, _, _, p, hp, hJC⟩ := TorusDefect.exists_affinization (X := X) (Over.mk
        (pullback.snd (splitTorus (Spec (CommRingCat.of A)) X).hom
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
      obtain ⟨a', ha'⟩ := hp a
      obtain ⟨ψ, hψ⟩ := TorusDefect.exists_eq_univ a'
      have hle : J.map (algebraMap A (AddMonoidAlgebra A X)) ≤ RingHom.ker (ψ : AddMonoidAlgebra A X →+* C) :=
        Ideal.map_le_iff_le_comap.2 fun j hj => by
          show ψ (algebraMap A _ j) = 0
          rw [AlgHom.commutes]
          exact hJC J _ rfl j hj
      have hκ0 : spMap ψ ≫ κ = 1 :=
        comp_eq_one_of_mem_redKer hκ ψ fun b hb => RingHom.mem_ker.1 (hle hb)
      have E : a ≫ r ≫ (univ A X ≫ f / κ) = a ≫ f := by
        rw [← ha', ← hψ]
        simp only [Category.assoc, hur]
        rw [GrpObj.comp_div, hκ0, div_one]
      rw [← ha, ← Over.comp_left, ← Over.comp_left, E]
    · simp only [Over.pullback_map_left, pullback.lift_snd]

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusLift

section General

variable {S S' S'' : Scheme.{0}}

theorem map_left_fst (p : S' ⟶ S) {V W : Over S} (f : V ⟶ W) :
    ((Over.pullback p).map f).left ≫ pullback.fst W.hom p = pullback.fst V.hom p ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem hom_ext_fst (p : S' ⟶ S) {Z : Over S'} {W : Over S} {a b : Z ⟶ (Over.pullback p).obj W}
    (h : a.left ≫ pullback.fst W.hom p = b.left ≫ pullback.fst W.hom p) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  have ha := Over.w a
  have hb := Over.w b
  simp only [Over.pullback_obj_hom] at ha hb
  simp [ha, hb]

theorem map_eq_iff {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p) {V W : Over S}
    (f g : V ⟶ W) : (Over.pullback q).map f = (Over.pullback q).map g ↔
      (Over.pullback s).map ((Over.pullback p).map f) =
        (Over.pullback s).map ((Over.pullback p).map g) := by
  subst h
  constructor
  · intro hfg
    have h1 := (Over.pullbackComp s p).hom.naturality f
    have h2 := (Over.pullbackComp s p).hom.naturality g
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi ((Over.pullbackComp s p).hom.app V)).1
    rw [← h1, ← h2, hfg]
  · intro hfg
    have h1 := (Over.pullbackComp s p).inv.naturality f
    have h2 := (Over.pullbackComp s p).inv.naturality g
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi ((Over.pullbackComp s p).inv.app V)).1
    rw [← h1, ← h2, hfg]

private theorem pullback_pullback_hom_ext {s : S'' ⟶ S'} {p : S' ⟶ S} {G : Over S} {Z : Over S''}
    {a b : Z ⟶ (Over.pullback s).obj ((Over.pullback p).obj G)}
    (h : a.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p = b.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p) :
    a = b := by
  apply hom_ext_fst
  apply pullback.hom_ext
  · simpa using h
  · have ha := Over.w a
    have hb := Over.w b
    simp only [Over.pullback_obj_hom] at ha hb
    simp only [Category.assoc, Over.pullback_obj_left, Over.pullback_obj_hom] at *
    rw [pullback.condition, reassoc_of% ha, reassoc_of% hb]

private theorem pullbackComp_hom_fst_fst (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) :
    ((Over.pullbackComp s p).hom.app G).left ≫ pullback.fst _ s ≫ pullback.fst G.hom p =
      pullback.fst G.hom (s ≫ p) := by
  have h := congrArg (fun x => x.left) (conjugateEquiv_counit (Over.mapPullbackAdj (s ≫ p))
    ((Over.mapPullbackAdj s).comp (Over.mapPullbackAdj p)) (Over.mapComp s p).symm.hom G)
  simpa [Over.pullbackComp] using h

theorem isMonHom_pullbackComp (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsMonHom (M := (Over.pullback (s ≫ p)).obj G)
      (N := (Over.pullback s).obj ((Over.pullback p).obj G))
      ((Over.pullbackComp s p).hom.app G) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.exists_pullback_comp_iso_monHom s p (s ≫ p) rfl G
  have : (Over.pullbackComp s p).hom.app G = e.hom := by
    apply pullback_pullback_hom_ext
    rw [hc, pullbackComp_hom_fst_fst]
  rw [this]
  exact he

private theorem isMonHom_iff_of_conj_iso {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    [MonObj M] [MonObj M'] [MonObj N] [MonObj N'] (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b]
    (ha : IsMonHom a) (hb : IsMonHom b) (g : M ⟶ N) (g' : M' ⟶ N') (hg : g ≫ b = a ≫ g') :
    IsMonHom g ↔ IsMonHom g' := by
  constructor
  · intro h
    have e : g' = (asIso a).inv ≫ g ≫ b := by simp [hg]
    rw [e]
    infer_instance
  · intro h
    have e : g = a ≫ g' ≫ (asIso b).inv := by simp [← reassoc_of% hg]
    rw [e]
    infer_instance

theorem isMonHom_map_iff {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p)
    {V W : Over S} [GrpObj V] [GrpObj W] (f : V ⟶ W) : IsMonHom ((Over.pullback q).map f) ↔
      IsMonHom ((Over.pullback s).map ((Over.pullback p).map f)) := by
  subst h
  exact isMonHom_iff_of_conj_iso _ _ (isMonHom_pullbackComp s p V) (isMonHom_pullbackComp s p W) _ _
    ((Over.pullbackComp s p).hom.naturality f)

theorem preimage_eq_top_of_surjective {X Y Z : Scheme.{0}} (i : X ⟶ Y) [Surjective i] (f : Y ⟶ Z)
    {U : Z.Opens} (h : (i ≫ f) ⁻¹ᵁ U = ⊤) : f ⁻¹ᵁ U = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := i.surjective y
  have hx : x ∈ (i ≫ f) ⁻¹ᵁ U := by rw [h]; trivial
  simpa using hx

end General

theorem surjective_specMap {A C : CommRingCat.{0}} (β : A ⟶ C) (hβ : Function.Surjective β)
    (h : IsNilpotent (RingHom.ker β.hom)) : Surjective (Spec.map β) := by
  obtain ⟨n, hn⟩ := h
  have hh : IsHomeomorph (PrimeSpectrum.comap β.hom) := by
    refine PrimeSpectrum.isHomeomorph_comap β.hom (fun x => ⟨1, one_pos, ?_⟩) ?_
    · obtain ⟨y, rfl⟩ := hβ x
      exact ⟨y, by simp⟩
    · intro x hx
      have hxn : x ^ n ∈ RingHom.ker β.hom ^ n := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hxn
      exact mem_nilradical.2 ⟨n, hxn⟩
  exact ⟨hh.surjective⟩

theorem isAffine_splitTorus (A : Type) [CommRing A] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left := by
  have := GlobalTheory.TorusNil.isIso_torusPt_of A X
  have : IsAffine (GlobalTheory.TorusNil.sp A (AddMonoidAlgebra A X)).left := by
    dsimp [GlobalTheory.TorusNil.sp]
    infer_instance
  exact IsAffine.of_isIso (inv (GlobalTheory.TorusNil.torusPt A X (AddMonoidAlgebra.of A X)).left)

theorem exists_lift {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [Smooth G.hom]
    (g : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G)
    {W : G.left.Opens} (hW : IsAffineOpen W) (hg : (g.left ≫ pullback.fst _ _) ⁻¹ᵁ W = ⊤) :
    ∃ f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, f.left ⁻¹ᵁ W = ⊤ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f = g := by
  have := isAffine_splitTorus A X
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  obtain ⟨f, hf⟩ := GlobalTheory.NilpotentLift.main A J hJ G (splitTorus (Spec (CommRingCat.of A)) X)
    (g.left ≫ pullback.fst _ _) (by
      have hw := Over.w g
      simp only [Over.pullback_obj_hom] at hw
      rw [Category.assoc, pullback.condition (f := G.hom), reassoc_of% hw]
      exact pullback.condition.symm) ⟨W, hW, hg⟩
  refine ⟨f, ?_, ?_⟩
  · apply preimage_eq_top_of_surjective
      (pullback.fst (splitTorus (Spec (CommRingCat.of A)) X).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    rw [hf]
    exact hg
  · apply hom_ext_fst
    rw [map_left_fst, hf]

private theorem exists_factor_through_quotient_of_surjective {A : Type} [CommRing A] (J : Ideal A) {C : CommRingCat.{0}}
    (β : CommRingCat.of A ⟶ C) (hβ : Function.Surjective β) (hker : RingHom.ker β.hom = J) :
    ∃ (g0 : C ⟶ CommRingCat.of (A ⧸ J)) (d0 : CommRingCat.of (A ⧸ J) ⟶ C),
      β ≫ g0 = CommRingCat.ofHom (Ideal.Quotient.mk J) ∧
        CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ d0 = β := by
  subst hker
  let e := RingHom.quotientKerEquivOfSurjective (f := β.hom) hβ
  refine ⟨CommRingCat.ofHom e.symm.toRingHom, CommRingCat.ofHom e.toRingHom, ?_, ?_⟩
  · ext a
    change e.symm (β.hom a) = Ideal.Quotient.mk _ a
    rw [RingEquiv.symm_apply_eq]
    rfl
  · ext a
    rfl

private theorem pullback_map_eq_iff_and_isMonHom_iff {S S' S'' : Scheme.{0}} {p : S' ⟶ S} {q : S'' ⟶ S} (s : S'' ⟶ S')
    (t : S' ⟶ S'') (hq : q = s ≫ p) (hp : p = t ≫ q) {V W : Over S} [GrpObj V] [GrpObj W]
    (f g : V ⟶ W) :
    ((Over.pullback p).map f = (Over.pullback p).map g ↔
        (Over.pullback q).map f = (Over.pullback q).map g) ∧
      (IsMonHom ((Over.pullback p).map f) ↔ IsMonHom ((Over.pullback q).map f)) := by
  refine ⟨⟨fun h => (map_eq_iff hq f g).2 (by rw [h]), fun h => (map_eq_iff hp f g).2 (by rw [h])⟩,
    ⟨fun h => (isMonHom_map_iff hq f).2 (by infer_instance),
      fun h => (isMonHom_map_iff hp f).2 (by infer_instance)⟩⟩

private theorem preimage_eq_univ_of_pullback_map_eq {S S' : Scheme.{0}} (p : S' ⟶ S) [Surjective p] {V W : Over S}
    (f g : V ⟶ W) (h : (Over.pullback p).map f = (Over.pullback p).map g) (U : W.left.Opens)
    (hf : f.left ⁻¹ᵁ U = ⊤) : g.left ⁻¹ᵁ U = ⊤ := by
  apply preimage_eq_top_of_surjective (pullback.fst V.hom p)
  rw [← map_left_fst p g, ← h, map_left_fst p f, Scheme.Hom.comp_preimage, hf,
    Scheme.Hom.preimage_top]

private theorem exists_isMonHom_lift_of_isMonHom_baseChange (X : Type) [AddCommGroup X] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), J ^ (n + 1) = ⊥ →
      ∀ {C : CommRingCat.{0}} (β : CommRingCat.of A ⟶ C), Function.Surjective β →
      RingHom.ker β.hom = J → ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
        [Smooth G.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G),
        IsMonHom ((Over.pullback (Spec.map β)).map f) → ∀ W : G.left.Opens, IsAffineOpen W →
        f.left ⁻¹ᵁ W = ⊤ → ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
          (Over.pullback (Spec.map β)).map f' = (Over.pullback (Spec.map β)).map f := by
  induction n with
  | zero =>
    intro A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW
    obtain ⟨g0, d0, hg0, hd0⟩ := exists_factor_through_quotient_of_surjective J β hβ hker
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = Spec.map g0 ≫ Spec.map β := by
      rw [← hg0, Spec.map_comp]
    have hp : Spec.map β = Spec.map d0 ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [← hd0, Spec.map_comp]
    have hJ2 : J ^ 2 = ⊥ := by
      rw [pow_one] at hJ
      rw [hJ, pow_two, Ideal.mul_bot]
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A J hJ2 X G f
      ((pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f f).2.1 hf)
    exact ⟨f', hf'1, (pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f' f).1.2 hf'2⟩
  | succ n ih =>
    intro A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW
    obtain ⟨I, hIdef⟩ : ∃ I : Ideal A, I = J ^ (n + 1) := ⟨_, rfl⟩
    have hI2 : I ^ 2 = ⊥ := by
      rw [eq_bot_iff, ← hJ, hIdef, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    have hIJ : I ≤ J := hIdef ▸ Ideal.pow_le_self (by omega)
    have hItop : I ≠ ⊤ := by
      intro h
      rw [h, pow_two, Ideal.top_mul] at hI2
      exact top_ne_bot hI2
    have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
    have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hIker : I ≤ RingHom.ker β.hom := hker ▸ hIJ
    let β' : CommRingCat.of (A ⧸ I) ⟶ C :=
      CommRingCat.ofHom (Ideal.Quotient.lift I β.hom (fun a ha => (RingHom.mem_ker).1 (hIker ha)))
    have hββ : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ β' = β := by
      ext a
      rfl
    have hβ' : Function.Surjective β' := by
      intro c
      obtain ⟨a, rfl⟩ := hβ c
      exact ⟨Ideal.Quotient.mk I a, rfl⟩
    have hker' : RingHom.ker β'.hom = J.map (Ideal.Quotient.mk I) := by
      simp only [β', CommRingCat.hom_ofHom]
      rw [← hker]
      exact Ideal.ker_quotient_lift _ hIker
    have hJ' : (J.map (Ideal.Quotient.mk I)) ^ (n + 1) = ⊥ := by
      rw [← Ideal.map_pow, ← hIdef, Ideal.map_quotient_self]
    have hSpec : Spec.map β = Spec.map β' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [← hββ, Spec.map_comp]
    have hsurjβ' : Surjective (Spec.map β') :=
      surjective_specMap β' hβ' ⟨n + 1, by rw [hker', hJ', Ideal.zero_eq_bot]⟩
    have hInil : IsNilpotent I := ⟨2, by rw [hI2, Ideal.zero_eq_bot]⟩
    have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).hom := by
      show Smooth (pullback.snd G.hom _)
      infer_instance
    obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Spec (CommRingCat.of A))
      (Spec (CommRingCat.of (A ⧸ I))) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) X
    obtain ⟨f₁, hf₁def⟩ : ∃ f₁, f₁ = e.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f := ⟨_, rfl⟩
    let W' : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).left.Opens :=
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ W
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :=
      inferInstance
    have hW' : IsAffineOpen W' := hW.preimage _
    have hf₁W : f₁.left ⁻¹ᵁ W' = ⊤ := by
      have h1 : f₁.left ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
          (e.hom.left ≫ pullback.fst _ _) ≫ f.left := by
        rw [hf₁def, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]
      change (f₁.left ≫ pullback.fst G.hom _) ⁻¹ᵁ W = ⊤
      rw [h1, Scheme.Hom.comp_preimage, hfW, Scheme.Hom.preimage_top]
    have hf₁ : IsMonHom ((Over.pullback (Spec.map β')).map f₁) := by
      have h2 : IsMonHom ((Over.pullback (Spec.map β')).map
          ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f)) :=
        (isMonHom_map_iff hSpec f).1 hf
      rw [hf₁def, Functor.map_comp]
      infer_instance
    obtain ⟨f₂, hf₂, hf₂eq⟩ := ih (A ⧸ I) (J.map (Ideal.Quotient.mk I)) hJ' β' hβ' hker'
      ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G) f₁ hf₁ W' hW' hf₁W
    have hf₂W : f₂.left ⁻¹ᵁ W' = ⊤ := preimage_eq_univ_of_pullback_map_eq (Spec.map β') f₁ f₂ hf₂eq.symm W' hf₁W
    obtain ⟨F, -, hF⟩ := exists_lift I hInil X G (e.inv ≫ f₂) hW (by
      change e.inv.left ⁻¹ᵁ (f₂.left ⁻¹ᵁ W') = ⊤
      rw [hf₂W]
      rfl)
    have hFmon : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map F) := by
      rw [hF]
      infer_instance
    obtain ⟨F', hF'1, hF'2⟩ := GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A I hI2 X G F hFmon
    refine ⟨F', hF'1, ?_⟩
    rw [map_eq_iff hSpec, hF'2, hF, Functor.map_comp, hf₂eq, hf₁def, Functor.map_comp,
      ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

theorem exists_correction {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] : IsNilpotent J → IsLocalRing A → ∀ {C : CommRingCat.{0}}
      (β : CommRingCat.of A ⟶ C), Function.Surjective β → RingHom.ker β.hom = J →
      ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
        (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G),
        IsMonHom ((Over.pullback (Spec.map β)).map f) → ∀ W : G.left.Opens, IsAffineOpen W →
        f.left ⁻¹ᵁ W = ⊤ → ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
          (Over.pullback (Spec.map β)).map f' = (Over.pullback (Spec.map β)).map f := by
  intro _ hloc C β hβ hker G _ _ _ f hf W hW hfW
  obtain ⟨n, hn⟩ := hJ
  cases n with
  | zero =>
    exfalso
    rw [pow_zero, Ideal.one_eq_top, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  | succ n =>
    exact exists_isMonHom_lift_of_isMonHom_baseChange X n A J (by rw [hn, Ideal.zero_eq_bot]) β hβ hker G f hf W hW hfW

theorem exists_affineOpen {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G : Over (Spec (CommRingCat.of A)))
    (W : (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).Opens)
    (hW : IsAffineOpen W) : ∃ U : G.left.Opens, IsAffineOpen U ∧
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ U = W := by
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  let i := pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have hemb : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  have hbij : Function.Bijective i.base := ⟨hemb.injective, i.surjective⟩
  have hopen : IsOpen (i.base '' (W : Set _)) := by
    rw [← compl_compl (i.base '' (W : Set _)), ← Set.image_compl_eq hbij]
    exact (hemb.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl
  let U : G.left.Opens := ⟨_, hopen⟩
  have hU : i ⁻¹ᵁ U = W := by
    ext x
    change i.base x ∈ i.base '' (W : Set _) ↔ x ∈ W
    exact hemb.injective.mem_set_image
  refine ⟨U, ?_, hU⟩
  have hW' : IsAffineOpen (i ⁻¹ᵁ U) := hU ▸ hW
  have : IsAffine (pullback (U.ι ≫ G.hom) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    have : IsAffine (i ⁻¹ᵁ U) := hW'
    exact IsAffine.of_isIso ((pullbackRightPullbackFstIso G.hom _ U.ι).inv ≫
      (pullbackSymmetry _ _).hom ≫ (pullbackRestrictIsoRestrict i U).hom)
  exact GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent A J hJ (Over.mk (U.ι ≫ G.hom)) this

theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (i₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G), IsMonHom i₀ → (∃ W : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤) → ∃! i : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom i ∧ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map i = i₀ := by
  intro A _ _ J hJ X _ G _ _ _ i₀ hi₀ ⟨W, hW, hW0⟩
  obtain ⟨U, hU, hUW⟩ := exists_affineOpen J hJ G W hW
  obtain ⟨f, hfU, hf⟩ := exists_lift J hJ X G i₀ hU (by
    rw [Scheme.Hom.comp_preimage, hUW]
    exact hW0)
  obtain ⟨f', hf'1, hf'2⟩ := exists_correction J hJ X hJ inferInstance
    (CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective (by simp) G f
    (by rw [hf]; exact hi₀) U hU hfU
  refine ⟨f', ⟨hf'1, hf'2.trans hf⟩, ?_⟩
  rintro i ⟨hi1, hi2⟩
  open CategoryTheory.GrpObj in
  have hmon : IsMonHom (i * f'⁻¹) := by
    rw [Hom.mul_def]
    infer_instance
  open CategoryTheory.GrpObj in
  have hmap : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (i * f'⁻¹) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (toUnit _ ≫ η[G]) := by
    rw [Functor.map_mul, Functor.map_inv', hi2, hf'2, hf, mul_inv_cancel, ← Hom.one_def, Functor.map_one]
  open CategoryTheory.GrpObj in
  have key := GlobalTheory.splitTorus_hom_eq_one_of_nilpotent A J hJ X G (i * f'⁻¹) hmon hmap
  open CategoryTheory.GrpObj in
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory.TorusLift
