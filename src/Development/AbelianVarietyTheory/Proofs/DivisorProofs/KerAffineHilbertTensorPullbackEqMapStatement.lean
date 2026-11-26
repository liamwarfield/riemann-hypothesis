module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaApplyEq
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem theta_comm {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (str A B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    congrArg (fun f => f.hom a) h1
  have key : (str A B).appTop ≫ (pullback.fst (str A B) g).appLE ⊤
      ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) =
      g.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
    calc _ = (pullback.fst (str A B) g ≫ str A B).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = (pullback.snd (str A B) g ≫ g).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          appLE_eq_of_eq (by simp [pullback.condition]) _ _ _ _
      _ = _ := by
          rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h2, secAlg, RingHom.comp_apply, ← CommRingCat.comp_apply, key, CommRingCat.comp_apply]

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra;
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => theta_comm A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra;
    theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
      ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U)
        (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) (x : letI := (secAlg A g U).toAlgebra; Γ(T, U) ⊗[A] B) :
    kappa A B g I U x =
      (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x) := by
  letI := (secAlg A g U).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hk : kappa A B g I U (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom c *
          ((I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
      letI : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) :=
        (((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [hk, theta_tmul, map_mul]
    congr 1
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
          ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    rw [← e]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl

theorem ker_kappa_eq {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    RingHom.ker (kappa A B g I U) =
      Ideal.comap (theta A B g U) (RingHom.ker (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom) := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker, kappa_apply_eq]; exact Iff.rfl

def psi (C : Type) [CommRing C] [Algebra A C] :
    C ⊗[A] B →+* Γ(pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C))), ⊤) :=
  (pullbackSpecIso A B C).hom.appTop.hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv.hom.comp
      (Algebra.TensorProduct.comm A C B).toRingHom)

end GlobalTheory.HilbAff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem theta_bijective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens) :
    Function.Bijective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have P₁ := CommRingCat.isPushout_tensorProduct A Γ(T, U) B
  have P₂ : IsPushout (CommRingCat.ofHom (algebraMap A Γ(T, U)))
      (CommRingCat.ofHom (algebraMap A B))
      ((pullback.snd (str A B) g).app U)
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (pullback.fst (str A B) g).appLE ⊤ W (by simp)) := by
    refine po.flip.of_iso (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of B)) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Iso.inv_comp_eq]; rfl
    · have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
      rw [← h1, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    · rw [Scheme.Hom.app_eq_appLE]; rfl
    · simp
  have e : CommRingCat.ofHom (theta A B g U) = (P₁.isoIsPushout _ _ P₂).hom := by
    apply P₁.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]
      ext c
      have := theta_tmul A B g U c 1
      simp only [map_one, mul_one] at this
      exact this
    · rw [IsPushout.inr_isoIsPushout_hom]
      ext b
      have := theta_tmul A B g U 1 b
      simp only [map_one, one_mul] at this
      exact this
  have : IsIso (CommRingCat.ofHom (theta A B g U)) := by rw [e]; infer_instance
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom (theta A B g U))

end GlobalTheory.HilbAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionTensorPullbackRingHom_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens), Function.Bijective (GlobalTheory.HilbAff.theta A B g U) := by
  first | (exact @GlobalTheory.HilbAff.theta_bijective) | (exact GlobalTheory.HilbAff.theta_bijective) | (intros; apply GlobalTheory.HilbAff.theta_bijective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem xI_ideal_top (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    (J : Ideal (C ⊗[A] B)) :
    (GlobalTheory.HilbAff.xI A B C J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (GlobalTheory.HilbAff.psi A B C) := by
  set X := pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C))) with hX
  set e := pullbackSpecIso A B C
  set q : CommRingCat.of (B ⊗[A] C) ⟶ CommRingCat.of ((C ⊗[A] B) ⧸ J) :=
    CommRingCat.ofHom ((Ideal.Quotient.mk J).comp (Algebra.TensorProduct.comm A B C).toRingHom) with hq
  set f : Spec (CommRingCat.of ((C ⊗[A] B) ⧸ J)) ⟶ X := Spec.map q ≫ e.inv with hf
  have hxI : xI A B C J = f.ker := rfl
  have h1 : e.hom.appTop ≫ f.appTop = (Spec.map q).appTop := by
    rw [hf, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
    simp
  have h2 := Scheme.ΓSpecIso_inv_naturality q
  have hcomp : f.appTop.hom.comp (psi A B C) =
      (Scheme.ΓSpecIso (CommRingCat.of ((C ⊗[A] B) ⧸ J))).inv.hom.comp (Ideal.Quotient.mk J) := by
    refine RingHom.ext fun x => ?_
    simp only [psi, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, h1, ← h2, CommRingCat.comp_apply]
    congr 1
    simp only [hq, CommRingCat.hom_ofHom, RingHom.comp_apply]
    congr 1
    rw [← Algebra.TensorProduct.comm_symm]
    exact (Algebra.TensorProduct.comm A B C).apply_symm_apply x
  have hsurj : Function.Surjective (psi A B C) := by
    intro y
    refine ⟨(Algebra.TensorProduct.comm A C B).symm
      ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).hom.hom ((pullbackSpecIso A B C).inv.appTop.hom y)), ?_⟩
    simp only [psi, RingHom.comp_apply]
    have h3 : (pullbackSpecIso A B C).inv.appTop ≫ (pullbackSpecIso A B C).hom.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; rfl
    have h5 : ∀ z, (Algebra.TensorProduct.comm A C B).toRingEquiv.toRingHom
        ((Algebra.TensorProduct.comm A C B).symm z) = z := fun z =>
      (Algebra.TensorProduct.comm A C B).apply_symm_apply z
    have h6 : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).hom.hom z) = z := fun z => by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    rw [h5, h6, ← CommRingCat.comp_apply, h3, CommRingCat.id_apply]
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of ((C ⊗[A] B) ⧸ J))).inv.hom := by
    intro a b h
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ((C ⊗[A] B) ⧸ J))).hom.hom h
    simpa using this
  have hker : RingHom.ker f.appTop.hom = J.map (psi A B C) := by
    rw [← Ideal.map_comap_of_surjective _ hsurj (RingHom.ker f.appTop.hom), RingHom.comap_ker, hcomp]
    congr 1
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
  rw [hxI, Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, hker]
  convert Ideal.map_id _
  rw [show ∀ h : (⊤ : X.Opens) ≤ ⊤, homOfLE h = 𝟙 _ from fun _ => Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory.HilbAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTopStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)), (GlobalTheory.HilbAff.xI A B C J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (GlobalTheory.HilbAff.psi A B C) := by
  first | (exact @GlobalTheory.HilbAff.xI_ideal_top) | (exact GlobalTheory.HilbAff.xI_ideal_top) | (intros; apply GlobalTheory.HilbAff.xI_ideal_top  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem IdealSheafData.ideal_comap_affineOpen_of_isAffine {X Y : Scheme.{0}} [IsAffine Y]
    (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens) :
    (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  haveI : IsAffine (W.1 : Scheme) := W.2
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (K.comap f) W.1.ι
    ⟨⊤, isAffineOpen_top _⟩
  rw [← Scheme.IdealSheafData.comap_comp, IdealSheafData.ideal_comap_top_of_isAffine] at h1
  have hc : (W.1.ι ≫ f).appTop ≫ (W.1.ι.appIso ⊤).inv = f.appLE ⊤ (W.1.ι ''ᵁ ⊤) (by simp) := by
    simp [Scheme.Hom.appLE]; exact Category.comp_id _
  have hs : Function.Surjective (W.1.ι.appIso ⊤).inv.hom :=
    (W.1.ι.appIso ⊤).commRingCatIsoToRingEquiv.symm.surjective
  have h2 : (K.comap f).ideal ⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ =
      Ideal.map (f.appLE ⊤ (Subtype.val (⟨W.1.ι ''ᵁ ⊤,
        (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens)) (by simp)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rw [← hc, CommRingCat.hom_comp, ← Ideal.map_map, h1, Ideal.map_comap_of_surjective _ hs]
  have hW : (⟨W.1.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.1.ι⟩ : X.affineOpens) = W :=
    Subtype.ext (by simp)
  have key : ∀ V : X.affineOpens, V = W →
      (K.comap f).ideal V = Ideal.map (f.appLE ⊤ V.1 (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) →
      (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (fun _ _ => trivial)).hom
        (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    rintro V rfl h; exact h
  exact key _ hW h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafComapIdealAffineOpenOfIsAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine : ∀ {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) (K : Y.IdealSheafData) (W : X.affineOpens), (K.comap f).ideal W = Ideal.map (f.appLE ⊤ W (by simp)).hom (K.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | (exact @GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine) | (exact GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine) | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_affineOpen_of_isAffine  <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open GlobalTheory.HilbAff in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C))
      (U : Z.affineOpens),
      (letI := (GlobalTheory.HilbAff.secAlg A
        (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U ∧
         RingHom.ker (GlobalTheory.HilbAff.kappa A B
           (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))
           ((GlobalTheory.HilbAff.xI A B C J).comap
             (GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) =
         J.map (Algebra.TensorProduct.map φ (AlgHom.id A B))) := by
  intro A B C _ _ _ _ _ J Z h U
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let g := h ≫ f
  let W := pullback.snd (str A B) g ⁻¹ᵁ (U : Z.Opens)
  let := (secAlg A g U).toAlgebra
  let φ : C →ₐ[A] Γ(Z, U) :=
    { toRingHom := secAlg C h U
      commutes' := fun a => by
        have hs : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appLE ⊤ U (by simp) =
            CommRingCat.ofHom (algebraMap A C) ≫
              (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ h.appLE ⊤ U (by simp) := by
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
                h.appLE ⊤ U (by simp) :=
              congrArg (_ ≫ ·) (Scheme.Hom.comp_appLE h f ⊤ U (by simp))
            _ = _ := (Scheme.ΓSpecIso_inv_naturality_assoc
              (CommRingCat.ofHom (algebraMap A C)) (h.appLE ⊤ U (by simp))).symm
        exact (congrArg (fun F => F.hom a) hs).symm }
  refine ⟨φ, rfl, ?_⟩
  have : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have hTensor : ((bc A B f h).appLE ⊤ W (by simp)).hom.comp (psi A B C) =
      (theta A B g U).comp (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom := by
    have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (pullback.fst (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ (pullback.snd (str A B) f).appTop =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫
            (pullbackSpecIso A B C).hom.appTop := by
      dsimp [f]
      rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    have hpsi (c : C) (b : B) : psi A B C (c ⊗ₜ[A] b) =
        (pullback.fst (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        (pullback.snd (str A B) f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
      have h1 := congrArg (fun F => F.hom b) eL
      have h2 := congrArg (fun F => F.hom c) eR
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      rw [h1, h2, ← map_mul, ← map_mul]
      simp [psi]
    have eF : (pullback.fst (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        (pullback.fst (str A B) g).appLE ⊤ W (by simp) := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
    have eS : (pullback.snd (str A B) f).appTop ≫ (bc A B f h).appLE ⊤ W (by simp) =
        h.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
      refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
      refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) g ≫ h)
        (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul c b =>
      have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
      have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
      rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, mul_comm]
      let : Algebra A Γ(pullback (str A B) g, W) :=
        (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
      symm
      change theta A B g U (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) g).app U).hom (secAlg C h U c) *
          ((pullback.fst (str A B) g).appLE ⊤ W (by simp)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hk := Scheme.IdealSheafData.ker_subschemeι_app
    ((xI A B C J).comap (bc A B f h)) ⟨W, hW⟩
  rw [ker_kappa_eq]
  erw [hk]
  rw [GlobalTheory.T.idealSheaf_comap_ideal_affineOpen_of_isAffine,
    GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top, Ideal.map_map, hTensor,
    ← Ideal.map_map, Ideal.comap_map_of_bijective _
      (GlobalTheory.T.sectionTensorPullbackRingHom_bijective A B _ U)]
  rfl
