module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem secAlg_toSpecΓ_top (Z : Scheme.{0}) :
    secAlg Γ(Z, ⊤) Z.toSpecΓ ⊤ = RingHom.id _ := by
  ext a
  have e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop := (Scheme.Hom.app_eq_appLE _).symm
  simp only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]
  simp

theorem exists_hom_secAlg_top (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)) :
    ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩
  rw [secAlg_comp, secAlg_toSpecΓ_top]
  rfl

end GlobalTheory.HilbAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHomStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom : ∀ (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)), ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  first | (exact @GlobalTheory.HilbAff.exists_hom_secAlg_top) | (exact GlobalTheory.HilbAff.exists_hom_secAlg_top) | (intros; apply GlobalTheory.HilbAff.exists_hom_secAlg_top  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem good_xI : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  intro A B C _ _ _ _ _ J r v hli hsp
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  haveI : Module.Free C ((C ⊗[A] B) ⧸ J) := Module.Free.of_basis bas
  haveI : Module.Finite C ((C ⊗[A] B) ⧸ J) := Module.Finite.of_basis bas
  have hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom) :=
    (Ideal.Quotient.mk_surjective).comp (Algebra.TensorProduct.comm A B C).surjective
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  have hsnd : (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp
      (Algebra.TensorProduct.comm A B C).toRingHom)) ≫ (pullbackSpecIso A B C).inv) ≫
      pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap C ((C ⊗[A] B) ⧸ J))) := by
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  refine good_ker A B r _ _ ?_ ?_ ?_
  · rw [hsnd]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · rw [hsnd]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  · intro y
    rw [hsnd]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap C ((C ⊗[A] B) ⧸ J) y).trans ?_
    haveI : Nontrivial C := by
      let p : PrimeSpectrum C := y
      refine ⟨⟨0, 1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
      rw [← h]; exact p.asIdeal.zero_mem
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis bas, Fintype.card_fin]
    rfl

end GlobalTheory.HilbAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatRankClosedSubschemeOfQuotientBasisStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) {r : ℕ} (v : Fin r → B), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → GlobalTheory.HilbAff.Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (GlobalTheory.HilbAff.xI A B C J) := by
  first | (exact @GlobalTheory.HilbAff.good_xI) | (exact GlobalTheory.HilbAff.good_xI) | (intros; apply GlobalTheory.HilbAff.good_xI  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestricStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
      (g : T ⟶ Spec (CommRingCat.of A))
      (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
      (U V : T.affineOpens) (h : (U : T.Opens) ≤ V),
      letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
      ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
        (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
          (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤
        RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  intro A B _ _ _ T g I U V h
  let := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  let := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
          (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op) }
  refine ⟨ρ, rfl, ?_⟩
  have kappa_tmul (W : T.Opens) (c : Γ(T, W)) (b : B) :
      letI := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
      GlobalTheory.HilbAff.kappa A B g I W (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd _ g).app W).hom c *
          ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) (by simp)).hom
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
    let := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
    let : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) :=
      (((I.subschemeι ≫ pullback.snd _ g).app W).hom.comp
        (GlobalTheory.HilbAff.secAlg A g W)).toAlgebra
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hκ (t : Γ(T, V) ⊗[A] B) :
      GlobalTheory.HilbAff.kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (GlobalTheory.HilbAff.kappa A B g I V t) := by
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
      have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := rfl
      rw [hc]
      congr 1
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
        rfl
      · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
            (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
            (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
        exact (congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [hκ t, ht, map_zero]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HilbAff.IdealDet
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem comm_fst {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
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
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => comm_fst A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    (letI := (secAlg A g U).toAlgebra
     theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
       ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
         ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    (letI := (secAlg A g U).toAlgebra
     ∀ x : Γ(T, U) ⊗[A] B, kappa A B g I U x =
       (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x)) := by
  letI := (secAlg A g U).toAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; rfl
  | tmul c b =>
    change ((I.subschemeι ≫ pullback.snd (str A B) g).app U).hom c *
      ((I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤
        ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = _
    rw [theta_tmul, map_mul]
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤ ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U)
          (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    congr 1
    rw [← e]; rfl

theorem theta_surjective {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (hU : IsAffineOpen U) : Function.Surjective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (str A B) g)
    inferInstance (isAffineOpen_top _) hU le_top (by simp)
  let R : CommRingCat.{0} := CommRingCat.of (Γ(T, U) ⊗[A] B)
  let k : Γ(T, U) ⟶ R := CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (S := A)).toRingHom
  let h : Γ(Spec (CommRingCat.of B), (str A B) ⁻¹ᵁ ⊤) ⟶ R :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U))).toRingHom
  have w : (str A B).app ⊤ ≫ h = g.appLE ⊤ U le_top ≫ k := by
    ext x
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = x :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom x, by simp⟩
    have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
    have h2 : (str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a) :=
      (congrArg (fun f => f.hom a) h1).symm
    change (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U)))
      ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ((str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      (Algebra.TensorProduct.includeLeft (S := A)) (secAlg A g U a)
    rw [h2, Iso.inv_hom_id_apply]
    exact ((Algebra.TensorProduct.includeRight).commutes a).trans
      ((Algebra.TensorProduct.includeLeft (S := A)).commutes a).symm
  let ψ := hP.desc h k w
  have hθ : ψ ≫ CommRingCat.ofHom (theta A B g U) = 𝟙 _ := by
    apply hP.hom_ext
    · rw [hP.inl_desc_assoc, Category.comp_id]
      ext z
      change theta A B g U ((1 : Γ(T, U)) ⊗ₜ[A] ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z)) = _
      have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z) = z :=
        Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) z
      rw [theta_tmul, map_one, one_mul, e]
      rfl
    · rw [hP.inr_desc_assoc, Category.comp_id]
      ext c
      change theta A B g U (c ⊗ₜ[A] (1 : B)) = _
      rw [theta_tmul, map_one, map_one, mul_one]
  intro y
  exact ⟨ψ y, congrArg (fun F => F.hom y) hθ⟩

theorem eq_of_ker_kappa_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) =
      RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  intro A B _ _ _ T g I₁ I₂ h
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback (str A B) g)
      (inferInstance : IsAffineHom (str A B))
  let W : T.affineOpens → (pullback (str A B) g).affineOpens :=
    fun U => ⟨pullback.snd (str A B) g ⁻¹ᵁ U, U.2.preimage _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ ?_
  · exact (pullback.snd (str A B) g).iSup_preimage_eq_top (iSup_affineOpens_eq_top T)
  · intro U
    letI := (secAlg A g U).toAlgebra
    have key : ∀ I : (pullback (str A B) g).IdealSheafData,
        I.ideal (W U) = Ideal.map (theta A B g U) (RingHom.ker (kappa A B g I U)) := by
      intro I
      have e : RingHom.ker (kappa A B g I U) = Ideal.comap (theta A B g U) (I.ideal (W U)) := by
        ext x
        rw [RingHom.mem_ker, Ideal.mem_comap, ← I.ker_subschemeι_app (W U), RingHom.mem_ker,
          kappa_apply]
        rfl
      rw [e, Ideal.map_comap_of_surjective _ (theta_surjective A B g U U.2)]
    rw [key, key, h U]

end GlobalTheory.HilbAff.IdealDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfKerTensorToSubschemeSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData), (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) = RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  first | (exact @GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (exact GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq) | (intros; apply GlobalTheory.HilbAff.IdealDet.eq_of_ker_kappa_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem quotient_basis_baseChange (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B)
    (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R)
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤) :
    LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧
    Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  set f := Algebra.TensorProduct.map ψ (AlgHom.id A B) with hf
  set J' := J.map f with hJ'
  let bas : Module.Basis (Fin r) C ((C ⊗[A] B) ⧸ J) := Module.Basis.mk hli hsp.ge
  have bas_apply : ∀ k, bas k = Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k) := fun k => Module.Basis.mk_apply _ _ _
  let Φ : (C ⊗[A] B) → (Fin r → R) := fun x k => ψ (bas.repr (Ideal.Quotient.mk J x) k)
  have mkC : ∀ (c : C) (x : C ⊗[A] B), Ideal.Quotient.mk J (c • x) = c • Ideal.Quotient.mk J x :=
    fun c x => map_smul (Ideal.Quotient.mkₐ C J) c x
  have Φ_add : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y; funext k; simp [Φ, map_add (f := _)]
  have Φ_zero : Φ 0 = 0 := by funext k; simp [Φ]
  have Φ_smul : ∀ (c : C) x, Φ (c • x) = ψ c • Φ x := by
    intro c x; funext k
    simp [Φ, mkC]
  have Φ_J : ∀ x ∈ J, Φ x = 0 := by
    intro x hx; funext k; simp [Φ, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have Φ_v : ∀ k, Φ ((1 : C) ⊗ₜ[A] v k) = Pi.single k 1 := by
    intro k; funext j
    simp only [Φ, ← bas_apply, Module.Basis.repr_self]
    by_cases h : j = k
    · subst h; simp
    · simp [Finsupp.single_apply, Pi.single_apply, Ne.symm h, h]
  let g : B →ₗ[A] (Fin r → R) :=
    { toFun := fun b => Φ ((1 : C) ⊗ₜ[A] b)
      map_add' := fun x y => by simp only [TensorProduct.tmul_add]; exact Φ_add _ _
      map_smul' := fun a x => by
        simp only [RingHom.id_apply]
        rw [TensorProduct.tmul_smul, ← algebraMap_smul C a ((1 : C) ⊗ₜ[A] x), Φ_smul,
          AlgHom.commutes, algebraMap_smul] }
  let ℓ : R ⊗[A] B →ₗ[R] (Fin r → R) := LinearMap.liftBaseChange R g
  have ℓ_tmul : ∀ (s : R) (b : B), ℓ (s ⊗ₜ[A] b) = s • Φ ((1 : C) ⊗ₜ[A] b) := by
    intro s b; simp [ℓ, g]
  have key : ∀ x : C ⊗[A] B, ℓ (f x) = Φ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [Φ_zero]
    | tmul c b =>
      rw [hf, Algebra.TensorProduct.map_tmul, ℓ_tmul]
      have : c ⊗ₜ[A] b = c • ((1 : C) ⊗ₜ[A] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, Φ_smul]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, Φ_add]
  have f_smul : ∀ (c : C) (y : C ⊗[A] B), f (c • y) = ψ c • f y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c' b =>
      rw [TensorProduct.smul_tmul', hf, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  have f_one : ∀ b : B, f ((1 : C) ⊗ₜ[A] b) = (1 : R) ⊗ₜ[A] b := by
    intro b; rw [hf, Algebra.TensorProduct.map_tmul, map_one]; rfl
  have kill : ∀ y ∈ J', ℓ y = 0 := by
    let K : Ideal (R ⊗[A] B) :=
      { carrier := {y | ∀ a, ℓ (a * y) = 0}
        add_mem' := fun {x y} hx hy a => by rw [mul_add, map_add (f := _), hx a, hy a, add_zero]
        zero_mem' := fun a => by simp
        smul_mem' := fun c {x} hx a => by
          show ℓ (a * (c * x)) = 0
          rw [← mul_assoc]; exact hx _ }
    have hJK : J' ≤ K := by
      rw [hJ', Ideal.map_le_iff_le_comap]
      intro j hj a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul s b =>
        have : (s ⊗ₜ[A] b) * f j = s • f (((1 : C) ⊗ₜ[A] b) * j) := by
          rw [map_mul, f_one, ← smul_mul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, key, Φ_J _ (J.mul_mem_left _ hj), smul_zero]
      | add x y hx hy => rw [add_mul, map_add (f := _), hx, hy, add_zero]
    intro y hy
    have := hJK hy 1
    simpa using this
  have mkR : ∀ (s : R) (x : R ⊗[A] B), Ideal.Quotient.mk J' (s • x) = s • Ideal.Quotient.mk J' x :=
    fun s x => map_smul (Ideal.Quotient.mkₐ R J') s x
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    have hmem : (∑ k, c k • ((1 : R) ⊗ₜ[A] v k)) ∈ J' := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simpa [mkR] using hc
    have h0 := kill _ hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    simp only [map_smul, ℓ_tmul, one_smul, Φ_v] at h0
    intro i
    have := congrFun h0 i
    simpa [Finset.sum_apply, Pi.single_apply] using this
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hbase : ∀ x : C ⊗[A] B, Ideal.Quotient.mk J' (f x) ∈
        Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J' ((1 : R) ⊗ₜ[A] v k))) := by
      intro x
      have hx := bas.sum_repr (Ideal.Quotient.mk J x)
      set c := bas.repr (Ideal.Quotient.mk J x)
      have hmem : x - ∑ k, c k • ((1 : C) ⊗ₜ[A] v k) ∈ J := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
        simp only [mkC, ← bas_apply]
        rw [hx, sub_self]
      have hmem' : f x - ∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k) ∈ J' := by
        have := Ideal.mem_map_of_mem f hmem
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum] at this
        simpa only [f_smul, f_one] using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sub_add_cancel (f x) (∑ k, ψ (c k) • ((1 : R) ⊗ₜ[A] v k)), map_add (f := _),
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem', zero_add, map_sum]
      refine Submodule.sum_mem _ (fun k _ => ?_)
      rw [mkR]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      have : s ⊗ₜ[A] b = s • f ((1 : C) ⊗ₜ[A] b) := by
        rw [f_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, mkR]
      exact Submodule.smul_mem _ _ (hbase _)
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_quotient_tensor_base_change : ∀ (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  first | (exact @GlobalTheory.quotient_basis_baseChange) | (exact GlobalTheory.quotient_basis_baseChange) | (intros; apply GlobalTheory.quotient_basis_baseChange  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfQuotient
open scoped TensorProduct

namespace GlobalTheory.HilbChart

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
  (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N)

noncomputable def sc (a m b : Fin N) : A := e.repr (e a * e m) b

variable {S : Type} [CommRing S] [Algebra A S]

noncomputable def coord (c : Fin N → Fin r → S) : S ⊗[A] B →ₗ[S] (Fin r → S) :=
  (Algebra.TensorProduct.basis S e).constr S c

noncomputable def ell (c : Fin N → Fin r → S) (m : Fin N) : S ⊗[A] B :=
  (1 : S) ⊗ₜ[A] e m - ∑ k, c m k • ((1 : S) ⊗ₜ[A] e (σ k))

noncomputable def chartIdeal (c : Fin N → Fin r → S) : Ideal (S ⊗[A] B) :=
  Ideal.span (Set.range (ell e σ c))

noncomputable def mulDefect (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) : S :=
  ∑ b, algebraMap A S (sc e a m b) * c b k -
    ∑ k', c m k' * ∑ b, algebraMap A S (sc e a (σ k') b) * c b k

def IsChart (c : Fin N → Fin r → S) : Prop :=
  (∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k') ∧ ∀ a m k, mulDefect e σ c a m k = 0

end GlobalTheory.HilbChart

namespace GlobalTheory.HilbChart
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
  (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {S : Type} [CommRing S] [Algebra A S]

theorem coord_one_tmul_basis (c : Fin N → Fin r → S) (m : Fin N) :
    coord e c ((1:S) ⊗ₜ e m) = c m := by
  rw [← Algebra.TensorProduct.basis_apply]; exact Module.Basis.constr_basis _ _ _ _

theorem sum_smul_single (v : Fin r → S) : ∑ k, v k • (Pi.single k (1:S) : Fin r → S) = v := by
  funext j; simp [Finset.sum_apply, Pi.single_apply]

theorem coord_apply (c : Fin N → Fin r → S) (y : S ⊗[A] B) :
    coord e c y = ∑ m, (Algebra.TensorProduct.basis S e).repr y m • c m := by
  rw [coord, Module.Basis.constr_apply, Finsupp.sum_fintype]; simp

theorem coord_one_tmul (c : Fin N → Fin r → S) (x : B) :
    coord e c ((1:S) ⊗ₜ x) = ∑ b, e.repr x b • c b := by
  conv_lhs => rw [← e.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.tmul_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul_of_tower, coord_one_tmul_basis]

theorem decomp (c : Fin N → Fin r → S) (y : S ⊗[A] B) :
    y = ∑ m, (Algebra.TensorProduct.basis S e).repr y m • ell e σ c m +
      ∑ k, coord e c y k • ((1:S) ⊗ₜ[A] e (σ k)) := by
  set bS := Algebra.TensorProduct.basis S e
  rw [coord_apply]
  simp only [ell, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
  rw [Finset.sum_comm (γ := Fin r)]
  have : ∑ m, bS.repr y m • ((1:S) ⊗ₜ[A] e m) = y := by
    conv_rhs => rw [← bS.sum_repr y]
    simp [bS]
  rw [this]; abel

theorem coord_sigma {c : Fin N → Fin r → S} (hc : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k')
    (k : Fin r) : c (σ k) = Pi.single k 1 := funext (hc k)

theorem coord_ell {c : Fin N → Fin r → S} (hc : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k')
    (m : Fin N) : coord e c (ell e σ c m) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc, sum_smul_single, sub_self]

theorem coord_mul_ell (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) :
    coord e c (((1:S) ⊗ₜ[A] e a) * ell e σ c m) k = mulDefect e σ c a m k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ell, mul_sub, Finset.mul_sum, mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    map_sub, map_sum, map_smul, coord_one_tmul]
  simp only [mulDefect, sc, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum]

theorem coord_mul_eq_zero {c : Fin N → Fin r → S} (hc : IsChart e σ c) (z y : S ⊗[A] B)
    (hy : coord e c y = 0) : coord e c (z * y) = 0 := by
  set bS := Algebra.TensorProduct.basis S e
  have hy' : y = ∑ m, bS.repr y m • ell e σ c m := by
    have := decomp e σ c y; rw [hy] at this; simpa using this
  rw [← bS.sum_repr z, hy']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun m _ => ?_
  have : coord e c (bS m * ell e σ c a) = 0 := by
    funext k; rw [Algebra.TensorProduct.basis_apply, coord_mul_ell]; exact hc.2 m a k
  rw [this, smul_zero]

theorem mem_chartIdeal_iff {c : Fin N → Fin r → S} (hc : IsChart e σ c) (y : S ⊗[A] B) :
    y ∈ chartIdeal e σ c ↔ coord e c y = 0 := by
  constructor
  · intro hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, rfl⟩; exact coord_ell e σ hc.1 m
    · simp
    · intro u v _ _ hu hv; rw [map_add (f := _), hu, hv, add_zero]
    · intro z u _ hu; exact coord_mul_eq_zero e σ hc z u hu
  · intro hy
    rw [decomp e σ c y, hy]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)

theorem mk_smul (J : Ideal (S ⊗[A] B)) (s : S) (y : S ⊗[A] B) :
    Ideal.Quotient.mk J (s • y) = s • Ideal.Quotient.mk J y := rfl

theorem sum_smul_tmul_sigma (c : Fin N → Fin r → S) (v : Fin r → S) (hc : ∀ k, c (σ k) = Pi.single k 1) :
    coord e c (∑ k, v k • ((1:S) ⊗ₜ[A] e (σ k))) = v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, coord_one_tmul_basis, hc, sum_smul_single]

theorem quotient_basis {c : Fin N → Fin r → S} (hc : IsChart e σ c) :
    LinearIndependent S (fun k => Ideal.Quotient.mk (chartIdeal e σ c) ((1 : S) ⊗ₜ[A] e (σ k))) ∧
    Submodule.span S (Set.range (fun k => Ideal.Quotient.mk (chartIdeal e σ c) ((1 : S) ⊗ₜ[A] e (σ k)))) = ⊤ := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← mk_smul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem, mem_chartIdeal_iff e σ hc] at hg
    rw [sum_smul_tmul_sigma e σ c g (coord_sigma σ hc.1)] at hg
    intro k; rw [hg]; rfl
  · rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [decomp e σ c y, map_add (f := _), map_sum, map_sum]
    have h0 : ∀ m, Ideal.Quotient.mk (chartIdeal e σ c)
        ((Algebra.TensorProduct.basis S e).repr y m • ell e σ c m) = 0 := fun m => by
      rw [Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
    simp only [h0, Finset.sum_const_zero, zero_add]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mk_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

variable {S' : Type} [CommRing S'] [Algebra A S']

theorem map_ell (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) (m : Fin N) :
    Algebra.TensorProduct.map φ (AlgHom.id A B) (ell e σ c m) = ell e σ (fun m k => φ (c m k)) m := by
  simp [ell, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_chartIdeal (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) :
    (chartIdeal e σ c).map (Algebra.TensorProduct.map φ (AlgHom.id A B)) =
      chartIdeal e σ (fun m k => φ (c m k)) := by
  rw [chartIdeal, chartIdeal, Ideal.map_span, ← Set.range_comp]
  have : (⇑(Algebra.TensorProduct.map φ (AlgHom.id A B)) ∘ ell e σ c) =
      ell e σ (fun m k => φ (c m k)) := funext (map_ell e σ φ c)
  rw [this]

theorem eq_of_chartIdeal_le {c d : Fin N → Fin r → S} (hc : IsChart e σ c)
    (h : chartIdeal e σ d ≤ chartIdeal e σ c) : c = d := by
  funext m
  have h1 := (mem_chartIdeal_iff e σ hc _).1 (h (Ideal.subset_span ⟨m, rfl⟩))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ell, map_sub, map_sum, map_smul, coord_one_tmul_basis, coord_sigma σ hc.1,
    sum_smul_single] at h1
  exact sub_eq_zero.1 h1

theorem exists_chart_of_quotient (J : Ideal (S ⊗[A] B))
    (hli : LinearIndependent S (fun k => Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span S (Set.range (fun k => Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k)))) = ⊤) :
    ∃ c : Fin N → Fin r → S, IsChart e σ c ∧ chartIdeal e σ c = J := by
  let bq := Module.Basis.mk hli hsp.ge
  let c : Fin N → Fin r → S := fun m k => bq.repr (Ideal.Quotient.mk J ((1:S) ⊗ₜ[A] e m)) k
  have hbq : ∀ k, bq k = Ideal.Quotient.mk J ((1 : S) ⊗ₜ[A] e (σ k)) := fun k => Module.Basis.mk_apply _ _ _
  have ha : ∀ k k', c (σ k) k' = Pi.single (M := fun _ => S) k 1 k' := by
    intro k k'
    simp only [c, ← hbq, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
    by_cases h : k = k'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hell : ∀ m, Ideal.Quotient.mk J (ell e σ c m) = 0 := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ell, map_sub, map_sum, mk_smul, ← hbq]
    rw [sub_eq_zero]
    exact (bq.sum_repr _).symm
  have hq : ∀ y, Ideal.Quotient.mk J y = ∑ k, coord e c y k • bq k := by
    intro y
    conv_lhs => rw [decomp e σ c y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, mk_smul, hell, smul_zero, Finset.sum_const_zero, zero_add, hbq]
  have hmem : ∀ y, y ∈ J ↔ coord e c y = 0 := by
    intro y
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq y]
    constructor
    · intro h
      exact funext ((Fintype.linearIndependent_iff.1 bq.linearIndependent) _ h)
    · intro h; simp [h]
  have hc : IsChart e σ c := by
    refine ⟨ha, fun a m k => ?_⟩
    rw [← coord_mul_ell]
    have : ell e σ c m ∈ J := (hmem _).2 (coord_ell e σ ha m)
    rw [(hmem _).1 (J.mul_mem_left _ this)]; rfl
  refine ⟨c, hc, ?_⟩
  ext y
  rw [mem_chartIdeal_iff e σ hc, hmem]

theorem mulDefect_map (φ : S →ₐ[A] S') (c : Fin N → Fin r → S) (a m : Fin N) (k : Fin r) :
    mulDefect e σ (fun m k => φ (c m k)) a m k = φ (mulDefect e σ c a m k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mulDefect, map_sub, map_sum, map_mul, AlgHom.commutes]

noncomputable def rels : (Fin r × Fin r) ⊕ (Fin N × Fin N × Fin r) → MvPolynomial (Fin N × Fin r) A
  | .inl p => MvPolynomial.X (σ p.1, p.2) - MvPolynomial.C (Pi.single (M := fun _ => A) p.1 1 p.2)
  | .inr p => mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) p.1 p.2.1 p.2.2

theorem isChart_iff_aeval (c : Fin N → Fin r → S) :
    IsChart e σ c ↔ ∀ i, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2) (rels e σ i) = 0 := by
  have hd : ∀ a m k, MvPolynomial.aeval (fun p : Fin N × Fin r => c p.1 p.2)
      (mulDefect e σ (fun m k => (MvPolynomial.X (m, k) : MvPolynomial (Fin N × Fin r) A)) a m k) =
      mulDefect e σ c a m k := by
    intro a m k
    rw [← mulDefect_map]; simp
  have hs : ∀ k k' : Fin r, algebraMap A S (Pi.single (M := fun _ => A) k 1 k') =
      Pi.single (M := fun _ => S) k 1 k' := by
    intro k k'; by_cases h : k' = k <;> simp [Pi.single_apply, h]
  constructor
  · rintro ⟨ha, hb⟩ (⟨k, k'⟩ | ⟨a, m, k⟩)
    · simp [rels, ha, hs]
    · simp only [rels]; rw [hd, hb]
  · intro h
    refine ⟨fun k k' => ?_, fun a m k => ?_⟩
    · have := h (.inl (k, k'))
      simp only [rels, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, hs] at this
      exact sub_eq_zero.1 this
    · have := h (.inr (a, m, k))
      simp only [rels] at this; rwa [hd] at this

noncomputable def relIdeal : Ideal (MvPolynomial (Fin N × Fin r) A) := Ideal.span (Set.range (rels e σ))

abbrev ChartRing := MvPolynomial (Fin N × Fin r) A ⧸ relIdeal e σ

noncomputable def univChart : Fin N → Fin r → ChartRing e σ :=
  fun m k => Ideal.Quotient.mk (relIdeal e σ) (MvPolynomial.X (m, k))

theorem isChart_univChart : IsChart e σ (univChart e σ) := by
  rw [isChart_iff_aeval]
  intro i
  have : MvPolynomial.aeval (fun p : Fin N × Fin r => univChart e σ p.1 p.2) =
      Ideal.Quotient.mkₐ A (relIdeal e σ) := by
    apply MvPolynomial.algHom_ext; intro p; simp [univChart]
  rw [this, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

end GlobalTheory.HilbChart

open GlobalTheory.HilbChart in
theorem GlobalTheory.hilbChart_representable : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (J : Ideal (C ⊗[A] B)), Algebra.FinitePresentation A C ∧ LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))) ∧ Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤ ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)), LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) → Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ → ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)) := by
  intro A B _ _ _ N r e σ
  have hC := isChart_univChart e σ
  refine ⟨ChartRing e σ, inferInstance, inferInstance, chartIdeal e σ (univChart e σ), ?_,
    (quotient_basis e σ hC).1, (quotient_basis e σ hC).2, ?_⟩
  · exact Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  · intro A' _ _ J' hli hsp
    obtain ⟨c, hc, hJ⟩ := exists_chart_of_quotient e σ J' hli hsp
    let ψ : MvPolynomial (Fin N × Fin r) A →ₐ[A] A' := MvPolynomial.aeval (fun p => c p.1 p.2)
    have hψ : ∀ a ∈ relIdeal e σ, ψ a = 0 := by
      intro a ha
      have hle : relIdeal e σ ≤ RingHom.ker ψ := by
        rw [relIdeal, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact (isChart_iff_aeval e σ c).1 hc i
      exact hle ha
    let φ : ChartRing e σ →ₐ[A] A' := Ideal.Quotient.liftₐ _ ψ hψ
    have hφ : (fun m k => φ (univChart e σ m k)) = c := by
      funext m k
      change ψ (MvPolynomial.X (m, k)) = c m k
      simp [ψ]
    refine ⟨φ, ?_, ?_⟩
    · show J' = _
      rw [map_chartIdeal, hφ, hJ]
    · intro φ' hφ'
      rw [map_chartIdeal, ← hJ] at hφ'
      have h1 : c = fun m k => φ' (univChart e σ m k) := eq_of_chartIdeal_le e σ hc hφ'.ge
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro p
      have h2 := congrFun (congrFun (h1.symm.trans hφ.symm) p.1) p.2
      simpa [univChart] using h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertChartRepresentable
namespace GlobalTheory.HilbAff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem exists_unique_lift (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {N r : ℕ}
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (C : Type) [CommRing C] [Algebra A C]
    (J : Ideal (C ⊗[A] B))
    (hli : LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k))))
    (hsp : Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] e (σ k)))) = ⊤)
    (huniv : ∀ (A' : Type) [CommRing A'] [Algebra A A'] (J' : Ideal (A' ⊗[A] B)),
      LinearIndependent A' (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k))) →
      Submodule.span A' (Set.range (fun k => Ideal.Quotient.mk J' ((1 : A') ⊗ₜ[A] e (σ k)))) = ⊤ →
      ∃! φ : C →ₐ[A] A', J' = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)))
    (hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J))
    (Z : Scheme.{0}) (g : Z ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (hI : Good A B r g I)
    (hy : ∀ U : Z.affineOpens, letI := (secAlg A g U).toAlgebra
      Function.Bijective fun c : Fin r → Γ(Z, U) => kappa A B g I U (∑ k, c k ⊗ₜ[A] e (σ k))) :
    ∃! h : Z ⟶ Spec (CommRingCat.of C), (functor A B r).map h.op
      (⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩ :
        (functor A B r).obj (op (Spec (CommRingCat.of C)))) = ⟨g, ⟨I, hI⟩⟩ := by
  have hch : ∀ U : Z.affineOpens, ∃ φ : C →+* Γ(Z, U), ∃ hφ : ∀ a : A,
      φ (algebraMap A C a) = secAlg A g U a,
      letI := (secAlg A g U).toAlgebra
      RingHom.ker (kappa A B g I U) = J.map (Algebra.TensorProduct.map
        ({ toRingHom := φ, commutes' := hφ } : C →ₐ[A] Γ(Z, U)) (AlgHom.id A B)) ∧
      ∀ ψ : C →ₐ[A] Γ(Z, U), RingHom.ker (kappa A B g I U) =
        J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B)) → ψ.toRingHom = φ := by
    intro U
    letI := (secAlg A g U).toAlgebra
    obtain ⟨-, hli', hsp'⟩ := (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)
    obtain ⟨φ, hφ, hφu⟩ := huniv Γ(Z, U) _ hli' hsp'
    exact ⟨φ.toRingHom, φ.commutes, hφ, fun ψ hψ => congrArg AlgHom.toRingHom (hφu ψ hψ)⟩
  choose φ hφA hφ hφu using hch
  have compat : ∀ (U V : Z.affineOpens) (hUV : (U : Z.Opens) ≤ V),
      (Z.presheaf.map (homOfLE hUV).op).hom.comp (φ V) = φ U := by
    intro U V hUV
    letI iU := (secAlg A g U).toAlgebra
    letI iV := (secAlg A g V).toAlgebra
    obtain ⟨ρ, hρ, hle⟩ := GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict A B g I U V hUV
    let φV : C →ₐ[A] Γ(Z, V) := { toRingHom := φ V, commutes' := hφA V }
    have hmap : J.map (Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B)) =
        (RingHom.ker (kappa A B g I V)).map (Algebra.TensorProduct.map ρ (AlgHom.id A B)) := by
      rw [hφ V, show Algebra.TensorProduct.map (ρ.comp φV) (AlgHom.id A B) =
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).comp
          (Algebra.TensorProduct.map φV (AlgHom.id A B)) by
        rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]]
      exact (Ideal.map_map (Algebra.TensorProduct.map φV (AlgHom.id A B)).toRingHom
        (Algebra.TensorProduct.map ρ (AlgHom.id A B)).toRingHom).symm
    have hsp2 := (GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J (ρ.comp φV) hli hsp).2
    have hliU := ((GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mp (hy U)).2.1
    have heq := GlobalTheory.T.ideals_eq_of_span_independent A B Γ(Z, U) (fun k => e (σ k)) _ _ (hmap ▸ hle) hsp2 hliU
    rw [← hφu U (ρ.comp φV) heq.symm, ← hρ]
    rfl
  obtain ⟨Φ, hΦ, hΦu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z C φ compat
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom Z C Φ
  have hhU : ∀ U : Z.affineOpens, secAlg C h U = φ U := fun U => by
    rw [← secAlg_res C h (le_top : (U : Z.Opens) ≤ ⊤), hh, hΦ U]
  have hgA : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g := by
    apply eq_of_secAlg_top
    rw [secAlg_comp, hh]
    obtain ⟨Ψ, -, hΨu⟩ := GlobalTheory.T.ring_map_from_affine_opens Z A (fun U => secAlg A g U) (fun U V hUV => secAlg_res A g hUV)
    have h1 := hΨu (Φ.comp (algebraMap A C)) (fun U => by
      rw [← RingHom.comp_assoc, hΦ U]; ext a; exact hφA U a)
    have h2 := hΨu (secAlg A g ⊤) (fun U => secAlg_res A g le_top)
    rw [h1, h2]
  refine ⟨h, ?_, ?_⟩
  · subst hgA
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    apply GlobalTheory.T.idealSheaf_eq_of_ker_tensorToSubschemeSections
    intro U
    obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    refine (hker.trans ?_).trans (hφ U).symm
    congr 2
    exact AlgHom.ext fun c => congrArg (fun F => F c) (hφ'.trans (hhU U))
  · intro h' hh'
    have hU : ∀ U : Z.affineOpens, secAlg C h' U = φ U := by
      intro U
      obtain ⟨φ', hφ', hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h' U
      cases hh'
      rw [← hφ']
      exact hφu U φ' hker
    have hΦ' : secAlg C h' ⊤ = Φ := hΦu _ (fun U => by rw [secAlg_res, hU U])
    exact eq_of_secAlg_top C (hΦ'.trans hh.symm)

theorem chart_represents (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) :
    ∃ (X : Scheme.{0}) (x : (functor A B r).obj (op X)), IsAffine X ∧ LocallyOfFiniteType x.1 ∧
      Basic A B e σ x ∧ ∀ (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)), Basic A B e σ y →
        ∃! g : Z ⟶ X, (functor A B r).map g.op x = y := by
  obtain ⟨C, _, _, J, hfp, hli, hsp, huniv⟩ := GlobalTheory.hilbChart_representable A B N r e σ
  have hgood : Good A B r (Spec.map (CommRingCat.ofHom (algebraMap A C))) (xI A B C J) :=
    GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_quotient_basis A B C J (fun k => e (σ k)) hli hsp
  let x : (functor A B r).obj (op (Spec (CommRingCat.of C))) :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap A C)), ⟨xI A B C J, hgood⟩⟩
  have hBx : ∀ (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)),
      Basic A B e σ ((functor A B r).map h.op x) := by
    intro Z h
    rw [functor_map, basic_iff_kappa]
    intro U
    obtain ⟨φ, -, hker⟩ := GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map A B C J Z h U
    letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
    obtain ⟨hli', hsp'⟩ := GlobalTheory.T.basis_quotient_tensor_base_change A B C Γ(Z, U) (fun k => e (σ k)) J φ hli hsp
    refine (GlobalTheory.T.tensor_basis_criterion A B Γ(Z, U) _ _ (fun k => e (σ k))).mpr ⟨GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective A B _ _ U, ?_, ?_⟩
    · rw [hker]; exact hli'
    · rw [hker]; exact hsp'
  have hBasic : Basic A B e σ x := by
    simpa using hBx _ (𝟙 _)
  refine ⟨Spec (CommRingCat.of C), x, inferInstance, ?_, hBasic, ?_⟩
  · show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A C)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    haveI := hfp
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  intro Z y hy
  obtain ⟨g, I, hI⟩ := y
  rw [basic_iff_kappa] at hy
  exact exists_unique_lift A B e σ C J hli hsp huniv hgood Z g I hI hy
end GlobalTheory.HilbAff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertChartRepresentableStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertChart_representable : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N), ∃ (X : Scheme.{0}) (x : (GlobalTheory.HilbAff.functor A B r).obj (op X)), IsAffine X ∧ LocallyOfFiniteType x.1 ∧ GlobalTheory.HilbAff.Basic A B e σ x ∧ ∀ (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), GlobalTheory.HilbAff.Basic A B e σ y → ∃! g : Z ⟶ X, (GlobalTheory.HilbAff.functor A B r).map g.op x = y := by
  first | (exact @GlobalTheory.HilbAff.chart_represents) | (exact GlobalTheory.HilbAff.chart_represents) | (intros; apply GlobalTheory.HilbAff.chart_represents <;> assumption)
end
