module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturality
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

theorem restrict_idealPow_lift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  intro A _ _ I X Z _ _ φ V hV _
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro hcomp G _ m
  haveI : (G.restrict (φ ⁻¹ᵁ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hf : (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) ≫
      cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m)) = 0 := by
    refine hom_eq_zero_of_affineOpens _ fun U s ↦ ?_
    have hU : IsAffineOpen (U : (φ ⁻¹ᵁ V).toScheme.Opens) := U.2
    have hU' : IsAffineOpen ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) :=
      hU.image_of_isOpenImmersion _
    have h1 : (idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s ∈
        (Ideal.map (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule _ _) :=
      (Set.ext_iff.1 (range_idealPowι_app I G hU' m) _).1 ⟨s, rfl⟩
    have hJ : ∀ a ∈ Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m),
        ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom a ∈
          Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) := by
      intro a ha
      have h := Ideal.mem_map_of_mem ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom.hom ha
      rw [Ideal.map_map] at h
      rw [← Ideal.map_pow, Ideal.map_map]
      convert h using 2
      ext r
      exact (hcomp U r).symm
    have h2 : ∀ x ∈ (Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))),
        (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens))) := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x ↦ (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens)))) hx ?_ ?_
      · intro a ha y _
        show _ ∈ _
        rw [Scheme.Modules.smul_restrictAppIso_inv_apply]
        exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
      · intro y z hy hz
        show _ ∈ _
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hy hz
    obtain ⟨y, hy⟩ := (Set.ext_iff.1 (range_idealPowι_app
      (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) hU m) _).2 (h2 _ h1)
    change (cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m))).app (U : (φ ⁻¹ᵁ V).toScheme.Opens)
      ((G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv
        ((idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s)) = 0
    rw [← hy, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, kernel.condition,
      Scheme.Modules.Hom.zero_app]
    rfl
  exact ⟨kernel.lift _ _ hf, kernel.lift_ι _ _ _⟩

end GlobalTheory.CompanionTheory.GE.FormalShift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturalityStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_restriction_functions_naturality : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | exact GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | (intros; apply GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.RingCompat

attribute [local instance] algebraOfOver

lemma topIso_inv_res_hom {X : Scheme.{0}} (V : X.Opens) :
    X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op ≫ V.topIso.inv = V.ι.appTop := by
  rw [Scheme.Opens.topIso_inv, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))

lemma topIso_inv_res {X : Scheme.{0}} (V : X.Opens) (c : Γ(X, ⊤)) :
    V.topIso.inv (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op c) = V.ι.appTop c :=
  ConcreteCategory.congr_hom (topIso_inv_res_hom V) c

lemma appIso_hom_res {Z : Scheme.{0}} (O : Z.Opens) (W : (O : Scheme.{0}).Opens) (d : Γ(Z, ⊤)) :
    (O.ι.appIso W).hom (Z.presheaf.map (homOfLE le_top : O.ι ''ᵁ W ⟶ ⊤).op d) =
      (O : Scheme.{0}).presheaf.map (homOfLE le_top : W ⟶ ⊤).op (O.ι.appTop d) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE]
  rfl

lemma morphismRestrict_appTop_ι {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (c : Γ(X, ⊤)) :
    (φ ∣_ V).appTop (V.ι.appTop c) = (φ ⁻¹ᵁ V).ι.appTop (φ.appTop c) := by
  have h := congrArg Scheme.Hom.appTop (morphismRestrict_ι φ V)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h c

lemma overBase_appTop {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) =
      (φ ∣_ V).appTop (V.topIso.inv b) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
    CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]

theorem toFunctions_preimage : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  intro A _ _ X Z _ _ φ hφ V hV _ W a
  have hZ : (Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      φ.appTop ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    rw [← hφ, Scheme.Hom.comp_appTop]
    rfl
  change ((φ ⁻¹ᵁ V).ι.appIso W).hom (Z.presheaf.map (homOfLE le_top).op
      ((Z ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) =
    (φ ⁻¹ᵁ V).toScheme.presheaf.map (homOfLE le_top).op
      ((φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv
        (X.presheaf.map (homOfLE le_top).op
          ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv a)))))
  rw [overBase_appTop, topIso_inv_res, morphismRestrict_appTop_ι, hZ, appIso_hom_res]

end GlobalTheory.CompanionTheory.GE.RingCompat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_restriction_functions_compatible : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage | exact GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage | (intros; apply GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShift
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

theorem algebraMap_overPre {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

theorem zeroth_cohomology_ideal_transfer : ∀ {X Z : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (G : Z.Modules), letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (J : Ideal Γ(X, V)) (x : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0), x ∈ (J • ⊤ : Submodule Γ(X, V) (Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x : Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))) ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  intro X Z φ V hV G
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro J x hx
  let L : Sheaf.H.{0} (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj G, V) :=
    { toFun := fun x => G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
        (Sheaf.H.equiv₀ (modulesAb (G.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
          Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
      map_add' := fun x y => by
        rw [map_add (f := _)]
        exact map_add _ _ _
      map_smul' := fun b x => by
        rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
        refine (RelSerre.smul_restrict_top G (φ ⁻¹ᵁ V) _ _).trans ?_
        refine (congrArg (· • _) (algebraMap_overPre φ V hV b)).trans ?_
        exact (smul_pushforward φ G b _).symm }
  change L x ∈ _
  refine Submodule.smul_induction_on hx (p := fun x => L x ∈ (J • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V))) (fun b hb y _ => ?_) (fun y y' hy hy' => ?_)
  · show L (b • y) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · show L (y + y') ∈ _
    rw [map_add (f := _)]
    exact add_mem hy hy'

theorem mem_formalK_of_factor {B : Type} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {Y : Scheme.{0}} [Y.Over (Spec (.of B))] {P F : Y.Modules} (f : P ⟶ F) (k : ℕ)
    (g : P ⟶ idealPow J F (k + 1)) (hg : g ≫ idealPowι J F (k + 1) = f) (p : Γ(P, ⊤)) :
    (Sheaf.H.equiv₀ (modulesAb F) isTerminalTop).symm (f.app ⊤ p) ∈ formalK J F 0 k := by
  refine ⟨(Sheaf.H.equiv₀ (modulesAb (idealPow J F (k + 1))) isTerminalTop).symm (g.app ⊤ p), ?_⟩
  refine (Sheaf.H.equiv₀_symm_naturality (hT := isTerminalTop)
    (modulesAbMap (idealPowι J F (k + 1))) (g.app ⊤ p)).trans ?_
  congr 1
  rw [← hg]
  rfl

theorem formal_shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {G : Z.Modules}, IsCoherent G → ∀ (V : X.Opens), IsAffineOpen V → ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(G, φ ⁻¹ᵁ V)), s ∈ Set.range ((idealPowι I G (n + c)).app (φ ⁻¹ᵁ V)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from s) ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  intro A _ _ I X Z _ _ _ φ hprop hφ G hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  haveI := hG.1
  have hF : IsCoherent (G.restrict (φ ⁻¹ᵁ V).ι) := hG.restrict _
  obtain ⟨c₀, hc₀⟩ := exists_formalK_le (Ideal.map (toFunctions (A := A) V) I) hF 0
  refine ⟨c₀ + 1, fun n s hs => ?_⟩
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨g, hg⟩ := GlobalTheory.T.affine_restriction_functions_naturality I φ V hV (GlobalTheory.T.open_restriction_functions_compatible φ hφ V hV) G (n + c₀ + 1)
  let p : Γ((idealPow I G (n + c₀ + 1)).restrict (φ ⁻¹ᵁ V).ι, ⊤) :=
    (idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t
  have hx := mem_formalK_of_factor _ _ (n + c₀) g hg p
  have hx2 := hc₀ n hx
  have hx3 := zeroth_cohomology_ideal_transfer φ V hV G _ _ hx2
  rw [← Ideal.map_pow] at hx3
  convert hx3 using 1
  dsimp only
  erw [AddEquiv.apply_symm_apply]
  have nat := NatTrans.naturality_apply (idealPowι I G (n + c₀ + 1)).mapPresheaf
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t
  change _ = G.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
    ((idealPowι I G (n + c₀ + 1)).mapPresheaf.app (op ((φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
      ((idealPow I G (n + c₀ + 1)).presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V))).op t))
  rw [nat]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [eqToHom_op, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory.CompanionTheory.GE.FormalShift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardIdealPowerShiftStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_ideal_power_shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {G : Z.Modules}, IsCoherent G → ∀ (V : X.Opens), IsAffineOpen V → ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(G, φ ⁻¹ᵁ V)), s ∈ Set.range ((idealPowι I G (n + c)).app (φ ⁻¹ᵁ V)) → (show Γ((Scheme.Modules.pushforward φ).obj G, V) from s) ∈ (Ideal.map (toFunctions (A := A) V) (I ^ n) • ⊤ : Submodule Γ(X, V) Γ((Scheme.Modules.pushforward φ).obj G, V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift | exact GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift | (intros; apply GlobalTheory.CompanionTheory.GE.FormalShift.formal_shift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPower
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPower
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PowImage

lemma idealSumMap_comp_natural {A : Type} [CommRing A] [IsNoetherianRing A] {Z : Scheme.{0}}
    [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (J : Ideal A) :
    idealSumMap F J ≫ g = biproduct.map (fun _ => g) ≫ idealSumMap G J := by
  apply biproduct.hom_ext'
  intro k
  simp only [idealSumMap, biproduct.ι_desc_assoc, biproduct.ι_map_assoc, GroundTheory.Arith.SchemeCoh.smulHom_comp,
    biproduct.ι_desc]

lemma idealPowι_comp_cokernel {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Z : Scheme.{0}} [Z.Over (Spec (.of A))] {F G : Z.Modules} (g : F ⟶ G) (m : ℕ) :
    idealPowι I F m ≫ g ≫ cokernel.π (idealSumMap G (I ^ m)) = 0 := by
  apply (cancel_epi (Abelian.factorThruImage (idealSumMap F (I ^ m)))).1
  have hfac : Abelian.factorThruImage (idealSumMap F (I ^ m)) ≫
      kernel.ι (cokernel.π (idealSumMap F (I ^ m))) = idealSumMap F (I ^ m) :=
    Abelian.image.fac _
  rw [comp_zero, ← Category.assoc, hfac, ← Category.assoc, idealSumMap_comp_natural,
    Category.assoc, cokernel.condition, comp_zero]

theorem adjMap_app_mem_range_idealPowι {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ)
    (hB : B ⊔ powSub I _ (n + 1) = pullSys I φ E S n) (V : X.Opens) (x : Γ(E, V))
    (hx : x ∈ secs (S n) V) :
    (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈
      Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  obtain ⟨y, rfl⟩ := hx
  let f := cokernel.π B.arrow ≫ cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1)))
  have hle : pullSys I φ E S n ≤ kernelSubobject f := by
    rw [← hB]
    refine sup_le ?_ ?_
    · apply le_kernelSubobject
      rw [← Category.assoc, cokernel.condition, zero_comp]
    · apply le_kernelSubobject
      rw [powSub, ← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc,
        idealPowι_comp_cokernel, comp_zero]
  have hS : (Scheme.Modules.pullback φ).map (S n).arrow ≫ f = 0 := by
    have h1 := le_sup_left.trans hle
    rw [← imageSubobject_arrow_comp ((Scheme.Modules.pullback φ).map (S n).arrow), Category.assoc,
      ← Subobject.ofLE_arrow h1, Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]
  let k := kernel.lift (cokernel.π (idealSumMap (cokernel B.arrow) (I ^ (n + 1))))
    ((Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow)
    (by rw [Category.assoc]; exact hS)
  have hk : k ≫ idealPowι I (cokernel B.arrow) (n + 1) =
      (Scheme.Modules.pullback φ).map (S n).arrow ≫ cokernel.π B.arrow := kernel.lift_ι _ _ _
  have hadj : (S n).arrow ≫ adjMap φ B =
      (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _ ≫
        (Scheme.Modules.pushforward φ).map (k ≫ idealPowι I (cokernel B.arrow) (n + 1)) := by
    rw [adjMap, Adjunction.homEquiv_unit, hk, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.naturality (S n).arrow
  refine ⟨((Scheme.Modules.pushforward φ).map k).app V
    (((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app _).app V y), ?_⟩
  have h2 := congrArg (fun g => g.app V y) hadj
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.map_comp] at h2
  rw [h2]
  rfl

end GlobalTheory.CompanionTheory.GE.PowImage
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPowerStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_section_ideal_power : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E) (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ), B ⊔ powSub I _ (n + 1) = pullSys I φ E S n → ∀ (V : X.Opens), ∀ x ∈ secs (S n) V, (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈ Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | exact GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | (intros; apply GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherent
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Shift

theorem exists_lift_pow_smul {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : N →ₗ[R] M) :
    ∃ k : ℕ, ∀ (n : ℕ) (y : N), f y ∈ J ^ (n + k) • (⊤ : Submodule R M) →
      ∃ i ∈ J ^ n • (⊤ : Submodule R N), f i = f y := by
  obtain ⟨k, hk⟩ := J.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k, fun n y hy => ?_⟩
  have h1 : f y ∈ J ^ (n + k) • (⊤ : Submodule R M) ⊓ LinearMap.range f := ⟨hy, y, rfl⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : J ^ n • (J ^ k • (⊤ : Submodule R M) ⊓ LinearMap.range f) ≤
      (J ^ n • (⊤ : Submodule R N)).map f := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨i, hi, hfi⟩ := h2 h1
  exact ⟨i, hi, hfi⟩

theorem mem_secs_adjKer {X Z : Scheme.{0}} (φ : Z ⟶ X) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (V : X.Opens) (x : Γ(E, V))
    (hx : (adjMap φ B).app V x = 0) : x ∈ secs (adjKer φ B) V := by
  obtain ⟨k, hk⟩ := kernel_ι_app_exact (adjMap φ B) V x hx
  refine ⟨(kernelSubobjectIso (adjMap φ B)).inv.app V k, ?_⟩
  rw [← hk, ← kernelSubobject_arrow' (adjMap φ B)]
  rfl

theorem local_shift {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (hE : IsCoherent E) (S : ℕ → Subobject E)
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : (B : Z.Modules).IsQuasicoherent)
    (hBS : ∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e)
    (hK : (adjKer φ B : X.Modules).IsQuasicoherent)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∃ c : ℕ, ∀ e, secs (S (e + c)) V ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) V := by
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.pushforward_ideal_power_shift I φ hφ hc hG V hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI := hP.2 V hV
  let f : Γ(E, V) →ₗ[Γ(X, V)] Γ((Scheme.Modules.pushforward φ).obj (cokernel B.arrow), V) :=
    { toFun := (adjMap φ B).app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  have hJ : ∀ m, Ideal.map (toFunctions (A := A) V) (I ^ m) = J ^ m := fun m => Ideal.map_pow _ _ _
  obtain ⟨c₂, hc₂⟩ := exists_lift_pow_smul J f
  refine ⟨c₂ + c₁, fun e x hx => ?_⟩
  have h1 := GlobalTheory.T.cokernel_section_ideal_power I φ S B (e + (c₂ + c₁)) (hBS _) V x hx
  rw [show e + (c₂ + c₁) + 1 = (e + 1 + c₂) + c₁ by omega] at h1
  have h2 := hc₁ (e + 1 + c₂) _ h1
  rw [hJ] at h2
  obtain ⟨i, hi, hfi⟩ := hc₂ (e + 1) x h2
  have hker : x - i ∈ secs (adjKer φ B) V :=
    mem_secs_adjKer φ B V _ (by
      change f (x - i) = 0
      rw [map_sub, hfi, sub_self])
  have hpow : i ∈ secs (powSub I E (e + 1)) V := by
    rw [GlobalTheory.T.ideal_power_subobject_sections I E hE.1 (e + 1) V hV, hJ]
    exact hi
  have hsup := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).2 V hV
  rw [hsup]
  exact ⟨x - i, hker, i, hpow, by abel⟩

theorem shift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (B : Z.Modules).IsQuasicoherent → (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∃ c : ℕ, ∀ e, S (e + c) ≤ adjKer φ B ⊔ powSub I E (e + 1) := by
  intro A _ _ I X Z _ _ _ _ φ hφ hc E hE S hS B hB hBS
  haveI := hE.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow (isCoherent_pullback φ hE)
  have hP := GlobalTheory.T.proper_pushforward_coherent φ hφ hG
  haveI := hP.1
  have hK : (adjKer φ B : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap φ B)).symm (isQuasicoherent_kernel _)
  have hloc : ∀ V : X.affineOpens, ∃ c : ℕ,
      ∀ e, secs (S (e + c)) (V : X.Opens) ⊆ secs (adjKer φ B ⊔ powSub I E (e + 1)) (V : X.Opens) :=
    fun V => local_shift I φ hφ hc hE S B hB hBS hK V V.2
  choose c hc' using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hx, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩)
  have anti : Antitone S :=
    antitone_nat_of_succ_le fun n => le_of_le_of_eq le_sup_left (hS.succ n).symm
  refine ⟨t.sup c, fun e => ?_⟩
  have hsupq := (GlobalTheory.T.quasicoherent_sup_sections hE.1 (adjKer φ B) (powSub I E (e + 1)) hK
    ((closedSys_pow I E).qcoh e)).1
  refine GlobalTheory.T.subobject_le_of_affine_cover (S (e + t.sup c)) _ (hS.qcoh _) hsupq (fun i : t => (i.1.1 : X.Opens))
    (fun i => i.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hxU⟩
  · intro i
    refine subset_trans ?_ (hc' i.1 e)
    exact (GlobalTheory.T.subobject_le_iff_affine_sections _ _).1 (anti (Nat.add_le_add_left (Finset.le_sup i.2) e)) i.1

end GlobalTheory.CompanionTheory.GE.Shift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPullbackSystemQuasicoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pullback_system_quasicoherent : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (B : Z.Modules).IsQuasicoherent → (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∃ c : ℕ, ∀ e, S (e + c) ≤ adjKer φ B ⊔ powSub I E (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Shift.shift | exact GlobalTheory.CompanionTheory.GE.Shift.shift | (intros; apply GlobalTheory.CompanionTheory.GE.Shift.shift <;> assumption)
end
