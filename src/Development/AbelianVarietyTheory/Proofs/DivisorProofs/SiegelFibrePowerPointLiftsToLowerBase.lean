module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.MumAmple

theorem relAmple_of_lam_iso_univ : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  intro o _ ζ g n F R' _ _ T B _ _ β β₂ hpb hsq L hL hiso
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) hpb.1 F.univ.ab.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) hpb.1 F.univ.ab.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 F.univ.ab.geomConnected }
  have := hB.proper
  have := hB.smooth
  refine ProperFinite.relAmple_of_geometricFibres B hL fun K _ _ y => ?_
  have hk := isGrpPullback_pullback B y
  have hkU := hk.comp hpb
  obtain ⟨⟨c, hc⟩, hprin⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s ((y ≫ T) ≫ F.s) (y ≫ T) F.univ rfl
  have hcp := hprin c hc F.princ
  obtain ⟨φc, φc₂, hcpb, hcsq, hcP, -⟩ := hc
  obtain ⟨L₀, h₀, hlam₀, ha₀⟩ := PolBundleLoc.exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  have hk₀ := KTrivOfLam.kTriv_of_lam_iso _ c.A c.ab c.P c.isLB hcp.2 L₀ h₀ hlam₀
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hcpb hkU
  haveI := he
  let ψ : c.A.left ⟶ B.left := e.hom.left ≫ pullback.fst B.hom y
  have hψ : IsGrpPullback c.A B y ψ := by
    have := (isGrpPullback_of_iso e).comp hk
    rwa [Category.id_comp] at this
  obtain ⟨ψ₂, sψ⟩ := SiegPull.exists_isSquare hψ.1.w
  have hN : (L.pull ψ).IsLB := pull_isLB hL ψ
  have hlamN : LBIso (abelian₂ c.A (L.pull ψ)) ((abelian₂ B L).pull ψ₂) :=
    SiegPull.lbIso_lam_pull hψ ((CechPic.cls_eq_iff hN hN).1 rfl) sψ
  have hsq' : IsSquare (ψ ≫ β) (ψ₂ ≫ β₂) := SiegPull.isSquare_comp sψ hsq
  have hφ : ψ ≫ β = φc := by simpa [ψ, Category.assoc] using heφ
  have e₂ : ψ₂ ≫ β₂ = φc₂ := SiegPull.isSquare_unique hsq' hcsq hφ
  have hpullP : LBIso ((abelian₂ B L).pull ψ₂) (F.univ.P.pull (ψ₂ ≫ β₂)) := SiegPull.lbIso_pull_comp hiso ψ₂
  rw [e₂] at hpullP
  have iLN : (abelian₂ c.A (L.pull ψ)).IsLB := LB.isLB_linComb hN _ _
  have iL0 : (abelian₂ c.A L₀).IsLB := LB.isLB_linComb h₀ _ _
  have iLB : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam : CechPic.lam (CechPic.cls (L.pull ψ) hN) (fst c.A c.A) (snd c.A c.A) =
      CechPic.lam (CechPic.cls L₀ h₀) (fst c.A c.A) (snd c.A c.A) :=
    (CechPic.cls_cube_two hN _ _ iLN).symm.trans
      (((CechPic.cls_eq_iff iLN (pull_isLB iLB _)).2 hlamN).trans
        (((CechPic.cls_eq_iff (pull_isLB iLB _) (pull_isLB F.univ.isLB _)).2 hpullP).trans
          (((CechPic.cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 hcP).symm.trans
            (((CechPic.cls_eq_iff iL0 c.isLB).2 hlam₀).symm.trans (CechPic.cls_cube_two h₀ _ _ iL0)))))
  obtain ⟨hampN, -⟩ := AmpleKerFibre.relAmple_kTriv_of_lam_eq K c.A c.ab L₀ h₀ ha₀ hk₀ (L.pull ψ) hN hlam
  have : IsProper c.A.hom := c.ab.proper
  have hAN := (relAmple_iff_isAmpleLB_of_isAffine c.A hN).1 hampN
  haveI : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have h1 := hAN.pull_of_isAffineHom e.inv.left
  have h2 : LBIso ((L.pull ψ).pull e.inv.left) (L.pull (pullback.fst B.hom y)) := by
    have h3 := SiegPull.lbIso_pull_comp ((CechPic.cls_eq_iff hN hN).1 rfl) e.inv.left
    have ee : e.inv.left ≫ ψ = pullback.fst B.hom y := by
      simp only [ψ]
      rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
    rwa [ee] at h3
  exact (isAmpleLB_congr (pull_isLB hN _) (pull_isLB hL _) h2).1 h1

end GlobalTheory.MumAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R' : Type) [CommRing R'] [IsNoetherianRing R'] (T : Sp R' ⟶ F.X) (B : Over (Sp R')) [GrpObj B] [IsCommMonObj B] (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A T β → IsSquare β β₂ → ∀ L : LB B.left, L.IsLB → LBIso (abelian₂ B L) (F.univ.P.pull β₂) → RelAmple B L := by
  first | exact @GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | exact GlobalTheory.MumAmple.relAmple_of_lam_iso_univ | (intros; apply GlobalTheory.MumAmple.relAmple_of_lam_iso_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnramifiedExtensionGroupLift
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem root_congr {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} {t t' : T ⟶ S} (e : t = t')
    (h : Root A P t) : Root A P t' := e ▸ h

theorem residue_lift (R R' k'' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Field k''] [Algebra (ResidueField R) k'']
    (ε : ResidueField R ⊗[R] R' ≃ₐ[ResidueField R] k'') :
    ∃ φ : k'' →+* ResidueField R', φ.comp (algebraMap (ResidueField R) k'') =
      algebraMap (ResidueField R) (ResidueField R') := by
  let g₂ : ResidueField R ⊗[R] R' →ₐ[ResidueField R] ResidueField R' :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  refine ⟨(g₂.comp ε.symm.toAlgHom).toRingHom, ?_⟩
  ext a
  exact (g₂.comp ε.symm.toAlgHom).commutes a

end GlobalTheory.PolBundleLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtale
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.PolBundleLocEt

open GlobalTheory.PolRoot GlobalTheory.PolBundleLoc

theorem exists_rigLB_sFam_etale :
    ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ y : Sp R ⟶ F.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R'), IsAdicComplete (maximalIdeal R') R' ∧ IsLocalHom ρ ∧ Function.Injective ρ ∧ ρ.Finite ∧ ρ.Etale ∧ ∃ (B : Over (Sp R')) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A (spMap ρ ≫ y) β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro o _ ζ g n F R _ _ _ hR y
  haveI : IsAdicComplete (maximalIdeal R) R := hR
  haveI : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have hAb := F.univ.ab
  have hP := F.univ.isLB
  let k := ResidueField R
  let t₀ : Sp k ⟶ F.X := spMap (residue R) ≫ y

  have h₁ : Root F.univ.A F.univ.P (spMap (algebraMap k (AlgebraicClosure k)) ≫ t₀) :=
    root_geom F (AlgebraicClosure k) _

  obtain ⟨B, hB, h₂⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ (AlgebraicClosure k) h₁
  haveI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : Algebra.IsIntegral k B := ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (Algebra.IsIntegral.isIntegral (R := k) (b : AlgebraicClosure k))⟩
  haveI : Module.Finite k B := Algebra.IsIntegral.finite

  obtain ⟨C, _, _, _, _, hC, ⟨ιC⟩, hdom⟩ := GlobalTheory.T.exists_complete_local_geomDomain' k B inferInstance
  let tC : Sp C ⟶ F.X := spMap (algebraMap k C) ≫ t₀
  have h₃ : Root F.univ.A F.univ.P (spMap (residue C) ≫ tC) := by
    refine root_congr ?_ (h₂.comp hAb (spMap ιC.toRingHom))
    simp only [tC, ← Category.assoc, spMap_comp']
    congr 2
    exact ιC.comp_algebraMap.trans (IsScalarTower.algebraMap_eq k C (ResidueField C))
  have h₄ : Root F.univ.A F.univ.P tC :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 C hC tC h₃

  obtain ⟨B', hB', h₅⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ C h₄
  have hdom' : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B') := by
    intro K _ _ h1 h2
    haveI := hdom K h1 h2
    let m : K ⊗[k] B' →ₐ[K] K ⊗[k] C := Algebra.TensorProduct.map (AlgHom.id K K) B'.val
    have hm : Function.Injective m := by
      have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (B'.val.toLinearMap)
        Subtype.val_injective
      exact this
    exact hm.isDomain m
  obtain ⟨k'', _, _, hfin, hsep, ⟨ψ⟩⟩ := GlobalTheory.T.exists_separable_point_of_geometrically_domain k B' ((Subalgebra.fg_iff_finiteType B').1 hB') hdom'
  have h₆ : Root F.univ.A F.univ.P (spMap (algebraMap k k'') ≫ t₀) := by
    refine root_congr ?_ (h₅.comp hAb (spMap ψ.toRingHom))
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact ψ.comp_algebraMap

  haveI : Module.Finite (ResidueField R) k'' := hfin
  haveI : Algebra.IsSeparable (ResidueField R) k'' := hsep
  obtain ⟨R', _, _, hfinR, het, _, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R k''
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_tfae (algebraMap R R')).out 1 5).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := Algebra.FormallyUnramified.map_maximalIdeal
  have hcR' : IsAdicComplete (maximalIdeal R') R' := by
    have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this
  haveI : IsNoetherianRing R' := isNoetherian_of_tower R inferInstance
  let ρ : R →+* R' := algebraMap R R'
  obtain ⟨φ, hφ⟩ := residue_lift R R' k'' ε
  let T : Sp R' ⟶ F.X := spMap ρ ≫ y
  have h₇ : Root F.univ.A F.univ.P (spMap (residue R') ≫ T) := by
    refine root_congr ?_ (h₆.comp hAb (spMap φ))
    simp only [T, t₀, ← Category.assoc, spMap_comp']
    congr 2
    rw [← RingHom.comp_assoc, hφ]
    exact (ResidueField.map_comp_residue ρ).symm
  obtain ⟨B₁, _, _, β, β₂, hβ, hsq, L, hL, hΛ⟩ :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 R' hcR' T h₇
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hβ
  have hP' : (F.univ.P.pull β₂).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb hP _ _
  have hker := GlobalTheory.SiegelPull.nondeg_pull hβ hsq hP hP' ((GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl) F.princ.2
  obtain ⟨M, hM, ⟨hcub⟩⟩ := exists_rigLB_cubical R' B₁ hB₁ L hL
  have hK := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ B₁ hB₁ (F.univ.P.pull β₂) hP' hker L hL hΛ
  have hA := GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal F R' T B₁ β β₂ hβ hsq L hL hΛ
  subst hM
  have hinj : Function.Injective ρ := by
    letI : Algebra.Etale R R' := het
    haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective R R'
  exact ⟨R', inferInstance, inferInstance, ρ, hcR', inferInstance, hinj, RingHom.finite_algebraMap.mpr hfinR,
    RingHom.etale_algebraMap.mpr het, B₁, inferInstance, inferInstance, β, β₂, M, hcub,
    hβ, hsq, hA, hK, hΛ⟩

end GlobalTheory.PolBundleLocEt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidified_cubical_root_polarisation_etale : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ y : Sp R ⟶ F.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R'), IsAdicComplete (maximalIdeal R') R' ∧ IsLocalHom ρ ∧ Function.Injective ρ ∧ ρ.Finite ∧ ρ.Etale ∧ ∃ (B : Over (Sp R')) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A (spMap ρ ≫ y) β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  first | exact @GlobalTheory.PolBundleLocEt.exists_rigLB_sFam_etale | exact GlobalTheory.PolBundleLocEt.exists_rigLB_sFam_etale | (intros; apply GlobalTheory.PolBundleLocEt.exists_rigLB_sFam_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.HenselLift

theorem exists_dvr_of_finite_etale : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  intro A R V _ _ _ _ _ _ _ ρ ψ hρl hρf hρe hV hdvr hψ
  letI := ρ.toAlgebra
  letI := ψ.toAlgebra
  obtain ⟨hnoeth, hic, hcpl, hchar⟩ := hV
  haveI : Algebra.Etale A R := hρe
  haveI : Module.Finite A R := hρf
  haveI : IsLocalHom (algebraMap A R) := hρl
  haveI : IsLocalHom (algebraMap A V) := hψ
  haveI : Algebra.Etale V (V ⊗[A] R) := Algebra.Etale.baseChange A R V
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Nontrivial (V ⊗[A] R) := Module.FaithfullyFlat.rTensor_nontrivial A R V
  obtain ⟨q, hq⟩ := Ideal.exists_maximal (V ⊗[A] R)
  haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_isAdicComplete V
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian V q
  haveI := GlobalTheory.isLocalRing_quotient_one_sub he q H
  haveI : IsLocalization.Away e (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  haveI : Algebra.Etale (V ⊗[A] R) (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  haveI : Algebra.Etale V (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.comp V (V ⊗[A] R) _
  haveI : Module.Finite V (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Module.Finite.trans (V ⊗[A] R) _
  have hfl : IsLocalHom (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) := by
    refine ((local_hom_tfae _).out 1 5).2 ?_
    have := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V)
      (maximalIdeal (V ⊗[A] R ⧸ Ideal.span {1 - e}))
    exact IsLocalRing.eq_maximalIdeal this
  haveI := hfl
  obtain ⟨hdom, hdvr', -, hff, -⟩ :=
    GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom V (V ⊗[A] R ⧸ Ideal.span {1 - e})
  have hinj : Function.Injective (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) :=
    FaithfulSMul.algebraMap_injective _ _
  haveI : IsNoetherianRing V := hnoeth
  haveI : IsAdicComplete (maximalIdeal V) V := hcpl
  haveI : CharZero V := hchar
  obtain ⟨-, hcpl'⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V
    (V ⊗[A] R ⧸ Ideal.span {1 - e}) inferInstance hinj
  have hcomm : ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
      (Algebra.TensorProduct.includeRight.toRingHom)).comp ρ =
      (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})).comp ψ := by
    ext a
    show Ideal.Quotient.mk _ ((1 : V) ⊗ₜ[A] ρ a) = Ideal.Quotient.mk _ (ψ a ⊗ₜ[A] (1 : R))
    rw [show ρ a = a • (1 : R) from Algebra.algebraMap_eq_smul_one a,
      show ψ a = a • (1 : V) from Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  refine ⟨V ⊗[A] R ⧸ Ideal.span {1 - e}, inferInstance, hdom, inferInstance,
    algebraMap V _, (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight.toRingHom),
    ⟨?_, inferInstance, hcpl', charZero_of_injective_algebraMap hinj⟩, hdvr', hinj,
    RingHom.finite_algebraMap.2 inferInstance, inferInstance, ?_, ?_⟩
  · exact isNoetherian_of_tower V inferInstance
  · refine ((local_hom_tfae _).out 1 5).2 ?_
    have hA : Ideal.comap (algebraMap A R) (Ideal.comap ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
        (Algebra.TensorProduct.includeRight.toRingHom)) (maximalIdeal _)) = maximalIdeal A := by
      have h1 : Ideal.comap (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) (maximalIdeal _) =
          maximalIdeal V := ((local_hom_tfae _).out 1 5).1 hfl
      have h2 : Ideal.comap ψ (maximalIdeal V) = maximalIdeal A := ((local_hom_tfae _).out 1 5).1 hψ
      change Ideal.comap ρ _ = _
      rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap, h1, h2]
    have hA' : (Ideal.comap (algebraMap A R) (Ideal.comap ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
        (Algebra.TensorProduct.includeRight.toRingHom)) (maximalIdeal _))).IsMaximal := by
      rw [hA]; exact maximalIdeal.isMaximal A
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) _ hA'
    exact IsLocalRing.eq_maximalIdeal hm
  · exact hcomm

end GlobalTheory.HenselLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  first | exact @GlobalTheory.HenselLift.exists_dvr_of_finite_etale | exact GlobalTheory.HenselLift.exists_dvr_of_finite_etale | (intros; apply GlobalTheory.HenselLift.exists_dvr_of_finite_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfFiniteOfFormallyUnramified
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.InteriorChart

theorem bijective_stalkSpecializes {X : Scheme.{0}} {x y : X} (e : x = y) (h : x ⤳ y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isEtaleCompletion_comp {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C]
    [IsLocalRing C] (φ : A →+* B) (ρ : B →+* C) [IsLocalHom ρ] (hφ : IsEtaleCompletion φ) (hf : ρ.Flat)
    (hm : (maximalIdeal B).map ρ = maximalIdeal C) (hfin : ρ.Finite) : IsEtaleCompletion (ρ.comp φ) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨RingHom.Flat.comp h1 hf, ?_, ?_⟩
  · rw [← Ideal.map_map, h2, hm]
  · have e : (residue C).comp (ρ.comp φ) = (ResidueField.map ρ).comp ((residue B).comp φ) := by
      rw [← RingHom.comp_assoc, ← ResidueField.map_comp_residue, RingHom.comp_assoc]
    rw [e]
    have hm' : (ResidueField.map ρ).Finite := by
      have h := RingHom.Finite.comp (RingHom.Finite.of_surjective (residue C) residue_surjective) hfin
      rw [← ResidueField.map_comp_residue] at h
      exact RingHom.Finite.of_comp_finite h
    exact RingHom.Finite.comp hm' h3

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨?_, ?_⟩
  · rw [hψ]
    exact isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

end GlobalTheory.InteriorChart

namespace GlobalTheory.InteriorChart

end GlobalTheory.InteriorChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowLift

theorem etCompl : ∀ {o : Type} [CommRing o] [IsNoetherianRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {r : ℕ} (y : (GlobalTheory.LowChart.powA F r).left) (R' : Type) [CommRing R'] [IsLocalRing R'] (ρ : GlobalTheory.LowChart.W F y →+* R'), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsEtaleCompletion (Scheme.stalkClosedPointTo (spMap ρ ≫ GlobalTheory.LowChart.toPow F y)).hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo (spMap ρ ≫ GlobalTheory.LowChart.toPow F y)).hom).FormallyUnramified := by
  intro o _ _ ζ h n F r y R' _ _ ρ hloc hfin het
  let y₀ : Sp (GlobalTheory.LowChart.W F y) ⟶ (GlobalTheory.LowChart.powA F r).left := GlobalTheory.LowChart.toPow F y
  obtain ⟨hEt₀, hres₀⟩ := GlobalTheory.InteriorChart.completedStalk_chart (GlobalTheory.LowChart.powA F r).left y
  change IsEtaleCompletion (Scheme.stalkClosedPointTo y₀).hom at hEt₀
  change Function.Surjective ((residue (GlobalTheory.LowChart.W F y)).comp (Scheme.stalkClosedPointTo y₀).hom) at hres₀
  have hfu : ρ.FormallyUnramified ∧ ρ.Flat := by
    algebraize [ρ]
    exact ⟨inferInstanceAs (Algebra.FormallyUnramified _ R'), inferInstanceAs (Module.Flat _ R')⟩
  have hm' : (maximalIdeal (GlobalTheory.LowChart.W F y)).map ρ = maximalIdeal R' := by
    algebraize [ρ]
    haveI : IsLocalHom (algebraMap (GlobalTheory.LowChart.W F y) R') := hloc
    exact Algebra.FormallyUnramified.map_maximalIdeal
  let ξ₀ : Sp R' ⟶ (GlobalTheory.LowChart.powA F r).left := spMap ρ ≫ y₀
  have hcp : ξ₀ (closedPoint R') = y₀ (closedPoint (GlobalTheory.LowChart.W F y)) := by
    show y₀ (spMap ρ (closedPoint R')) = _
    rw [show spMap ρ (closedPoint R') = closedPoint (GlobalTheory.LowChart.W F y) from IsLocalRing.comap_closedPoint ρ]
  have hs : ξ₀ (closedPoint R') ⤳ y₀ (closedPoint (GlobalTheory.LowChart.W F y)) := specializes_of_eq hcp
  have key := GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes (GlobalTheory.LowChart.powA F r).left y₀ ρ hs
  let E := RingEquiv.ofBijective ((GlobalTheory.LowChart.powA F r).left.presheaf.stalkSpecializes hs).hom
    (GlobalTheory.InteriorChart.bijective_stalkSpecializes hcp hs)
  have hξ : (Scheme.stalkClosedPointTo ξ₀).hom =
      (ρ.comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom := by
    ext b
    obtain ⟨a, rfl⟩ := E.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    exact key a
  refine ⟨?_, ?_⟩
  · show IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₀).hom
    rw [hξ]
    exact isEtaleCompletion_comp_bij _ E.symm.bijective _
      (GlobalTheory.InteriorChart.isEtaleCompletion_comp _ ρ hEt₀ hfu.2 hm' hfin)
  · show ((residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom).FormallyUnramified
    have hmap : (ResidueField.map ρ).FormallyUnramified := by
      apply RingHom.FormallyUnramified.of_comp (f := residue (GlobalTheory.LowChart.W F y))
      rw [ResidueField.map_comp_residue]
      exact RingHom.FormallyUnramified.comp hfu.1 (RingHom.FormallyUnramified.of_surjective residue_surjective)
    have e2 : (residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom = (ResidueField.map ρ).comp
        (((residue (GlobalTheory.LowChart.W F y)).comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom) := by
      rw [hξ, ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← ResidueField.map_comp_residue]
      rfl
    rw [e2]
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective (hres₀.comp E.symm.surjective)) hmap

theorem prodPush : ∀ {S S' T : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}, IsGrpPullback G' G f φ → ∀ {r : ℕ} (p : Fin r → (𝟙_ (Over S') ⟶ G')) (t : T ⟶ S) (q : Fin r → (Over.mk t ⟶ G)) (g : T ⟶ S'), g ≫ f = t → (∀ i, g ≫ (p i).left ≫ φ = (q i).left) → ∀ a : Fin r → ℤ, g ≫ (∏ i, p i ^ a i).left ≫ φ = (∏ i, q i ^ a i).left := by
  intro S S' T G G' _ _ _ _ f φ hG r p t q g ht hq a
  subst ht
  let U : Over.mk g ⟶ 𝟙_ (Over S') := toUnit _
  let Φ : (𝟙_ (Over S') ⟶ G') →* (Over.mk ((Over.mk g).hom ≫ f) ⟶ G) := (pushHom hG (Over.mk g)).comp (preHom U)
  have hΦ : ∀ x, (Φ x).left = g ≫ x.left ≫ φ := fun x => by
    show (U ≫ x).left ≫ φ = _
    rw [Over.comp_left, Category.assoc]
    rfl
  have hpq : ∀ i, Φ (p i) = q i := fun i => Over.OverMorphism.ext ((hΦ _).trans (hq i))
  have e : Φ (∏ i, p i ^ a i) = ∏ i, q i ^ a i := by
    rw [map_prod]
    simp only [map_zpow, hpq]
  exact (hΦ _).symm.trans (congrArg (fun z => z.left) e)

end GlobalTheory.LowLift

namespace GlobalTheory.LowLift

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem main : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (F : SFam h n (zetaAway n)) (r : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsDiscreteValuationRing V₁ → ∀ (b₁ : cycAway n →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap b₁), ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V₁ →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = h ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b₁ ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ (GlobalTheory.LowChart.siegAt F v _ hs).A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' (GlobalTheory.LowChart.siegAt F v _ hs).A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((GlobalTheory.LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn _ h F r V₁ _ _ _ hV hdvr b₁ v hs
  have hV0 := hV
  obtain ⟨-, -, hVc, -⟩ := hV
  haveI := hVc
  let w := v (closedPoint V₁)
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.LowChart.exists_local_hom F w V₁ v rfl
  haveI : IsNoetherianRing (GlobalTheory.LowChart.W F w) := GlobalTheory.LowChart.isNoetherianRing_completedStalkSiegelFibrePower F w
  obtain ⟨R', _, _, ρ, hc', hloc, hinj, hfin, het, B, _, _, β, β₂, M, cub, hpb, hsq, hamp, hk, hiso⟩ :=
    GlobalTheory.T.exists_rigidified_cubical_root_polarisation_etale F (GlobalTheory.LowChart.W F w) (GlobalTheory.LowChart.isAdicComplete_completedStalkSiegelFibrePower F w) (GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.powA F r).hom)

  let pt : Fin r → (𝟙_ (Over (Sp R')) ⟶ B) := fun i => Over.homMk
    (hpb.1.lift (spMap ρ ≫ GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.coord F i).left) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, Over.w (GlobalTheory.LowChart.coord F i)])) (hpb.1.lift_snd _ _ _)
  have hpt : ∀ i, (pt i).left ≫ β = spMap ρ ≫ GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.coord F i).left := fun i =>
    hpb.1.lift_fst _ _ _
  let c : (Fin r → ℤ) → (𝟙_ (Over (Sp R')) ⟶ B) := fun a => ∏ i, pt i ^ a i
  have hc : ∀ a a', c (a + a') = c a * c a' := fun a a' => by
    simp only [c, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  obtain ⟨τ, hτg, hτs, hτa⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c hc
  have hab : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) hpb.1 F.univ.ab.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) hpb.1 F.univ.ab.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 F.univ.ab.geomConnected }
  have hdim : SmoothOfRelativeDimension h B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange h).of_isPullback hpb.1
      (GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (show n ≠ 0 by omega)))

  let T : TautBase (cycAway n) R' :=
    { b := ρ.comp (GlobalTheory.LowChart.base F w)
      B := B
      isAb := hab
      g := h
      smoothDim := hdim
      M := M
      cub := cub
      ample := hamp
      ktriv := hk
      r := r
      c₀ := c
      c₀_add := hc
      τ₀ := τ
      τ₀_gen := hτg
      τ₀_symm := hτs
      τ₀_add := hτa }
  have hcomp : IsNoetherianRing R' := by
    algebraize [ρ]
    exact Algebra.FiniteType.isNoetherianRing (GlobalTheory.LowChart.W F w) R'
  obtain ⟨hEt, hur⟩ := etCompl F w R' ρ hloc hfin het
  have hcart : IsGrpPullback B F.univ.A ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom) β := by
    rw [Category.assoc]; exact hpb
  have hsingle : ∀ i, c (Pi.single i 1) = pt i := fun i => by
    classical
    show ∏ j, pt j ^ (Pi.single i 1 : Fin r → ℤ) j = _
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp),
      Pi.single_eq_same, zpow_one]
  let L : LowBase (zetaAway n) n :=
    { h := h
      F := F
      W := R'
      noeth := hcomp
      complete := hc'
      T := T
      u := spMap ρ ≫ GlobalTheory.LowChart.toPow F w
      u_et := hEt
      u_sep := hur
      u_base := by
        show _ = spMap (ρ.comp (GlobalTheory.LowChart.base F w))
        rw [spMap_comp', GlobalTheory.LowChart.spMap_base, Category.assoc]
      dim := rfl
      β := β
      β₂ := β₂
      cart := hcart
      sq := hsq
      lb := hiso
      coord := fun i => by
        show (c (Pi.single i 1)).left ≫ β = _
        rw [hsingle, hpt, Category.assoc] }

  obtain ⟨V', _, _, _, f, κ, hV', hdvr', hfi, hff, hfl, hκl, hκρ⟩ :=
    GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange (GlobalTheory.LowChart.W F w) R' V₁ ρ ψ hloc hfin het hV0 hdvr hψl
  have hspec : spMap κ ≫ (spMap ρ ≫ GlobalTheory.LowChart.toPow F w) = spMap f ≫ v := by
    rw [← Category.assoc, ← spMap_comp', hκρ, spMap_comp', Category.assoc, hψ]
  have hb : κ.comp T.b = f.comp b₁ := by
    have e : spMap (κ.comp T.b) = spMap (f.comp b₁) := by
      show spMap (κ.comp (ρ.comp (GlobalTheory.LowChart.base F w))) = _
      rw [spMap_comp', spMap_comp', spMap_comp', GlobalTheory.LowChart.spMap_base, ← hs]
      simpa only [Category.assoc] using congrArg (· ≫ GlobalTheory.LowChart.toO F r) hspec
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

  let SA := (GlobalTheory.LowChart.siegAt F v _ hs).A
  have hSA : IsGrpPullback SA F.univ.A (v ≫ (GlobalTheory.LowChart.powA F r).hom)
      (Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A) :=
    Pdiv.PullbackComparison.isGrpPullback _ _
  have hB' : IsGrpPullback ((Over.pullback (spMap f)).obj SA) SA (spMap f) (Pdiv.PullbackComparison.pφ (spMap f) SA) :=
    Pdiv.PullbackComparison.isGrpPullback _ _
  have hcomm : spMap κ ≫ ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom) =
      spMap f ≫ (v ≫ (GlobalTheory.LowChart.powA F r).hom) := by
    rw [← Category.assoc, hspec, Category.assoc]
  obtain ⟨β'', hβ'', hββ⟩ := GlobalTheory.isGrpPullback_paste F.univ.A B SA ((Over.pullback (spMap f)).obj SA) _ _ (spMap f)
    (spMap κ) β _ _ hcart hSA hB' hcomm
  obtain ⟨β₂', hsq'⟩ : ∃ β₂', IsSquare β'' β₂' := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ''.1.w⟩
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f, κ, AddEquiv.refl _, rfl, hV', hdvr', hfi, hff, hfl, hκl, hb,
    (Over.pullback (spMap f)).obj SA, inferInstance, Pdiv.PullbackComparison.pφ (spMap f) SA, β'', Pdiv.PullbackComparison.pφ₂ (spMap f) SA, β₂', hB',
    hβ'', Pdiv.PullbackComparison.isSquare _ _, hsq', ?_, ?_⟩
  · have key : β₂' ≫ β₂ = Pdiv.PullbackComparison.pφ₂ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A :=
      GlobalTheory.LamPull.isSquare_unique (isSquare_comp hsq' hsq)
        (by rw [hββ]; exact isSquare_comp (Pdiv.PullbackComparison.isSquare _ _) (Pdiv.PullbackComparison.isSquare _ _))
    have e1 : LBIso ((abelian₂ B M.L).pull β₂') (F.univ.P.pull (β₂' ≫ β₂)) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hiso β₂' rfl
    have e2 : LBIso (F.univ.P.pull (Pdiv.PullbackComparison.pφ₂ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A))
        ((F.univ.P.pull (Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A)).pull (Pdiv.PullbackComparison.pφ₂ (spMap f) SA)) :=
      GlobalTheory.GenSpread.lbIso_pull_pull F.univ.isLB _ rfl
    rw [key] at e1
    exact LBIso.trans (pull_isLB (pull_isLB F.univ.isLB _) _) (pull_isLB F.univ.isLB _)
      (pull_isLB (DVR.linComb_isLB M.L M.isLB _ _) _) (LBIso.symm e2) (LBIso.symm e1)
  · intro a
    let q : Fin r → (Over.mk (spMap κ ≫ ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom)) ⟶ F.univ.A) :=
      fun i => Over.homMk (spMap f ≫ v ≫ (GlobalTheory.LowChart.coord F i).left) (by
        show _ = spMap κ ≫ _
        rw [hcomm, Category.assoc, Category.assoc, Over.w (GlobalTheory.LowChart.coord F i)])
    have cA : (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ SA.hom = 𝟙 _ := Over.w _
    have h0 : (spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left) ≫ SA.hom = 𝟙 _ ≫ spMap f := by
      rw [Category.assoc, cA]
      simp
    obtain ⟨x, lf, ls⟩ : ∃ x : Sp V' ⟶ ((Over.pullback (spMap f)).obj SA).left,
        x ≫ Pdiv.PullbackComparison.pφ (spMap f) SA = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ∧
          x ≫ ((Over.pullback (spMap f)).obj SA).hom = 𝟙 _ :=
      ⟨hB'.1.lift _ _ h0, hB'.1.lift_fst _ _ _, hB'.1.lift_snd _ _ _⟩
    refine ⟨x, ls, lf, ?_⟩
    have e1 := prodPush hSA (GlobalTheory.LowChart.ptAt F v _ hs) _ q (spMap f) hcomm.symm
      (fun i => by rw [GlobalTheory.LowChart.ptAt_left]; rfl) ((n : ℤ) • a)
    have e2 := prodPush hcart pt _ q (spMap κ) rfl (fun i => by
      rw [hpt]
      show _ = spMap f ≫ v ≫ _
      simpa only [Category.assoc] using congrArg (· ≫ (GlobalTheory.LowChart.coord F i).left) hspec) ((n : ℤ) • a)
    apply hcart.1.hom_ext
    · calc (x ≫ β'') ≫ β = x ≫ Pdiv.PullbackComparison.pφ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A := by
            rw [Category.assoc, hββ]
        _ = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫
            Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A :=
          (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A) lf).trans
            (Category.assoc _ _ _))
        _ = (∏ i, q i ^ ((n : ℤ) • a) i).left := e1
        _ = (spMap κ ≫ (c ((n : ℤ) • a)).left) ≫ β := e2.symm.trans (Category.assoc _ _ _).symm
    · calc (x ≫ β'') ≫ B.hom = x ≫ ((Over.pullback (spMap f)).obj SA).hom ≫ spMap κ := by
            rw [Category.assoc, hβ''.1.w]
        _ = spMap κ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ spMap κ) ls).trans (Category.id_comp _))
        _ = spMap κ ≫ (c ((n : ℤ) • a)).left ≫ B.hom := by rw [Over.w (c ((n : ℤ) • a))]; exact (Category.comp_id _).symm
        _ = (spMap κ ≫ (c ((n : ℤ) • a)).left) ≫ B.hom := (Category.assoc _ _ _).symm

end GlobalTheory.LowLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFibrePower_point_lifts_to_lower_base : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (F : SFam h n (zetaAway n)) (r : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsDiscreteValuationRing V₁ → ∀ (b₁ : cycAway n →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap b₁), ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V₁ →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = h ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b₁ ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ (GlobalTheory.LowChart.siegAt F v _ hs).A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' (GlobalTheory.LowChart.siegAt F v _ hs).A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((GlobalTheory.LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  first | exact @GlobalTheory.LowLift.main | exact GlobalTheory.LowLift.main | (intros; apply GlobalTheory.LowLift.main <;> assumption)
end
