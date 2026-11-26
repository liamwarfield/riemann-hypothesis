module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtCubicalSymmetricEvenFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataUniformiseFiniteExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtCompIsPullDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FinExtComp

theorem finExt_comp_isPullDeg : ∀ (R R₀ R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₀ : R →+* R₀) (ρ₁ : R₀ →+* R₁) (D : DegPre R) (D₀ : DegPre R₀) (D₁ : DegPre R₁), FinExt ρ₀ → FinExt ρ₁ → Nonempty (IsPullDeg ρ₀ D D₀) → Nonempty (IsPullDeg ρ₁ D₀ D₁) → FinExt (ρ₁.comp ρ₀) ∧ Nonempty (IsPullDeg (ρ₁.comp ρ₀) D D₁) := by
  intro R R₀ R₁ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ D D₀ D₁ h₀ h₁ ⟨p⟩ ⟨q⟩
  exact ⟨⟨h₁.1, h₁.2.1.comp h₀.2.1, h₁.2.2.comp h₀.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp h₀.2.1 h₁.2.1 p q⟩

end GlobalTheory.Mum.FinExtComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPulledBackFactorSamePolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPulledBackFactorSamePolarisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorIdent

theorem squareGroup_hom_ext_projections {S : Scheme.{0}} (H : Over S) {X : Scheme.{0}} (a b : X ⟶ (G2 H).left)
    (h1 : a ≫ (fst H H).left = b ≫ (fst H H).left) (h2 : a ≫ (snd H H).left = b ≫ (snd H H).left) : a = b :=
  pullback.hom_ext h1 h2

theorem samePol_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → ∀ (A₉ : PolAV (Sp (FractionRing R₉))) (D₉' : DegData R₉ (maximalIdeal R₉)) (U₉ : Unif (maximalIdeal R₉) D₉' A₉ G₉), U₉.LG = P₉.L → ∃ D₉ : DegData R₉ (maximalIdeal R₉), Nonempty (IsPullDeg ρ₉ D.toPre D₉.toPre) ∧ SamePol D₉.toPre D₉'.toPre := by
  intro R _ _ _ hB D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉
    hfin hpb₉ hsq₉ hsa₉ hlam₉ A₉ D₉' U₉ hLG
  obtain ⟨hadm, hinj, hfinite⟩ := hfin
  haveI : CharZero R := hB.2
  have hloc : IsLocalHom ρ₉ := RingHom.IsIntegral.isLocalHom (RingHom.IsIntegral.of_finite hfinite) hinj
  have hB₉ : Base R₉ := ⟨hadm, charZero_of_injective_ringHom hinj⟩
  obtain ⟨D₁, D₁', F₁, A₁', G₁', _, _, U₁', oA₁, oG₁, G₁, _, _, β, β₂, inc₁, pr₁, hpd, hsa₁', hlin₁, hsa₁, hinc₁, hpr₁,
      hip₁, hpi₁, hpb₁, hsq₁, hlb₁⟩ :=
    GlobalTheory.T.idempotentFactor_uniformised_groups_baseChange R hB.1 D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ hadm hinj hloc
  obtain ⟨e, he, hβ⟩ := grpPullback_iso hpb₉ hpb₁
  have hei : IsMonHom e.inv := inferInstance
  let m : G2 G₉ ⟶ G2 G₁ := lift (fst G₉ G₉ ≫ e.hom) (snd G₉ G₉ ≫ e.hom)
  have hm : β₉₂ = m.left ≫ β₂ := by
    apply squareGroup_hom_ext_projections G
    · rw [hsq₉.1, Category.assoc, hsq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc, hβ]
    · rw [hsq₉.2, Category.assoc, hsq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc, hβ]
  have hℓ : (lift (fst G₉ G₉ ≫ e.hom ≫ inc₁) (snd G₉ G₉ ≫ (e.hom ≫ inc₁) ≫ oG₁.act F₁.f) : G2 G₉ ⟶ G2 G₁').left =
      m.left ≫ (lift (fst G₁ G₁ ≫ inc₁) (snd G₁ G₁ ≫ inc₁ ≫ oG₁.act F₁.f) : G2 G₁ ⟶ G2 G₁').left := by
    rw [← Over.comp_left]
    congr 1
    simp [m]
  have hL' : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hL₁ : (abelian₂ G₁' U₁'.LG.L).IsLB := LB.isLB_linComb U₁'.LG.isLB _ _
  have h1 : LBIso (abelian₂ G₉ U₉.LG.L) ((abelian₂ G' U'.LG.L).pull
      (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
    rw [hLG]; exact hlam₉
  have h2 := GlobalTheory.GenSpread.lbIso_pull_pull hL'
    (a := (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ rfl
  have h3 := GlobalTheory.GenSpread.lbIso_pull_comp m.left hℓ hm hlb₁
  have hLam : LBIso (abelian₂ G₉ U₉.LG.L) ((abelian₂ G₁' U₁'.LG.L).pull
      (lift (fst G₉ G₉ ≫ e.hom ≫ inc₁) (snd G₉ G₉ ≫ (e.hom ≫ inc₁) ≫ oG₁.act F₁.f) : G2 G₉ ⟶ G2 G₁').left) :=
    LBIso.trans (LB.isLB_linComb U₉.LG.isLB _ _) (pull_isLB (pull_isLB hL' _) _) (pull_isLB hL₁ _)
      (LBIso.trans (LB.isLB_linComb U₉.LG.isLB _ _) (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) h1 h2)
      (LBIso.symm h3)
  have hsame : SamePol D₁.toPre D₉'.toPre :=
    GlobalTheory.T.samePolarisedData_of_idempotentFactor_uniformisation R₉ hB₉ D₁ D₁' F₁ A₁' G₁' hsa₁' U₁' oA₁ oG₁ hlin₁ G₉ hsa₉ (e.hom ≫ inc₁) (pr₁ ≫ e.inv)
      inferInstance inferInstance
      (by rw [Category.assoc, ← Category.assoc inc₁, hip₁, Category.id_comp, Iso.hom_inv_id])
      (by rw [Category.assoc, ← Category.assoc e.inv, Iso.inv_hom_id, Category.id_comp, hpi₁]) D₉' A₉ U₉ hLam
  exact ⟨D₁, hpd, hsame⟩

end GlobalTheory.Mum.FactorIdent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPulledBackFactorSamePolarisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_pulledBackFactor_samePolarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → ∀ (A₉ : PolAV (Sp (FractionRing R₉))) (D₉' : DegData R₉ (maximalIdeal R₉)) (U₉ : Unif (maximalIdeal R₉) D₉' A₉ G₉), U₉.LG = P₉.L → ∃ D₉ : DegData R₉ (maximalIdeal R₉), Nonempty (IsPullDeg ρ₉ D.toPre D₉.toPre) ∧ SamePol D₉.toPre D₉'.toPre := by
  first | exact @GlobalTheory.Mum.FactorIdent.samePol_pull | exact GlobalTheory.Mum.FactorIdent.samePol_pull | (intros; apply GlobalTheory.Mum.FactorIdent.samePol_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem isPullDeg_of_trait_unif : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R₀ _ _ _ hR D₀ A₀ G₀ _ _ hG U₀ W _ _ _ hW φ hφ hloc GW _ _ β DW AW UW hβ hLβ
  obtain ⟨hL1, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G₀ (spMap φ))
  have hbc' : bc.hom.left ≫ pullback.fst G₀.hom (specOf φ) = β := hbc
  have hGW : IsSemiAbelian GW := by
    have := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G₀ hG)

  have sq : spMap (GlobalTheory.ArcPull.fracMap hφ) ≫ jK R₀ = jK W ≫ spMap φ :=
    (GlobalTheory.ArcPull.fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hL1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hφ)) A₀
  have gpA : IsGrpPullback A'.A A₀.A (spMap (GlobalTheory.ArcPull.fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := GlobalTheory.ThetaBaseChange.grp_generic U₀.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj GW) G₀ (spMap (GlobalTheory.ArcPull.fracMap hφ) ≫ jK R₀)
      (pullback.fst GW.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback GW (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₀.gen.inv.left ≫ U₀.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A'.L.pull eA.hom.left) (U₀.LG.L.pull (pullback.fst GW.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G₀.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A₀.isLB gA) eA.hom.left)
      (pull_isLB U₀.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A₀.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₀.gen.inv.left)
      (chartPullLinComb A₀.L gA (fun _ => eA.hom.left) (fun _ => U₀.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₀.LG.L _ (fun _ => pullback.fst G₀.hom (jK R₀)) _ _ fun _ => ?_) U₀.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc', ← heA]; simp only [Category.assoc]

  have he : eSec GW ≫ bc.hom.left ≫ pullback.fst G₀.hom (specOf φ) = specOf φ ≫ eSec G₀ := by
    rw [hbc']; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, hwL, hm⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G₀ GW
    (bc.hom.left ≫ pullback.fst G₀.hom (specOf φ)) he U₀.LG UW.LG (by rw [hbc']; exact hLβ)

  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R₀ _ hR D₀
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R₀)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo

  obtain ⟨D₁, hD₁, U₁, hLG, -, -⟩ := h4.unifBaseChange R₀ W _ _ hR hW' φ (map_maximalIdeal_le φ) D₀ A₀ G₀ hG U₀
    Wo hψ hgen GW bc mbc A' dA eA mE wA UW.LG wL he hwL hm
  obtain ⟨-, w₀, -, g₀, -, m₀, -⟩ := exists_iso_pair_of_eq hLG
  obtain ⟨hDid, -⟩ := GlobalTheory.sixthLaws_and_unifUniq.2 W _ hW' D₁ DW A' AW GW hGW U₁ UW w₀ g₀ m₀
  have h := GlobalTheory.Mum.isPullDeg_unique_and_comp.2 R₀ W W φ (RingHom.id W) hφ Function.injective_id D₀.toPre D₁.toPre
    DW.toPre ⟨hD₁⟩ ⟨hDid⟩
  rwa [RingHom.id_comp] at h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_base_change_complete_dvr : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  first | exact @GlobalTheory.Mum.isPullDeg_of_trait_unif | exact GlobalTheory.Mum.isPullDeg_of_trait_unif | (intros; apply GlobalTheory.Mum.isPullDeg_of_trait_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitTwist

theorem exists_bundle_data_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → EvenOn P₉ → IsMonHom gen₉.hom → LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉ A₉ gen₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ hev₉ hgen₉ hgl₉
  have hR₉ : Base R₉ := ⟨hfin₉.1, by
    haveI := hR.2
    exact charZero_of_injective_ringHom hfin₉.2.1⟩
  obtain ⟨D₉', U₉, hL₉, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₉ hR₉ G₉ P₉ hG₉ hev₉ A₉ gen₉ hgen₉ hgl₉
  obtain ⟨D₉, hD₉, hsame⟩ := GlobalTheory.T.uniformisation_pulledBackFactor_samePolarisation R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ G₉ β₉ β₉₂ P₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ A₉ D₉' U₉ hL₉
  obtain ⟨R₀, _, _, _, ρ, D₀, G₀, _, _, β, β₂, A₀, U₀, hfin, hD₀, hpb, hsq, hlam⟩ :=
    GlobalTheory.T.samePolarisedData_uniformise_finite_extension R₉ hR₉ D₉ D₉' A₉ G₉ hG₉ U₉ hsame
  have hG₀ : IsSemiAbelian G₀ := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG₉
  obtain ⟨P, hPL, hPE⟩ := GlobalTheory.Mum.unif_evenOn R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀
  obtain ⟨hfin', hD'⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₉ R₀ ρ₉ ρ D.toPre D₉.toPre D₀.toPre hfin₉ hfin hD₉ hD₀
  have hsp : spMap (ρ.comp ρ₉) = spMap ρ ≫ spMap ρ₉ := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  refine ⟨R₀, inferInstance, inferInstance, inferInstance, ρ.comp ρ₉, D₀, G₀, inferInstance, inferInstance, β ≫ β₉, β₂ ≫ β₉₂, P, A₀, U₀.gen,
    hfin', hD', ?_, GlobalTheory.ZM.SiegPull.isSquare_comp hsq hsq₉, hG₀, ?_, hPE, U₀.gen_hom, ?_, ?_⟩
  · rw [hsp]; exact IsGrpPullback.comp hpb hpb₉
  · rw [hPL]
    rw [← hL₉] at hlam₉
    have i₁ : (abelian₂ G₀ U₀.LG.L).IsLB := LB.isLB_linComb U₀.LG.isLB _ _
    have i₂ : ((abelian₂ G₉ U₉.LG.L).pull β₂).IsLB := pull_isLB (LB.isLB_linComb U₉.LG.isLB _ _) _
    have i₃ : ((abelian₂ G' U'.LG.L).pull ((β₂ ≫ β₉₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)).IsLB :=
      pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _
    exact LBIso.trans i₁ i₂ i₃ hlam (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hlam₉ β₂ (Category.assoc _ _ _))
  · rw [hPL]; exact U₀.ext
  · intro W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW hpbW hLW
    rw [hPL] at hLW
    exact GlobalTheory.T.uniformization_base_change_complete_dvr R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀ W hW φ hφ hloc GW βW DW AW UW hpbW hLW

end GlobalTheory.Mum.TraitTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_uniformization_linear_action_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → EvenOn P₉ → IsMonHom gen₉.hom → LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  first | exact @GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits | exact GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits | (intros; apply GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorTrait

theorem exists_trait_of_unif (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] (hR : Base R₀)
    (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀]
    [IsCommMonObj G₀] (hG : IsSemiAbelian G₀) (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW)
      (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W)))
      (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (U₀.LG.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  have := hR.2
  have := hR.1.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R₀ (maximalIdeal R₀)
  haveI hloc : IsLocalHom φ := ((IsLocalRing.local_hom_tfae φ).out 1 5).mpr hc
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨DW, hD, AW, UW, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hW' φ hφ (map_maximalIdeal_le φ) hG U₀
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ) =
      pullback.fst G₀.hom (specOf φ) := Category.id_comp _
  refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf φ)).obj G₀, inferInstance, inferInstance,
    (Iso.refl ((Over.pullback (specOf φ)).obj G₀)).hom.left ≫ pullback.fst G₀.hom (specOf φ), DW, AW, UW, hW, hφ, hloc,
    ?_, ⟨hP.lg.choose, hP.lg.choose_spec.1⟩, ⟨hD⟩⟩
  exact (isGrpPullback_pullback G₀ (spMap φ)).congr rfl hb.symm

theorem factor_unif_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (P.L.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hR D D' F hA A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr h1 h2
  obtain ⟨R₉, _, _, _, ρ₉, G₉, _, _, β₉, β₉₂, P₉, A₉, gen₉, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    GlobalTheory.T.exists_finExt_cubicalSymmetric_even_factor R hR D D' F hA A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, A₀, gen₀, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
    GlobalTheory.T.semiabelian_uniformization_linear_action_descent R hR D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr h1 h2 R₉ ρ₉ G₉ β₉ β₉₂ P₉ A₉ gen₉ a1 a2 a3 a4 a5 a6 a7 a8
  haveI := hR.2
  have hR₀ : Base R₀ := ⟨c1.1, charZero_of_injective_ringHom c1.2.1⟩
  obtain ⟨D'', U'', hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₀ hR₀ G₀ P c5 c7 A₀ gen₀ c8 c9
  obtain ⟨W, _, _, _, φ, GW, _, _, β, DW, AW, UW, w1, w2, w3, w4, w5, -⟩ := exists_trait_of_unif R₀ hR₀ D'' A₀ G₀ c5 U''
  rw [hLG] at w5
  exact ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW, c1, c2, c3, c4, c5, w1, w2, w3,
    w4, w5, c10 W w1 φ w2 w3 GW β DW AW UW w4 w5, c6⟩

end GlobalTheory.Mum.FactorTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionTransferStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_uniformization_linear_action_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₀ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₀ (spMap φ) β ∧ LBIso UW.LG.L (P.L.L.pull β) ∧ Nonempty (IsPullDeg φ D₀.toPre DW.toPre) ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  first | exact @GlobalTheory.Mum.FactorTrait.factor_unif_at_trait | exact GlobalTheory.Mum.FactorTrait.factor_unif_at_trait | (intros; apply GlobalTheory.Mum.FactorTrait.factor_unif_at_trait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem factor_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hB D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW,
    hF₀, hD₀, hβ₀, hsq₀, hG₀, hW, hφi, hφl, hβ, hL, hDW, hLam⟩ :=
    GlobalTheory.T.semiabelian_uniformization_linear_action_transfer R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  haveI := hB.2
  have hB₀ : Base R₀ := ⟨hF₀.1, charZero_of_injective_ringHom hF₀.2.1⟩
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hF₁, hD₁, hβ₁, hL₁⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif R₀ hB₀ D₀ G₀ P hG₀ W hW φ hφi hφl GW β DW AW UW hβ hL hDW
  obtain ⟨hF, hD⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₀ R₁ ρ₀ ρ₁ D.toPre D₀.toPre D₁.toPre hF₀ hF₁ hD₀ hD₁
  obtain ⟨β₁₂, hsq₁, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ₁) G₀ G₁ β₁ hβ₁
  have hQ : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have key := hlam P.L.L U₁.LG.L _ (abelian₂ G' U'.LG.L) _ P.L.isLB U₁.LG.isLB hQ hL₁ hLam
  have hsp : spMap (ρ₁.comp ρ₀) = spMap ρ₁ ≫ spMap ρ₀ := by
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁.comp ρ₀, D₁, G₁, inferInstance, inferInstance,
    β₁ ≫ β₀, β₁₂ ≫ β₀₂, A₁, U₁, hF, hD, ?_, ?_, ?_⟩
  · rw [hsp]; exact hβ₁.comp hβ₀
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, hsq₁.1, Category.assoc]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, hsq₁.2, Category.assoc]
  · simpa only [Category.assoc] using key
end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentFactor_uniformised_of_degData_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  first | exact @GlobalTheory.Mum.factor_unif | exact GlobalTheory.Mum.factor_unif | (intros; apply GlobalTheory.Mum.factor_unif <;> assumption)
end
