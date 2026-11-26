module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationPullbackLocalHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearRingActionGenericFibreOfActsAs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearRingActionGenericFibreOfActsAs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oAct_oLinear_of_actsAs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oG : RingAct G O), (∀ a, ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) (oG.act a)) → ∃ oA : A.OAct O, U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oG hgA
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have hg := oG.hom
  have one := oG.map_one
  have mul := oG.map_mul
  have add := oG.map_add
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (oG.act a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        haveI := hg a; haveI := hg b
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs R hR D A G hG U O o a (oG.act a)
        (oG.act (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, fA, F]
end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearRingActionGenericFibreOfActsAsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_ringAction_genericFibre_of_actsAs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oG : RingAct G O), (∀ a, ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) (oG.act a)) → ∃ oA : A.OAct O, U.toUnifPre.OLinear O o oA oG := by
  first | exact @GlobalTheory.Mum.exists_oAct_oLinear_of_actsAs | exact GlobalTheory.Mum.exists_oAct_oLinear_of_actsAs | (intros; apply GlobalTheory.Mum.exists_oAct_oLinear_of_actsAs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsOnThickeningsOfPullbackUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsOnThickeningsOfPullbackUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum


open GlobalTheory.TorusCoord GlobalTheory.PullLinear in
theorem actsAs_of_isPullUnif : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (I : Ideal R) (I' : Ideal V) (D : DegData R I) (D' : DegData V I') (hD : IsPullDeg θ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf θ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif θ hD bc U U' → ∀ (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) (b' : D'.toPre.P.A ⟶ D'.toPre.P.A) (h' : D'.toPre.X → D'.toPre.X) (g' : G' ⟶ G'), IsMonHom b' → ActsAs U.toUnifPre b h g → g' ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf θ)).map g → b' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map b → (∀ y, hD.xe (h' y) = h (hD.xe y)) → ActsAs U'.toUnifPre b' h' g' := by
  intro R R' _ _ _ _ φ I I' D D' hD A A' G _ _ G' _ _ bc U U' hU b k₀ g b' k' g' hb' hlin hG hB hx
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ), ((Over.pullback (thick R' I' e)).map g').left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map g).left := by
    intro e
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom hG, Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ), (Over.pullback (thick R' I' e)).map g' ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (c : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (c.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = c.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ c u
      rw [Over.comp_left, Category.assoc, map_left_fst, PullLinear.pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map g).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ b.left := by
      rw [← k, ← (hlin e).1]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map g') ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ b' := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map g').left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ b'.left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom hB, (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine fun e => ⟨hq e, ?_⟩
  obtain ⟨t, ht, hi⟩ := (hlin e).2
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map g') ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (k' χ)).1 ((hpt e).2 (k' χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsOnThickeningsOfPullbackUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actsOnThickenings_of_pullback_uniformisation : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (I : Ideal R) (I' : Ideal V) (D : DegData R I) (D' : DegData V I') (hD : IsPullDeg θ D.toPre D'.toPre) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf θ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif θ hD bc U U' → ∀ (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) (b' : D'.toPre.P.A ⟶ D'.toPre.P.A) (h' : D'.toPre.X → D'.toPre.X) (g' : G' ⟶ G'), IsMonHom b' → ActsAs U.toUnifPre b h g → g' ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf θ)).map g → b' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf θ)).map b → (∀ y, hD.xe (h' y) = h (hD.xe y)) → ActsAs U'.toUnifPre b' h' g' := by
  first | exact @GlobalTheory.Mum.actsAs_of_isPullUnif | exact GlobalTheory.Mum.actsAs_of_isPullUnif | (intros; apply GlobalTheory.Mum.actsAs_of_isPullUnif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationPullbackLocalHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.ulin_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (θ : R →+* V), Base R → Base V → IsLocalHom θ → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap θ (genericPoint (Sp V)) ∈ W → ∃ (D₁ : DegData V (maximalIdeal V)) (hD : IsPullDeg θ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing V))) (U₁ : Unif (maximalIdeal V) D₁ A₁ ((Over.pullback (specOf θ)).obj G)) (_ : Module O D₁.toPre.X) (o₁ : D₁.toPre.OAct O) (oA₁ : A₁.OAct O) (oG₁ : RingAct ((Over.pullback (specOf θ)).obj G) O), LBIso U₁.LG.L (U.LG.L.pull (pullback.fst G.hom (specOf θ))) ∧ (∀ (a : O) (y : D₁.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (o.onB.act a).left) ∧ (∀ a, oG₁.act a = (Over.pullback (specOf θ)).map (oG.act a)) ∧ U₁.toUnifPre.OLinear O o₁ oA₁ oG₁ := by
  intro R V _ _ _ _ _ _ θ bR bV hθ D A G _ _ hG U O _ _ _ o oA oG lin W hψ hW
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf θ)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D₁, A₁, hD, U₁, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R bR D A G hG U V bV.1 θ hθ W hψ hW _ (Iso.refl _) mR
  obtain ⟨m, o₁, hx, ho⟩ := GlobalTheory.FactorPull.degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R V θ _ _ hD O o
  obtain ⟨oA₁, lin₁⟩ := GlobalTheory.T.exists_linear_ringAction_genericFibre_of_actsAs V bV D₁ A₁ _ (IsSemiAbelian.pullback _ G hG) U₁ O o₁ (GlobalTheory.FactorPull.ringActPull (specOf θ) oG) fun a =>
    GlobalTheory.T.actsOnThickenings_of_pullback_uniformisation R V θ _ _ D D₁ hD A A₁ G _ (Iso.refl _) U U₁ hU (o.onB.act a) (fun χ => star a • χ) (oG.act a) _ _ _ (o₁.onB.hom a)
      (fun e => ⟨lin.q_lin e a, lin.i_lin e a⟩) ((Category.comp_id _).trans (Category.id_comp _).symm) (ho a) (hx (star a))
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁, hD, A₁, U₁, m, o₁, oA₁, _, ?_, hx, fun a => GlobalTheory.PullLinear.act_proj _ hD.e.hom (ho a), fun _ => rfl, lin₁⟩
  have H : LBIso _ _ := ⟨wL, hwL⟩
  rwa [show (Iso.refl ((Over.pullback (specOf θ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf θ) = pullback.fst G.hom (specOf θ) from Category.id_comp _] at H
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationPullbackLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearUniformisation_pullback_localHom : ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (θ : R →+* V), Base R → Base V → IsLocalHom θ → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap θ (genericPoint (Sp V)) ∈ W → ∃ (D₁ : DegData V (maximalIdeal V)) (hD : IsPullDeg θ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing V))) (U₁ : Unif (maximalIdeal V) D₁ A₁ ((Over.pullback (specOf θ)).obj G)) (_ : Module O D₁.toPre.X) (o₁ : D₁.toPre.OAct O) (oA₁ : A₁.OAct O) (oG₁ : RingAct ((Over.pullback (specOf θ)).obj G) O), LBIso U₁.LG.L (U.LG.L.pull (pullback.fst G.hom (specOf θ))) ∧ (∀ (a : O) (y : D₁.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (o.onB.act a).left) ∧ (∀ a, oG₁.act a = (Over.pullback (specOf θ)).map (oG.act a)) ∧ U₁.toUnifPre.OLinear O o₁ oA₁ oG₁ := by
  first | exact @GlobalTheory.Mum.ulin_pull | exact GlobalTheory.Mum.ulin_pull | (intros; apply GlobalTheory.Mum.ulin_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauOnOpen

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens}

theorem tauW_isGen (ψW : PsiOn D W) (a b : D.X) : (ψW.tau a b).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ψW.psi_gen _) (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (ψW.psi_gen _)))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))

theorem val_tauW_generic (ψW : PsiOn D W) (a b : D.X) (lam : (TK R).left ⟶ W.toScheme) (h : lam ≫ W.ι = jK R)
    (z : (TK R).left) (J) (hJ : Good D.P.L z J) : val (ψW.tau a b) lam z J = val (D.tau a b) (𝟙 _) z J := by
  have hW : lam ≫ W.ι = 𝟙 _ ≫ jK R := h.trans (Category.id_comp _).symm
  obtain ⟨mu, l₁, l₂⟩ : ∃ mu : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, mu ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      mu ≫ (jK R ∣_ W) = lam :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ hW,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have vψ : ∀ χ, val (ψW.psi χ) lam z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
    have e := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) mu).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at e
    exact e
  have vρ : val (D.rigW W) lam z J = val D.rigK (𝟙 _) z J := by
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    exact congrArg (fun q => val D.rig q z J) hW
  refine (TauPull.val_tauW ψW lam hJ a b).trans (Eq.trans ?_ (TauPull.val_tau (𝟙 _) hJ a b).symm)
  rw [← vψ, ← vψ, ← vψ, ← vρ]

end GlobalTheory.TauOnOpen

namespace GlobalTheory

theorem exists_tau_onOpen : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  intro R _ _ D W ψW a b
  obtain ⟨t, ht, hv⟩ : ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TW W).left) (z : Z) (J), Good D.P.L z J →
        val t r z J = val (ψW.tau a b) r z J := by
    refine exists_gen D.P.isLB (fun U _ h => ?_) (ψW.tau a b) (TauOnOpen.tauW_isGen ψW a b)
    have e₁ : (toUnit (TW W) ≫ D.c (a + b)).left = ((toUnit (TW W) ≫ D.c a) * (toUnit (TW W) ≫ D.c b)).left := by
      rw [D.c_add]; exact congrArg (fun q : TW W ⟶ D.P.A => q.left) (MonObj.comp_mul (toUnit (TW W)) (D.c a) (D.c b))
    have e₂ : (toUnit (TW W)).left ≫ eSec D.P.A = (1 : TW W ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, e₁, e₂]
    simp [lamPts, negε]
  exact ⟨t, ht, hv, fun lam h z J hJ => (hv _ lam z J hJ).trans (TauOnOpen.val_tauW_generic ψW a b lam h z J hJ)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_period_generator_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  first | exact @GlobalTheory.exists_tau_onOpen | exact GlobalTheory.exists_tau_onOpen | (intros; apply GlobalTheory.exists_tau_onOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorProportionalitySpreadsFromGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorProportionalitySpreadsFromGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenSpread

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} (hF : FormEq φ₁ ε₁ φ₂ ε₂)
    {t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)} {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t₁ r z J * (val t₂ r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 (hF U h))
    (LB.mulGen L _ _ _ _ t₁ (LB.invGen L _ _ t₂)) (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ (DVR.invGen_isGen _ _ _ _ h₂))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

def fnOn {R : Type} [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Sp S) (a : R) :
    gs (spMap f) z ⊤ (fnOn a) = gs (𝟙 (Sp S)) z ⊤ (fnOn (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have := gs_pull (𝟙 (Sp S)) (spMap f) z ⊤ trivial (fnOn a)
  rw [Category.id_comp] at this
  rw [← this]
  exact congrArg (gs (𝟙 (Sp S)) z ⊤) e.symm

def gsHom {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom

theorem gsHom_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gsHom r z a = gs r z ⊤ a :=
  (gs_eq r z ⊤ trivial a).symm

theorem gs_res_fn {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (W : (Sp R).Opens) (r : Sp S ⟶ W.toScheme)
    (hr : r ≫ W.ι = spMap f) (z : Sp S) (a : R) :
    gsHom r z (W.ι.appTop.hom (fnOn a)) = gsHom (𝟙 (Sp S)) z (fnOn (f a)) := by
  rw [gsHom_apply, gsHom_apply, ← gs_spMap, ← hr]
  exact gs_pull r W.ι z ⊤ trivial _

theorem eq_zero_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens)
    (lam : Sp (FractionRing R) ⟶ W.toScheme) (hl : lam ≫ W.ι = jK R) (z : Sp (FractionRing R))
    (d : Γ(W.toScheme, ⊤)) (hd : gsHom lam z d = 0) : d = 0 := by
  haveI : AlgebraicGeometry.IsReduced W.toScheme := isReduced_of_isOpenImmersion W.ι
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w ∈ W.toScheme.basicOpen d := by
    by_contra h
    exact hne (le_bot_iff.1 fun w hw => h ⟨w, hw⟩)
  have hsp : W.ι (lam z) ⤳ W.ι w := by
    have e : W.ι (lam z) = jK R z := by rw [← hl]; rfl
    rw [e]
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have hz : (z : PrimeSpectrum (FractionRing R)).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime z).ne_top
    have ha' : algebraMap R (FractionRing R) a ∈ (z : PrimeSpectrum (FractionRing R)).asIdeal := ha
    rw [hz, Ideal.mem_bot] at ha'
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (ha'.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  have hsp' : lam z ⤳ w := W.ι.isOpenEmbedding.isInducing.specializes_iff.1 hsp
  have hm : z ∈ lam ⁻¹ᵁ W.toScheme.basicOpen d := hsp'.mem_open (W.toScheme.basicOpen d).isOpen hw
  rw [Scheme.preimage_basicOpen] at hm
  have hu := (Scheme.mem_basicOpen _ (U := lam ⁻¹ᵁ ⊤) _ z trivial).1 hm
  exact not_isUnit_zero (hd ▸ hu : IsUnit (0 : (Sp (FractionRing R)).presheaf.stalk z))

theorem val_spread : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  intro R V _ _ _ _ θ W X L hL K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ hF t₁ t₂ h₁ h₂ lam hl g hg x y k k' hy hk hk' H z J hJ
  obtain ⟨c, hc⟩ := exists_ratio hL hF h₁ h₂
  have hu : ∀ {F : Type} [Field F] (u : Fˣ) (w : Sp F),
      (gm (𝟙 (Sp F)) w ⊤ (unitOn u)).val = gsHom (𝟙 (Sp F)) w (fnOn (u : F)) := fun u w =>
    ((gsHom_apply _ _ _).trans (gs_unit _ w ⊤ trivial (unitOn u))).symm
  let z₀ : Sp (FractionRing R) := (⊥ : PrimeSpectrum (FractionRing R))
  choose I hI using fun χ : (TK R).left ⟶ X => exists_chart hL (χ z₀)
  have e₀ : gsHom lam z₀ c = gsHom (𝟙 (Sp (FractionRing R))) z₀ (fnOn (k : FractionRing R)) := by
    have := hc _ lam z₀ I hI
    rw [H z₀ I hI, mul_inv_cancel_right] at this
    exact (gsHom_apply _ _ _).trans (this.symm.trans (hu k z₀))
  have e₁ : c * W.ι.appTop.hom (fnOn y) - W.ι.appTop.hom (fnOn x) = 0 := by
    refine eq_zero_of_generic W lam hl z₀ _ ?_
    rw [map_sub, map_mul, gs_res_fn (algebraMap R (FractionRing R)) W lam hl,
      gs_res_fn (algebraMap R (FractionRing R)) W lam hl, ← hk, map_mul, map_mul]
    exact sub_eq_zero.2 (congrArg (· * _) e₀)
  have hg' : g ≫ W.ι = spMap ((algebraMap V (FractionRing V)).comp θ) :=
    hg.trans (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  have e₂ := congrArg (gsHom (Z := Sp (FractionRing V)) g z) (sub_eq_zero.1 e₁)
  rw [map_mul, gs_res_fn _ W g hg', gs_res_fn _ W g hg', RingHom.comp_apply, RingHom.comp_apply, ← hk', map_mul,
    map_mul] at e₂
  have hy' : IsUnit (algebraMap V (FractionRing V) (θ y)) :=
    isUnit_iff_ne_zero.2 fun h => hy (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))
  have e₃ := ((hy'.map fnOn).map (gsHom (𝟙 (Sp (FractionRing V))) z)).mul_right_cancel e₂
  refine mul_inv_eq_iff_eq_mul.1 (Units.ext ?_)
  exact (hc _ g z J hJ).trans ((gsHom_apply _ _ _).symm.trans (e₃.trans (hu k' z).symm))

end GlobalTheory.GenSpread

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorProportionalitySpreadsFromGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_proportionality_spreads_from_generic : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  first | exact @GlobalTheory.GenSpread.val_spread | exact GlobalTheory.GenSpread.val_spread | (intros; apply GlobalTheory.GenSpread.val_spread <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.FactorPeriod


set_option maxHeartbeats 800000 in
theorem factor_period : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  intro R V _ _ _ _ θ Q D₀ F W ψW g hg a b u x y k k' hu hy hk hk' hτ z J J' hJ hJ'
  letI := D₀.P.isAb.comm
  obtain ⟨t, ht, tv, tl⟩ := GlobalTheory.T.exists_period_generator_on_open R D₀ W ψW (F.xi a) (F.f • F.xi b)
  have hQ : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left ≫
      (lift (fst Q.B Q.B ≫ F.inc) (snd Q.B Q.B ≫ F.inc ≫ F.o.onB.act F.f) : G2 Q.B ⟶ G2 D₀.P.A).left =
      𝟙 _ ≫ (lift (toUnit T ≫ D₀.c (F.xi a)) (toUnit T ≫ D₀.c (F.f • F.xi b))).left := fun T => by
    rw [Category.id_comp, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, F.o.c_lin, F.c_xi, F.c_xi]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso _ _ Q.B D₀.P.A Q.M.L D₀.P.L Q.M.isLB D₀.P.isLB _ F.w F.w_gen (TW W) (TW W)
    (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b) _ _ (𝟙 _) (hQ (TW W)) t ht
  obtain ⟨lam, hlam⟩ : ∃ lam : (TK R).left ⟶ W.toScheme, lam ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact GlobalTheory.TauPull.jK_mem p _ ⟨(g z).1, (g z).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have hl : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left =
      T.hom ≫ (lift (Q.c a) (Q.c b)).left := fun T => by
    rw [← comp_lift]; rfl
  have H := GlobalTheory.T.generator_proportionality_spreads_from_generic R V θ W Q.B.left Q.M.L Q.M.isLB (Fin 4) (Fin 4)
    (lamPts (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)) negε
    (fun i => W.ι ≫ lamPts (Q.c a) (Q.c b) i) negε (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 2
      fin_cases i
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TW W)) (Q.c a) (Q.c b)).symm
      · rfl
      · rfl
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TW W))).symm)
    t₁ (LB.pullGen Q.M.L _ _ u W.ι) ht₁ (DVR.pullGen_isGen _ _ _ _ hu _) lam hlam g hg x y k k' hy hk hk'
    (fun p I' hI' => by
      obtain ⟨I, hI⟩ := DegPull.exists_good' D₀.P.isLB p
      have e₁ := v₁ _ lam p I I' hI hI'
      have e₂ : lam ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
          (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left := by
        rw [hl, hl, ← Category.assoc]
        exact congrArg (· ≫ _) hlam
      rw [e₂] at e₁
      erw [Category.comp_id] at e₁
      refine e₁.trans ((congrArg (_ * ·) (tl lam hlam p I hI)).trans ((F.tau a b p I I' hI hI').symm.trans
        ((hτ p I' hI').trans (congrArg (_ * ·) ?_))))
      rw [val_pull hI', hlam]
      rfl) z J' hJ'
  have e₁ := v₁ _ g z J J' hJ hJ'
  have e₂ : g ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left := by
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ _) hg
  rw [e₂] at e₁
  erw [Category.comp_id] at e₁
  rw [val_pull hJ', hg] at H
  exact H.symm.trans (e₁.trans (congrArg (_ * ·) (tv _ g z J hJ)))

end GlobalTheory.FactorPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_factor_periods_at_generating_point : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  first | exact @GlobalTheory.FactorPeriod.factor_period | exact GlobalTheory.FactorPeriod.factor_period | (intros; apply GlobalTheory.FactorPeriod.factor_period <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauPullOn

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.FactorPull
open GlobalTheory.PsiEvenPull (proj)

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {D₀ : DegPre R}
  {D₁ : DegPre V} (hD : IsPullDeg θ D₀ D₁) {z : (TK V).left} {J : ((TK V).left ⟶ D₀.P.A.left) → D₀.P.L.ι}
  {J₁ : ((TK V).left ⟶ D₁.P.A.left) → D₁.P.L.ι} (hJ : Good D₀.P.L z J) (hJ₁ : Good D₁.P.L z J₁)
include hJ hJ₁

theorem psiW_val (x : D₁.X) : val (hD.psiW.psi (hD.xe x)) hD.g z J =
    (om hD.w z J J₁ (D₁.xK x))⁻¹ * val (D₁.psi x) (𝟙 _) z J₁ := by
  have e := PsiEvenPull.psi_pull hD x (𝟙 _) z hJ hJ₁
  simp only [Category.id_comp] at e
  exact e

theorem rigW_val : val (D₀.rigW hD.W) hD.g z J =
    om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left * val D₁.rigK (𝟙 _) z J₁ := by
  have pm := (maps_iff hD.w _ (fun _ => eSec D₀.P.A) _ D₁.rig D₀.rig (specOf θ) _
    (rigPull_le (proj hD) (specOf θ) hD.he D₀.P.L) (fun _ => rfl)).1 hD.w_rig
  have e := pmaps_om (fun _ => hD.he) pm (jK V) z hJ hJ₁
  rw [Fintype.prod_unique, zpow_one] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm))
  rw [Category.id_comp]
  exact (congrArg (fun q => val D₀.rig q z J) hD.g_comm).trans e


omit hJ hJ₁ in
theorem tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  intro R V _ _ _ _ θ D₀ D₁ hD
  refine ⟨sqOf (pull_grp hD), lamIso (pull_grp hD) hD.w, isSquare_sqOf _, isGen_lamIso _ _ hD.w_gen,
    fun a b z J J₁ hJ hJ₁ => ?_⟩
  have g := gw_lam (pull_grp hD) hD.w (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z hJ hJ₁
  have p := prod_lam (DVR.cP D₁ (TK V) a) (DVR.cP D₁ (TK V) b) (om hD.w z J J₁)
  rw [← DVR.cPoint_add] at p
  have l : lamVal (lamIso (pull_grp hD) hD.w) (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ =
      om hD.w z J J₁ (D₁.xK (a + b)) * (om hD.w z J J₁ (D₁.xK a))⁻¹ * (om hD.w z J J₁ (D₁.xK b))⁻¹ *
        om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left := by
    refine Eq.trans ?_ (g.trans p)
    simp only [Category.assoc]
    rfl
  rw [l, TauPull.val_tauW _ _ hJ, TauPull.val_tau _ hJ₁, ← map_add (f := _), psiW_val hD hJ hJ₁, psiW_val hD hJ hJ₁,
    psiW_val hD hJ hJ₁, rigW_val hD hJ hJ₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauPullOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_pulled_degeneration_data : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  first | exact @GlobalTheory.TauPullOn.tau_pull | exact GlobalTheory.TauPullOn.tau_pull | (intros; apply GlobalTheory.TauPullOn.tau_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorTau

theorem lift_square {S S' : Scheme.{0}} {B C : Over S} {B₁ C₁ : Over S'} {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}
    {β₂ : (G2 B₁).left ⟶ (G2 B).left} {δ₂ : (G2 C₁).left ⟶ (G2 C).left} (hβ : IsSquare β β₂) (hδ : IsSquare δ δ₂)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ δ₂ =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, hδ.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hβ.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, hδ.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hβ.2, Category.assoc]

theorem pair_square {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B₁ T : Over S'} {β : B₁.left ⟶ B.left}
    {β₂ : (G2 B₁).left ⟶ (G2 B).left} (hβ : IsSquare β β₂) {a b : 𝟙_ (Over S) ⟶ B} {a₁ b₁ : 𝟙_ (Over S') ⟶ B₁}
    (ha : a₁.left ≫ β = f ≫ a.left) (hb : b₁.left ≫ β = f ≫ b.left) :
    (lift (toUnit T ≫ a₁) (toUnit T ≫ b₁)).left ≫ β₂ = (T.hom ≫ f) ≫ (lift a b).left := by
  have hT : (toUnit T).left = T.hom := (Category.comp_id _).symm.trans (Over.w (toUnit T))
  apply pullback.hom_ext
  · show _ ≫ (fst B B).left = _ ≫ (fst B B).left
    rw [Category.assoc, hβ.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc, ha, hT, Category.assoc]
  · show _ ≫ (snd B B).left = _ ≫ (snd B B).left
    rw [Category.assoc, hβ.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc, hb, hT, Category.assoc]


set_option maxHeartbeats 800000 in
theorem factor_tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex hQ
  obtain ⟨β, β₂, wP, gβ, sβ, hwP, hc, hτ⟩ := hQ
  refine ⟨β, gβ, hc, fun inc xi hi hxi hcx => ?_⟩
  letI := D₀.P.isAb.comm
  letI := D₁.P.isAb.comm
  obtain ⟨w₁₂, hw₁₂, v₁₂⟩ := GlobalTheory.T.mumfordBundleIso_comp_values_mul _ _ _ Q'.B Q.B D₀.P.A Q'.M.L Q.M.L D₀.P.L Q'.M.isLB Q.M.isLB D₀.P.isLB
    β₂ _ _ rfl F.w F.w_gen wP hwP
  obtain ⟨δ₂, w₀, sδ, hw₀, v₀⟩ := GlobalTheory.T.exists_periods_pulled_degeneration_data R V θ D₀ D₁ hD
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  obtain ⟨w, hw, vw⟩ := GlobalTheory.T.mumfordBundleIso_cancel_values_mul _ _ _ Q'.B D₁.P.A D₀.P.A Q'.M.L D₁.P.L D₀.P.L Q'.M.isLB D₁.P.isLB D₀.P.isLB
    _ δ₂ _ (lift_square sβ sδ hi hf) w₀ hw₀ w₁₂ hw₁₂
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
  obtain ⟨JQ, hJQ⟩ := DegPull.exists_good' Q.M.isLB z
  obtain ⟨u, x, y, k, k', hu, hy, hk, hk', t₀, t₁⟩ := hτ a b
  have e₁ := t₁ z JQ J' hJQ hJ'
  have e₂ := GlobalTheory.T.idempotent_factor_periods_at_generating_point R V θ Q D₀ F hD.W hD.psiW hD.g hD.g_comm (ex a) (ex b) u x y k k' hu hy hk hk' t₀
    z J₀ JQ hJ₀ hJQ
  have e₃ := v₁₂ _ (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J' JQ J₀ hJ' hJQ hJ₀
  have e₄ := vw _ (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J' J J₀ hJ' hJ hJ₀
  have e₅ := v₀ (xi a) (F.f • xi b) z J₀ J hJ₀ hJ
  have hP := pair_square (T := TK V) sβ (hc a) (hc b)
  have hq : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫
      (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left =
      (lift (toUnit (TK V) ≫ D₁.c (xi a)) (toUnit (TK V) ≫ D₁.c (F.f • xi b))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hcx, hcx]
    simp only [Category.assoc]
  rw [hP] at e₃
  rw [hq] at e₄
  rw [hx, hxi, hxi] at e₅
  rw [e₁, e₅, mul_left_comm, ← _root_.mul_assoc (lamVal w _ z J J'), ← e₄, e₃, _root_.mul_assoc]
  exact congrArg _ e₂

end GlobalTheory.FactorTau

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorTau.factor_tau_pull | exact GlobalTheory.FactorTau.factor_tau_pull | (intros; apply GlobalTheory.FactorTau.factor_tau_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedFactorAlgebraicPartPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedFactorAlgebraicPartPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.PFactorPull


open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.FactorPull in
theorem algebraic_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X) (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B (spMap θ) β → (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) → ∃ (inc : Q'.B ⟶ D₁.P.A) (pr : D₁.P.A ⟶ Q'.B) (xi : Q'.X →+ D₁.X) (xp : D₁.X →+ Q'.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left ∧ (∀ y, hD.xe (xi y) = F.xi (ex y)) ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) ∧ (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁.X, ∃ y, star F.e • z = star F.e • F.f • xi y) := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex β gp hcβ
  have gp' := pull_grp hD
  obtain ⟨inc, mi, hi⟩ := hom_pull gp gp' F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gp' gp F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : Q'.X →+ D₁.X, ∀ y, hD.xe (xi y) = F.xi (ex y) :=
    ⟨hD.xe.symm.toAddMonoidHom.comp (F.xi.comp ex.toAddMonoidHom), fun y => hD.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁.X →+ Q'.X, ∀ y, ex (xp y) = F.xp (hD.xe y) :=
    ⟨ex.symm.toAddMonoidHom.comp (F.xp.comp hD.xe.toAddMonoidHom), fun y => ex.apply_symm_apply _⟩
  have hc : ∀ y, D₁.c (xi y) = Q'.c y ≫ inc := fun y => ext_pull gp' (by
    rw [hD.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (Q'.c y).left,
      hcβ, Category.assoc]
    try rfl)
  refine ⟨inc, pr, xi, xp, hi, hxi, mi, mp, ext_pull gp ?_, ext_pull gp' ?_, fun y => ex.injective ?_,
    fun y => hD.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD.xe h
    simp only [hx, hxi] at h'
    exact ex.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD.xe z)
    refine ⟨ex.symm y, hD.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, ex.apply_symm_apply, hy]

end GlobalTheory.PFactorPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedFactorAlgebraicPartPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedFactor_algebraic_part_pullback : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X) (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B (spMap θ) β → (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) → ∃ (inc : Q'.B ⟶ D₁.P.A) (pr : D₁.P.A ⟶ Q'.B) (xi : Q'.X →+ D₁.X) (xp : D₁.X →+ Q'.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left ∧ (∀ y, hD.xe (xi y) = F.xi (ex y)) ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧ (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) ∧ (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁.X, ∃ y, star F.e • z = star F.e • F.f • xi y) := by
  first | exact @GlobalTheory.PFactorPull.algebraic_pull | exact GlobalTheory.PFactorPull.algebraic_pull | (intros; apply GlobalTheory.PFactorPull.algebraic_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum


open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in
theorem lamRetract_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (inc : G ⟶ G₀) (v : G₀ ⟶ G₀) (L : LB G₀.left) (L₁ : LB ((Over.pullback f).obj G₀).left) (P : LB (G2 G).left), L.IsLB → L₁.IsLB → P.IsLB → LBIso L₁ (L.pull (pullback.fst G₀.hom f)) → LBIso P ((abelian₂ G₀ L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ v) : G2 G ⟶ G2 G₀).left) → ∃ π₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left, IsSquare (G' := (Over.pullback f).obj G) (G := G) (pullback.fst G.hom f) π₂ ∧ LBIso ((abelian₂ ((Over.pullback f).obj G₀) L₁).pull (lift (fst _ _ ≫ (Over.pullback f).map inc) (snd _ _ ≫ (Over.pullback f).map inc ≫ (Over.pullback f).map v) : G2 ((Over.pullback f).obj G) ⟶ G2 ((Over.pullback f).obj G₀)).left) (P.pull π₂) := by
  intro S S' f G _ _ G₀ _ _ inc v L L₁ P hL hL₁ hP hw hPw
  have gG := isGrpPullback_pullback G f
  have gG' := isGrpPullback_pullback G₀ f
  obtain ⟨wL, hwL⟩ := hw
  refine ⟨sqOf gG, isSquare_sqOf gG, ?_⟩
  have hm := lift_sq gG gG' (u := inc) (v := inc ≫ v) (u₁ := (Over.pullback f).map inc)
    (v₁ := (Over.pullback f).map inc ≫ (Over.pullback f).map v) (map_left_fst _ _)
    (by rw [← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _)
  have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
  have lL : (abelian₂ G₀ L).IsLB := DVR.linComb_isLB _ hL _ _
  have lL₁ : (abelian₂ _ L₁).IsLB := DVR.linComb_isLB _ hL₁ _ _
  have H₁ := H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
    (chartPullLinComb (abelian₂ G₀ L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
  have H₂ := hPw.chartPull (Geo.Tor.chartPullPull _ (sqOf gG) _ rfl) (Geo.Tor.chartPullPull _ (sqOf gG) _ rfl)
  exact LBIso.trans (pull_isLB lL₁ _) (pull_isLB (pull_isLB lL _) _) (pull_isLB hP _) H₁ H₂.symm

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordPairingRetract_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (inc : G ⟶ G₀) (v : G₀ ⟶ G₀) (L : LB G₀.left) (L₁ : LB ((Over.pullback f).obj G₀).left) (P : LB (G2 G).left), L.IsLB → L₁.IsLB → P.IsLB → LBIso L₁ (L.pull (pullback.fst G₀.hom f)) → LBIso P ((abelian₂ G₀ L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ v) : G2 G ⟶ G2 G₀).left) → ∃ π₂ : (G2 ((Over.pullback f).obj G)).left ⟶ (G2 G).left, IsSquare (G' := (Over.pullback f).obj G) (G := G) (pullback.fst G.hom f) π₂ ∧ LBIso ((abelian₂ ((Over.pullback f).obj G₀) L₁).pull (lift (fst _ _ ≫ (Over.pullback f).map inc) (snd _ _ ≫ (Over.pullback f).map inc ≫ (Over.pullback f).map v) : G2 ((Over.pullback f).obj G) ⟶ G2 ((Over.pullback f).obj G₀)).left) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.lamRetract_baseChange | exact GlobalTheory.Mum.lamRetract_baseChange | (intros; apply GlobalTheory.Mum.lamRetract_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonPull

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _

end GlobalTheory.Mum.CanonPull


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.canon_pull_unif : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂)
:= by
  intro R V' _ _ _ _ _ _ θ hR hV hθ Q W G₁ _ _ P hG hC hW D' ex hP
  obtain ⟨hPl, D₀, F, A₀, G₀, i₀, c₀, U₀, oA, oG, inc, pr, hψ, hG₀, lin, mi, mp, hip, hpi, hL⟩ := hC
  have bR : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have bV : Base V' := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  obtain ⟨D₁, hD, A₁, U₁, m, o₁, oA₁, oG₁, hL₁, hx, ho, ha, lin₁⟩ :=
    GlobalTheory.T.linearUniformisation_pullback_localHom R V' θ bR bV hθ D₀ A₀ G₀ hG₀ U₀ F.O F.o oA oG lin W hψ hW
  obtain ⟨β, gβ, hc, H⟩ := GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback R V' θ Q D₀.toPre F D₁.toPre hD o₁ hx ho (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex hP
  obtain ⟨inc', pr', xi, xp, h₁, h₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉⟩ :=
    GlobalTheory.T.polarisedFactor_algebraic_part_pullback R V' θ Q D₀.toPre F D₁.toPre hD o₁ hx ho (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex β gβ hc
  obtain ⟨w, hw, hτ⟩ := H inc' xi h₁ h₂ b₇
  let F₁ : Factor D'.toPre D₁.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := hw,
      tau := fun a b z J J' hJ hJ' =>
        ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').symm.trans (hτ a b z J J' hJ hJ') }
  obtain ⟨π₂, sq, hl⟩ := GlobalTheory.T.mumfordPairingRetract_baseChange _ _ (specOf θ) G₁ G₀ inc (oG.act F.f) U₀.LG.L U₁.LG.L P U₀.LG.isLB U₁.LG.isLB hPl hL₁ hL
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data V' bV D' D₁ F₁ F.alg A₁ _ (IsSemiAbelian.pullback _ G₀ hG₀) U₁ oA₁ oG₁ lin₁
    ((Over.pullback (specOf θ)).obj G₁) (IsSemiAbelian.pullback _ G₁ hG) ((Over.pullback (specOf θ)).map inc)
    ((Over.pullback (specOf θ)).map pr) inferInstance inferInstance
    (by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])
    (by rw [← CategoryTheory.Functor.map_comp, hpi]; exact (ha _).symm)
  refine ⟨(Over.pullback (specOf θ)).obj G₁, inferInstance, inferInstance, _, π₂, A, U, isGrpPullback_pullback G₁ (specOf θ), sq, ?_⟩
  rw [show oG₁.act F₁.f = (Over.pullback (specOf θ)).map (oG.act F.f) from ha _] at hU
  exact LBIso.trans (GlobalTheory.Mum.CanonPull.lam_isLB _ U.LG.isLB)
    (pull_isLB (GlobalTheory.Mum.CanonPull.lam_isLB _ U₁.LG.isLB) _) (pull_isLB hPl _) hU hl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_mumford_family_pullback_local_uniformised : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  first | exact @GlobalTheory.Mum.canon_pull_unif | exact GlobalTheory.Mum.canon_pull_unif | (intros; apply GlobalTheory.Mum.canon_pull_unif <;> assumption)
end
