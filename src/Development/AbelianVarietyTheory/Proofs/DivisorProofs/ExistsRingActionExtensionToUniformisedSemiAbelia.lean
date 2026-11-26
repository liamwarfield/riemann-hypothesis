module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThick
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfOfChars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbelia
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericOfFormal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenericEnd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem eq_of_generic (U : UnifPre I D A G) {g g' : G ⟶ G}
    (h : (Over.pullback (jK R)).map g = (Over.pullback (jK R)).map g') : g = g' := by
  have := U.smooth
  have := U.separated
  have : IsSchemeTheoreticallyDominant (jK R) :=
    schDom_spec_map _ (IsFractionRing.injective R (FractionRing R))
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w g, Over.w g']) (pullback.fst G.hom (jK R)) ?_
  have e := congrArg (fun k => k.left ≫ pullback.fst G.hom (jK R)) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

theorem exists_generic_of_formal (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) (hb : FormalEnd U a h' b) (g : G ⟶ G) (hg : IsMonHom g)
    (hgb : ∀ e, (Over.pullback (thick R I e)).map g = b e) :
    ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g' : G ⟶ G, IsMonHom g' →
      (Over.pullback (jK R)).map g' ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U a h' g' := by
  have := U.gen_hom
  refine ⟨U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom, inferInstance, fun g' _ hg' => ?_⟩
  obtain rfl : g' = g := eq_of_generic U (by
    rw [← cancel_mono U.gen.hom, hg', Iso.hom_inv_id_assoc])
  intro e
  obtain ⟨t, ht, hi⟩ := hb.2.2.2 e
  exact ⟨by rw [hgb]; exact hb.2.2.1 e, t, ht, by rw [hgb]; exact hi⟩

end GlobalTheory.Mum.GenericEnd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.GenericEnd.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o a
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o a
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings R hB.1 D A G hG U _ _ _ _ hE
  obtain ⟨g, hg, hgb⟩ := GlobalTheory.T.mumford_formalEndomorphism_algebraic R hB D A G hG U _ _ _ _ hE b hb
  obtain ⟨f, hf, hact⟩ := GlobalTheory.Mum.GenericEnd.exists_generic_of_formal U.toUnifPre (o.onB.act a)
    (DistribSMul.toAddMonoidHom D.toPre.X (star a)) b hb g hg hgb
  have hfun : (⇑(DistribSMul.toAddMonoidHom D.toPre.X (star a)) : D.toPre.X → D.toPre.X) = fun χ => star a • χ :=
    funext fun χ => DistribSMul.toAddMonoidHom_apply _ _ χ
  rw [hfun] at hact
  exact ⟨f, hf, hact⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericEndomorphism_mumford_ringAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  first | exact @GlobalTheory.Mum.GenericEnd.main | exact GlobalTheory.Mum.GenericEnd.main | (intros; apply GlobalTheory.Mum.GenericEnd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtends
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genericEnd_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  intro R _ _ _ hR G _ _ hG f hf
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  haveI := hN
  haveI := hIC
  haveI := hf
  obtain ⟨g, ⟨hg, hg'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG f
  exact ⟨g, hg, hg'⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtendsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_generic_endomorphism_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  first | exact @GlobalTheory.Mum.genericEnd_extends | exact GlobalTheory.Mum.genericEnd_extends | (intros; apply GlobalTheory.Mum.genericEnd_extends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbelia
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_oLinear_of_oAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o
  have hgen : IsMonHom U.gen.hom := U.gen_hom
  have hgeni : IsMonHom U.gen.inv := by infer_instance
  have L1 : ∀ a : O, ∃ g : G ⟶ G, IsMonHom g ∧ ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
    intro a
    obtain ⟨f, hf, hfA⟩ := GlobalTheory.T.exists_genericEndomorphism_mumford_ringAction R hR D A G hG U O o a
    obtain ⟨g, hg, hgf⟩ := GlobalTheory.T.semiAbelian_generic_endomorphism_extends R hR G hG (U.gen.hom ≫ f ≫ U.gen.inv) inferInstance
    refine ⟨g, hg, hfA g hg ?_⟩
    rw [hgf]; simp
  have L2 := GlobalTheory.T.uniformisedGroup_endomorphism_unique_of_thickening_action R hR D A G hG U
  choose g hg hgA using L1
  have one : g 1 = 𝟙 G := by
    refine L2 _ _ _ _ (hg 1) inferInstance (hgA 1) ?_
    have := actsAs_id U.toUnifPre
    rw [o.onB.map_one]
    convert this using 1
    funext χ; simp
  have mul : ∀ a b : O, g (a * b) = g b ≫ g a := by
    intro a b
    haveI := hg a; haveI := hg b
    refine L2 _ _ _ _ (hg (a * b)) inferInstance (hgA (a * b)) ?_
    have := actsAs_comp U.toUnifPre (hgA b) (hgA a)
    rw [o.onB.map_mul]
    convert this using 1
    funext χ; simp [star_mul, mul_smul]
  have add : ∀ a b : O, g (a + b) = padd G (g a) (g b) := by
    intro a b
    haveI := hg a; haveI := hg b
    have hp : IsMonHom (padd G (g a) (g b)) := by unfold padd; infer_instance
    refine L2 _ _ _ _ (hg (a + b)) hp (hgA (a + b)) ?_
    have := actsAs_padd U.toUnifPre (hgA a) (hgA b)
    rw [o.onB.map_add]
    convert this using 1
    funext χ; simp [star_add, add_smul]
  let oG : RingAct G O := { act := g, hom := hg, map_one := one, map_mul := mul, map_add := add }
  let F := Over.pullback (jK R)
  let fA : O → (A.A ⟶ A.A) := fun a => U.gen.inv ≫ F.map (g a) ≫ U.gen.hom
  let oA : A.OAct O :=
    { act := fA
      hom := fun a => by haveI := hg a; dsimp [fA]; infer_instance
      map_one := by simp [fA, F, one]
      map_mul := fun a b => by simp [fA, F, mul]
      map_add := fun a b => by
        simp only [fA, F, add, pull_padd]
        rw [padd_comp_hom, padd, padd, comp_lift_assoc]
      rosati := fun a => GlobalTheory.T.rosatiAdjoint_genericFibre_of_acts_star R hR D A G hG U O o a (g a) (g (star a)) (hg a) (hg (star a)) (hgA a) (hgA (star a)) }
  refine ⟨oA, oG, ⟨fun a => ?_, fun e a => (hgA a e).1, fun e a => (hgA a e).2⟩⟩
  simp [oA, oG, fA, F]
end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbeliaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  first | exact @GlobalTheory.Mum.exists_oLinear_of_oAct | exact GlobalTheory.Mum.exists_oLinear_of_oAct | (intros; apply GlobalTheory.Mum.exists_oLinear_of_oAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryTripleConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumRiggedFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumRiggedFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FrDict

theorem fst_isFinF : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) → (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S FA FW hFA hFW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hFA τ, hFW τ]
  exact hF

end GlobalTheory.FrDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumRiggedFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTriple_firstFiniteDatum_riggedFrames : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) → (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  first | exact @GlobalTheory.FrDict.fst_isFinF | exact GlobalTheory.FrDict.fst_isFinF | (intros; apply GlobalTheory.FrDict.fst_isFinF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleSecondFiniteDatumIsFiniteRigging
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem _root_.GlobalTheory.T.seesawTriple_secondFiniteDatum_isFinite_rigging : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn false FA').cart τ = X.rA'.s τ) → (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t) := by
  intro D T A A' WW X ψ θ α β νH S FA' FW hA' hW hI t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [hA' τ, hW τ]
  exact hF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryTripleConditions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr

theorem gBig_two {P Q S : GP} (hP : GBig P) (hQ : GBig Q)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      P G μ₀ C x b → Q G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (le_of_max_le_right hCF)
  exact ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _
    (g1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hr T Lc μ₀ hμ G)
    (g2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hr T Lc μ₀ hμ G)⟩

theorem dictionary_at_stage : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
      GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
        HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_two GlobalTheory.T.gridSquare_infinityExponent_gap_largeGrids GlobalTheory.T.towerStage_finitePlaces_unramified_or_split ?_
  intro D T Lc sc G μ₀ C x b hinf hram W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hsz := stage_sizes i j hp hq hrA hrA'
  have hrk : WW.rank = A.rank + A'.rank := hXi.rank.symm
  have e1 : ∀ τ, (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart τ = -X.rA.s τ := cart_frSgn_true_rigFr X.rA hXi.rigA
  have e1' : ∀ τ, (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart τ = X.rA'.s τ := cart_frSgn_false_rigFr X.rA' hXi.rigA'
  have e2 : ∀ τ, (rigFr X.rW hXi.rigW).cart τ = X.rW.s τ := cart_rigFr X.rW hXi.rigW
  refine ⟨rigFr X.rA hXi.rigA, rigFr X.rA' hXi.rigA', rigFr X.rW hXi.rigW, a, b, fun t => ⟨?_,
    fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    GlobalTheory.T.seesawTriple_firstFiniteDatum_riggedFrames X _ _ _ _ _ _ _ _ e1 e2 hXi t, GlobalTheory.T.seesawTriple_secondFiniteDatum_isFinite_rigging X _ _ _ _ _ _ _ _ e1' e2 hXi t, ?_, ?_⟩⟩
  · refine
      { hecA := (hXi.weil' t).hecS
        hecB := (hXi.weil t).hecS
        resA := (hXi.weil' t).resS
        resB := (hXi.weil t).resS
        rank := hrk
        even := by rw [hrk]; exact hsz.1
        sig := ⟨p, q, fun τ => ⟨hnA τ, hnA' τ, hnW τ⟩, hsz.2.1, hsz.2.2.1⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, ?_⟩
        ram := hram W i j p q A A' WW X ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ t }
    have h1 := (hab t τ).2.2
    have h2 : ((WW.rank : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast (hrk ▸ hsz.2.2.2)
    linarith
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn true (rigFr X.rA hXi.rigA)).cart = fun τ => -X.rA.s τ := funext e1
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA hXi.rigA).onb = X.rA.B := funext (onb_rigFr X.rA hXi.rigA)
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [f1, f2, f3, f4]
  · intro P g h
    have f1 : (GlobalTheory.SquareComm.frSgn false (rigFr X.rA' hXi.rigA')).cart = X.rA'.s := funext e1'
    have f2 : (rigFr X.rW hXi.rigW).cart = X.rW.s := funext e2
    have f3 : (rigFr X.rA' hXi.rigA').onb = X.rA'.B := funext (onb_rigFr X.rA' hXi.rigA')
    have f4 : (rigFr X.rW hXi.rigW).onb = X.rW.B := funext (onb_rigFr X.rW hXi.rigW)
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [f1, f2, f3, f4]
    rfl

end GlobalTheory.StageDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryTripleConditionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerStage_seesawDictionary_tripleConditions : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), ∀ t : T,
      GlobalTheory.SquareComm.IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧
      (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧
        HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧
      GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧
      (∀ P g h, thetaKO (X.ω t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧
      ∀ P g h, thetaKO (X.ω' t) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.StageDict.dictionary_at_stage | exact GlobalTheory.StageDict.dictionary_at_stage | (intros; apply GlobalTheory.StageDict.dictionary_at_stage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestRest
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.TopFlip.MeasW

theorem nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {t t' : T} {M M' : Vol G}
    (hM : M.Is t) (hM' : M'.Is t') (i j : Fin D.R.m) :
    M.ν (.grid (i + 1) (j + 1)) = M'.ν (.grid (i + 1) (j + 1)) :=
  GlobalTheory.FunObjModel.isAt_unique (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩) (hM'.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩)

theorem exists_ratio : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW G i j))), m.IsHaarMeasure →
      ∃ s₀ : NNReal, s₀ ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • m → s = s₀ := by
  intro D T L sc G μ₀ _ i j m hm
  by_cases h : ∃ (t : T) (M : Vol G) (s : NNReal), M.Is t ∧ M.ν (.grid (i + 1) (j + 1)) = s • m
  · obtain ⟨t₀, M₀, s₀, hM₀, e₀⟩ := h
    have hH := (hM₀.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund.1
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW G i j)
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (GA D (spW G i j))) := inferInstance
    have hK0 : m K ≠ 0 :=
      ((isOpen_interior.measure_pos m K.interior_nonempty).trans_le (measure_mono interior_subset)).ne'
    have hK1 : m K ≠ ⊤ := K.isCompact.measure_lt_top.ne
    refine ⟨s₀, ?_, fun t M hM s e => ?_⟩
    · rintro rfl
      rw [e₀, zero_smul] at hH
      exact (isOpen_univ.measure_pos (0 : Measure (GA D (spW G i j))) Set.univ_nonempty).ne' rfl
    · have e1 : s • m = s₀ • m := e.symm.trans ((nu_eq hM hM₀ i j).trans e₀)
      have e2 : (s : ENNReal) * m K = (s₀ : ENNReal) * m K := by
        have e3 := congrArg (fun μ : Measure (GA D (spW G i j)) => μ K) e1
        exact e3
      exact_mod_cast (ENNReal.mul_left_inj hK0 hK1).1 e2
  · exact ⟨1, one_ne_zero, fun t M hM s e => absurd ⟨t, M, s, hM, e⟩ h⟩

end GlobalTheory.TopFlip.MeasW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairModularTwistIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix

namespace GlobalTheory.BotRealInv

theorem substF_minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (H : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) (fun τ => (H τ)ᵀ) (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (H τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF (rfl : a = a) (rfl : d = d) T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  have one : ∀ (τ : D.what₂.Tau) (s : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) (fun τ => (H τ)ᵀ)
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (H τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_transpose ((MvPolynomial.C : ℂ →+* _).mapMatrix (H τ)), mul_comm,
      ← Matrix.det_mul]
    congr 1
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X,
      RingHom.mapMatrix_apply, Matrix.transpose_apply]
    rw [Finset.sum_eq_single (s i)]
    · simp only [Matrix.one_apply_eq, one_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [GlobalTheory.NormSum.minorPol, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  simp only [one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

theorem succ_mul_succ_sub_one_div_succ {G : Type*} [CommGroup G] (a e c : G) : a * e / (c * e) = a / c := mul_div_mul_right_eq_div _ _ _

end GlobalTheory.BotRealInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGrids
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGrids
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

theorem bottom_infExp_gap : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro _ i j
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := by
    show (G.V (.grid (i : ℕ) (j : ℕ))).rank % 2 = _
    rw [(node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).rank]
    rfl
  refine ⟨fun τ => -(D.hc τ).e ⟨j, j.2⟩ + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2),
    fun τ => (cen D 1 τ (D.R.m - i) : ℚ) + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2), fun t τ => ⟨?_, ?_, ?_⟩⟩
  · have h := GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, hε] at h
    exact h
  · have h := GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps] at h
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps, hε] at h
    exact h
  · have key := GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen (D := D) 1 τ i j i.2 j.2
    have hle : SqNum.botBig D i j + SqNum.botSmall D i j ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
      simp only [SqNum.botBig, SqNum.botSmall]
      omega
    have hle' : ((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) ≤ ((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
      exact_mod_cast hle
    push_cast at key hle' ⊢
    linarith

end GlobalTheory.BotDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGridsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ) := by
  first | exact @GlobalTheory.BotDict.bottom_infExp_gap | exact GlobalTheory.BotDict.bottom_infExp_gap | (intros; apply GlobalTheory.BotDict.bottom_infExp_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SumSize GlobalTheory.SumCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CosCount

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem cosFam_apply_eq_of_mem_supp {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β β' : CosFam G t} (hβ : β ∈ S.supp t Φ) (hβ' : β' ∈ S.supp t Φ) :
    β ⟨P, hl⟩ = β' ⟨P, hl⟩ := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO G t P hj)
  have hk : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
  have hb := hβ ⟨P, hl⟩
  have hb2 := hβ' ⟨P, hl⟩
  rw [hk] at hb hb2
  exact funext fun i => (hO _ hb i).trans (hO _ hb2 i).symm

theorem supp_subsingleton {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (hQ : L.Q t = ∅) : (S.supp t Φ).Subsingleton := by
  classical
  intro β hβ β' hβ'
  have hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP; rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  funext ⟨P, hl⟩
  have hP : P ∈ G.pl.W0 := by
    rcases Finset.mem_union.1 hl with h | h
    · exact h
    · rw [hQ] at h; exact absurd h (Finset.notMem_empty _)
  exact cosFam_apply_eq_of_mem_supp hL S t Φ hde hc hP hl hβ hβ'

end GlobalTheory.CosCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToP
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

theorem kerPow_one {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) :
    KerPow f 1 k (1 : ptOver k k ⟶ A.X) := by
  refine ⟨⟨MonObj.one_comp _, one_pow _⟩, ?_⟩
  intro R _ _ x _ hx
  rw [pow_one] at hx
  subst hx
  refine ⟨Algebra.ofId k R, ?_, fun ψ _ => Subsingleton.elim _ _⟩
  change (spOver (Algebra.ofId k R) ≫ (1 : ptOver k k ⟶ A.X)).left = (1 : ptOver k R ⟶ A.X).left
  rw [MonObj.comp_one]

theorem exists_kerPow_primePow {k : Type} [Field k] {A B : AbVar k} (f : A ⟶ B) (q e : ℕ) (hq : q.Prime) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f (q ^ e) H i ∧ ∃ j : ℕ, Module.finrank k H = q ^ j := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨G, -, ⟨tA⟩⟩ := GlobalTheory.AVTower.exists_tower q k A
  obtain ⟨G', -, ⟨tB⟩⟩ := GlobalTheory.AVTower.exists_tower q k B
  refine ⟨_, inferInstance, inferInstance, kerPt tA tB f e, kerPow_kerPt tA tB f e, ?_⟩
  exact (Nat.dvd_prime_pow hq).1 (finrank_quot_kerIdeal_dvd (tA.map tB f.hom) e) |>.imp fun _ h => h.2

theorem exists_kerPow_not_dvd : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B)
    (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  intro p hp k _ A B f m
  have hpp : p.Prime := hp.out
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow q n hq hn =>
    intro _ hdvd
    have hqp : q ≠ p := by
      rintro rfl
      exact hdvd (dvd_pow_self q hn.ne')
    obtain ⟨H, _, _, i, hi, j, hj⟩ := exists_kerPow_primePow f q n hq
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hj]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1 (hpp.dvd_of_dvd_pow h)).symm
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    refine ⟨k, inferInstance, inferInstance, 1, kerPow_one f, ?_⟩
    rw [Module.finrank_self]
    exact hpp.not_dvd_one
  | coprime a b ha hb hab iha ihb =>
    intro _ hdvd
    have hpa : ¬ p ∣ a := fun h => hdvd (h.mul_right b)
    have hpb : ¬ p ∣ b := fun h => hdvd (h.mul_left a)
    obtain ⟨H₁, _, _, i₁, hi₁, h₁⟩ := iha (by omega) hpa
    obtain ⟨H₂, _, _, i₂, hi₂, h₂⟩ := ihb (by omega) hpb
    obtain ⟨H, _, _, i, hi, hH⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f a b hab H₁ i₁ H₂ i₂ hi₁ hi₂
    refine ⟨H, inferInstance, inferInstance, i, hi, ?_⟩
    rw [hH]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
    · exact h₁ h
    · exact h₂ h

end GlobalTheory.AV.KerPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelPartOrderPrimeToPStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelPart_order_prime_to_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (f : A ⟶ B) (m : ℕ), 0 < m → ¬ p ∣ m → ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X), KerPow f m H i ∧ ¬ p ∣ Module.finrank k H := by
  first | exact @GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | exact GlobalTheory.AV.KerPart.exists_kerPow_not_dvd | (intros; apply GlobalTheory.AV.KerPart.exists_kerPow_not_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAtFittedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMatrixDescendsOfRationalOnTuple
namespace GlobalTheory

theorem complex_matrix_descends_of_rational_on_tuple : ∀ {K : Type} [Field K] (σ : K →+* ℂ) {T : Type} (n D : ℕ) (dQ nV : T → ℕ) (ι : ∀ t, Matrix (Fin D) (Fin (dQ t)) K) (Pq : ∀ t, Matrix (Fin (dQ t)) (Fin (nV t)) K) (V : ∀ t, Matrix (Fin n) (Fin (nV t)) K) (r : T → K) (U : Set T) (t0 : T) (Ψc : Matrix (Fin n) (Fin D) ℂ), t0 ∈ U → Function.Bijective (ι t0).mulVec → Function.Surjective (Pq t0).mulVec → (∀ t ∈ U, Ψc * (ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ) → (∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ.map σ = Ψc ∧ ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t) ∧ (Function.Injective Ψc.mulVec → r t0 = 1 → LinearMap.ker (V t0).mulVecLin = LinearMap.ker (Pq t0).mulVecLin) := by
  intro K _ σ T n D dQ nV ι Pq V r U t0 Ψc ht0 hι hP h
  have hσ : Function.Injective σ := σ.injective
  have hsurj : Function.Surjective (ι t0 * Pq t0).mulVec := by
    intro y
    obtain ⟨x, rfl⟩ := hι.2 y
    obtain ⟨z, rfl⟩ := hP x
    exact ⟨z, (Matrix.mulVec_mulVec _ _ _).symm⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ = ((r t0)⁻¹ • V t0) * R := ⟨_, rfl⟩
  have hΨc : Ψ.map σ = Ψc := by
    calc Ψ.map σ = ((r t0)⁻¹ • V t0).map σ * R.map σ := by rw [hΨ, Matrix.map_mul]
      _ = Ψc * (ι t0 * Pq t0).map σ * R.map σ := by rw [h t0 ht0]
      _ = Ψc * ((ι t0 * Pq t0) * R).map σ := by rw [Matrix.map_mul (M := R), Matrix.mul_assoc]
      _ = Ψc := by rw [hR, Matrix.map_one σ σ.map_zero σ.map_one, Matrix.mul_one]
  have hall : ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t := by
    intro t ht
    apply Matrix.map_injective hσ
    show (Ψ * ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ
    rw [Matrix.mul_assoc, Matrix.map_mul, hΨc, h t ht]
  refine ⟨⟨Ψ, hΨc, hall⟩, fun hinj hr => ?_⟩
  have key : Ψ * ι t0 * Pq t0 = V t0 := by
    rw [hall t0 ht0, hr, inv_one, one_smul]
  have hΨinj : Function.Injective Ψ.mulVec := by
    intro x y hxy
    have hc : Ψc.mulVec (fun j => σ (x j)) = Ψc.mulVec (fun j => σ (y j)) := by
      funext i
      change (Ψc).mulVec (σ ∘ x) i = (Ψc).mulVec (σ ∘ y) i
      rw [← hΨc, ← RingHom.map_mulVec, ← RingHom.map_mulVec, hxy]
    funext j
    exact hσ (congrFun (hinj hc) j)
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    have h1 : (ι t0).mulVec ((Pq t0).mulVec v) = 0 := hΨinj (hv.trans (Matrix.mulVec_zero Ψ).symm)
    exact hι.1 (h1.trans (Matrix.mulVec_zero (ι t0)).symm)
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end GlobalTheory
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem out_sum_tw {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {n : ℕ}
    (f : E →ₗ[ℂ] ℂ) (φ : (Fin n → ℂ) →ₗ[ℂ] Tw s E) (z : Fin n → ℂ) :
    f (Tw.out (φ z)) = ∑ k, cj s (z k) * f (Tw.out (φ (Pi.single k 1))) := by
  let o : Tw s E →+ E := ⟨⟨Tw.out, rfl⟩, Tw.out_add⟩
  have e : z = ∑ k, z k • (Pi.single k 1 : Fin n → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j; by_cases hj : j = k <;> simp [hj]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [e, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show Tw.out (∑ k, φ (z k • Pi.single k 1)) = ∑ k, Tw.out (φ (z k • (Pi.single k 1 : Fin n → ℂ))) from
    map_sum o (fun k => φ (z k • (Pi.single k 1 : Fin n → ℂ))) Finset.univ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Tw.out_smul, map_smul, smul_eq_mul]

theorem twist_conj_base_embedding_eq (p : PtAt ex Csz) (a : D.what₂.LL) :
    cj (twAt D.what₂.embLL p.P.A3.A.v0) (p.P.A3.fam3.base3.v0.embedding a) = D.what₂.embLL a := by
  rw [show p.P.A3.fam3.base3.v0 = p.P.A3.A.v0 from rfl, emb_eq D.what₂.embLL p.P.A3.A.v0 a, cj_cj, sgAt_mk _ p.R.hv0]

theorem mul_eq_one_of_covolume_identity (κ zt z0 ct c0 v : ℂ) (hκ : κ ≠ 0) (hzt : zt ≠ 0) (hz0 : z0 ≠ 0) (hct : ct ≠ 0) (hc0 : c0 ≠ 0) :
    κ⁻¹ * z0 * c0 * (κ * v / (zt * ct)) = (zt / z0 * (ct / c0))⁻¹ * v := by
  field_simp


end GlobalTheory.BigTop.Fun
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRing
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_any_ring : PrimitiveExtendedDegTwoVanish := by
  apply GlobalTheory.T.primitive_degree_two_extension
  apply GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish
  intro R _ A _ g hA hs
  exact ⟨(GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).1,
    (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).2.1⟩

end GlobalTheory.Obs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRingStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_degree_two_any_ring : PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_any_ring | exact GlobalTheory.Obs.primE2_any_ring | (intros; apply GlobalTheory.Obs.primE2_any_ring <;> assumption)
end
end
