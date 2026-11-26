module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateActionUniformisationCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateActionUniformisationCharacters
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem GlobalTheory.USep.conjAct_endU_chars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (a : 𝓞 E), ∃ En : GlobalTheory.UT.EndU P.U.toUnifPre, En.aA = (letI := H.starRing; P.oA.act (H.bar a)) ∧ ∀ x, En.h x = a • x := by
  intro E _ _ _ H V _ _ _ hV t P a
  letI := H.starRing
  haveI : CharZero V := hV.2.2.2
  obtain ⟨En, -, hA, -, hh, -⟩ := GlobalTheory.Mum.EFix.endU_of_oLinear GlobalTheory.firstFiveLaws V (maximalIdeal V)
    ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩ P.D P.A t.G t.semi P.U (𝓞 E) P.oD P.oA t.act.toRingAct P.lin (H.bar a)
  refine ⟨En, hA, fun x => ?_⟩
  rw [hh]
  exact congrArg (· • x) (star_star a)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateActionUniformisationCharactersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateAction_uniformisation_characters : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (a : 𝓞 E), ∃ En : GlobalTheory.UT.EndU P.U.toUnifPre, En.aA = (letI := H.starRing; P.oA.act (H.bar a)) ∧ ∀ x, En.h x = a • x := by
  first | exact @GlobalTheory.USep.conjAct_endU_chars | exact GlobalTheory.USep.conjAct_endU_chars | (intros; apply GlobalTheory.USep.conjAct_endU_chars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryUniformisationBaseChangeInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryUniformisationBaseChangeInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepBC


set_option maxHeartbeats 1600000 in
theorem exists_pelUnif_baseChange_of_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → ∃ (t₁ : SAB H (Sp V₁)) (P₁ : PELUnif (maximalIdeal V₁) t₁) (p : IsPullDeg ρ P.D.toPre P₁.D.toPre), GenOf Xo c (spMap fK ≫ y) t₁ ∧ (∀ (a : 𝓞 E) x, p.xe (a • x) = a • p.xe x) ∧ ∀ x r, Formalism.L2.Pj.PsiCoord P.D.toPre (p.xe x) r → ∃ w : V₁ˣ, Formalism.L2.Pj.PsiCoord P₁.D.toPre x (w * ρ r) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV t y P hG V₁ _ _ _ ρ fK hV₁ hρ hl hfK
  have hR : GlobalTheory.Mum.Base V := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  have hR₁ : GlobalTheory.Mum.Base V₁ := ⟨⟨hV₁.1, inferInstance, hV₁.2.1, hV₁.2.2.1⟩, hV₁.2.2.2⟩
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨Wo, hWo, ⟨hψ⟩⟩ := h5.psiOnExists V (maximalIdeal V) hR.1 P.D
  let WS : Set (PrimeSpectrum V) := (Wo : Set (Sp V))
  have hWS : IsOpen WS := Wo.isOpen
  have hbot : (⊥ : PrimeSpectrum V) ∈ WS := by
    have := hWo
    rw [genericPoint_eq_bot_of_affine] at this
    exact this
  obtain ⟨_, ⟨f, rfl⟩, hf, hfW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hWS
  have hf0 : f ≠ 0 := by
    intro e
    apply hf
    rw [e]
    show (0 : V) ∈ (⊥ : PrimeSpectrum V).asIdeal
    exact Ideal.zero_mem _
  have hψW : ∀ x, PsiUnitOn P.D.toPre x (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
    intro x j U hU hUW
    exact GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn V P.D.toPre Wo hψ x j U hU (hUW.trans hfW)
  have hρf : ρ f ≠ 0 := fun e => hf0 (hρ (e.trans (map_zero ρ).symm))
  obtain ⟨t₁, P₁, p, ⟨m₀⟩, hlin, -⟩ := GlobalTheory.LocalPull.exists_pelUnif_pull V V₁ hR hR₁ t P ρ hl f hρf hψW
  refine ⟨t₁, P₁, p, ?_, hlin, fun x r hr => GlobalTheory.PelCoordPull.psiCoord_pull p x r hr⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hG
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨e⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) e⟩
  have sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
      ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, semiPull f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
    have h := isGrpPullback_pullback t.G f
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
        pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
        pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
      Over.OverMorphism.ext (by
        show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP, cub, sym, adj, prim, n, -⟩ := sabPull CubePf.cubePull (jK V₁) t₁
  let tK₁ : SAB H (Sp (FractionRing V₁)) := ⟨(Over.pullback (jK V₁)).obj t₁.G, semiPull _ t₁.G t₁.semi,
    OAct.pullback _ t₁.G t₁.act, PP, cub, sym, adj, prim⟩
  have n' : SABMap tK₁ t₁ (jK V₁) := n
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ t t₁ tK₁ _ _ m₀ n'
  have sq : jK V₁ ≫ spMap ρ = spMap fK ≫ jK V := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact (hfK a).symm
  rw [sq] at b
  obtain ⟨c', -⟩ := sabCancel pullCubCancel E H _ _ _ t tK tK₁ _ _ m₁ b
  obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tK tK₁ _ _ m₂ c'
  refine ⟨tK₁, ⟨n'⟩, ⟨?_⟩⟩
  rw [Category.assoc]
  exact d

end GlobalTheory.USepBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryUniformisationBaseChangeInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryUniformisation_baseChange_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → ∃ (t₁ : SAB H (Sp V₁)) (P₁ : PELUnif (maximalIdeal V₁) t₁) (p : IsPullDeg ρ P.D.toPre P₁.D.toPre), GenOf Xo c (spMap fK ≫ y) t₁ ∧ (∀ (a : 𝓞 E) x, p.xe (a • x) = a • p.xe x) ∧ ∀ x r, Formalism.L2.Pj.PsiCoord P.D.toPre (p.xe x) r → ∃ w : V₁ˣ, Formalism.L2.Pj.PsiCoord P₁.D.toPre x (w * ρ r) := by
  first | exact @GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective | exact GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective | (intros; apply GlobalTheory.USepBC.exists_pelUnif_baseChange_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingValuePointLiesOverUnitaryModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingValuePointLiesOverUnitaryModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep

theorem valPt_lies_over_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ Xo.XF c), GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = y ≫ C.i → ∃ (yK : X₁.S.R →+* FractionRing V₁) (x' : Sp (FractionRing V₁) ⟶ Sp (ratHull X₁.S.R)), (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ x' ≫ spMap (toRat X₁.S.R) = spMap yK ∧ x' ≫ u = y := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL z₁ V₁ _ _ _ ev y hreg hy
  set yw := jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyw
  set w := yw (IsLocalRing.closedPoint (FractionRing V₁)) with hw
  have hle : X₁.S.R ≤ X₁.M.O w := fun a ha => hreg a ha

  have hπw : π w = C.i (y (IsLocalRing.closedPoint (FractionRing V₁))) := by
    have h1 : yw ≫ π = y ≫ C.i := by simpa only [hyw, Category.assoc] using hy
    have h2 := congrArg (fun f => f (IsLocalRing.closedPoint (FractionRing V₁))) h1
    exact h2
  have hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X₁.M.O w) := fun n hn => by
    rw [← map_intCast (X₁.M.stalkEquiv w) n, MulEquiv.isUnit_map, ← map_intCast (π.stalkMap w).hom n,
      isUnit_map_iff, hπw, ← isUnit_map_iff (C.i.stalkMap _).hom, map_intCast]
    have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
    have h' := ((h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
      ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) (y (IsLocalRing.closedPoint (FractionRing V₁))))
        trivial).hom).map ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F).stalkMap _).hom
    rwa [map_intCast, map_intCast, map_intCast] at h'
  have hle' : ratHull X₁.S.R ≤ X₁.M.O w := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 (hc n hn)
    have e : ((n : X₁.M.O w) : X₁.Ω₁) = n := by simp
    rw [e] at h1 h2
    have := mul_mem h2 (hle h)
    rwa [inv_mul_cancel_left₀ h1] at this
  have hsp : yw (IsLocalRing.closedPoint (FractionRing V₁)) ⤳ w := specializes_rfl
  let ψ : ratHull X₁.S.R →+* X₁.M.Z.presheaf.stalk w :=
    (X₁.M.stalkEquiv w).symm.toRingHom.comp (Subalgebra.inclusion hle').toRingHom
  let φ : X₁.M.Z.presheaf.stalk w →+* FractionRing V₁ := (X₁.M.Z.presheaf.stalkSpecializes hsp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of (FractionRing V₁)) yw).hom
  have hK : (RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom =
      (φ.comp ψ).comp (toRat X₁.S.R) :=
    RingHom.ext fun a => (RatModel.valLoc_eq_val yw hsp (Subalgebra.inclusion hle a)).symm
  refine ⟨(RatModel.valHom yw w (RatModel.range_eq_singleton yw _)).comp (Subalgebra.inclusion hle).toRingHom,
    spMap (φ.comp ψ), fun a => rfl, ?_, ?_⟩
  · rw [hK]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI := C.isPreimmersion_i
  haveI : IsProper C.z := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  haveI : C.Z.IsSeparated := by
    constructor
    rw [← terminal.comp_from C.z]
    infer_instance
  haveI : IsDominant (spMap (X₁.M.stalkHom w)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (X₁.M.stalkHom w))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (X₁.M.stalkHom_injective w)]
    exact bot_le
  have hfs : ∀ {B : Type} [CommRing B] [IsLocalRing B] (q : Sp B ⟶ X₁.M.Z) (h : q (IsLocalRing.closedPoint B) ⤳ w),
      spMap (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of B) q).hom ≫
        X₁.M.Z.fromSpecStalk w = q := by
    intro B _ _ q h
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of B) q
  have e1 : spMap (X₁.M.stalkHom w) ≫ spMap ψ = spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => congrArg Subtype.val ((X₁.M.stalkEquiv w).apply_symm_apply (Subalgebra.inclusion hle' a))
  have e2 : spMap (X₁.M.stalkHom w) ≫ X₁.M.Z.fromSpecStalk w = X₁.M.pt :=
    hfs X₁.M.pt (X₁.M.pt_specializes _ w)
  have hab : spMap ψ ≫ u ≫ C.i = X₁.M.Z.fromSpecStalk w ≫ π := by
    refine ext_of_isDominant (spMap (X₁.M.stalkHom w)) ?_
    rw [reassoc_of% e1, reassoc_of% e2, hL.2.2.2]
  have e3 : spMap φ ≫ X₁.M.Z.fromSpecStalk w = yw := hfs yw hsp
  rw [← cancel_mono C.i, Category.assoc]
  rw [show spMap (φ.comp ψ) = spMap φ ≫ spMap ψ by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp], Category.assoc, hab, reassoc_of% e3, ← hy]
  simp only [hyw, Category.assoc]

end GlobalTheory.GSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRingValuePointLiesOverUnitaryModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRing_valuePoint_lies_over_unitaryModuli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (y : Sp (FractionRing V₁) ⟶ Xo.XF c), GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = y ≫ C.i → ∃ (yK : X₁.S.R →+* FractionRing V₁) (x' : Sp (FractionRing V₁) ⟶ Sp (ratHull X₁.S.R)), (∀ a, yK a = X₁.M.val (jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) ∧ x' ≫ spMap (toRat X₁.S.R) = spMap yK ∧ x' ≫ u = y := by
  first | exact @GlobalTheory.GSep.valPt_lies_over_unitary | exact GlobalTheory.GSep.valPt_lies_over_unitary | (intros; apply GlobalTheory.GSep.valPt_lies_over_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUniformisationGenericFibreIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUniformisationGenericFibreIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USepGen

theorem genfib_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (yK : X₁.S.R →+* FractionRing V) (x' : Sp (FractionRing V) ⟶ Sp (ratHull X₁.S.R)), x' ≫ spMap (toRat X₁.S.R) = spMap yK → GenOf Xo c (x' ≫ u) t → ∃ φ : P.A.A.left ⟶ X₁.ρ.P.A.left, IsGrpPullback P.A.A X₁.ρ.P.A (spMap yK) φ ∧ LBIso P.A.L (X₁.ρ.P.L.pull φ) ∧ ∀ a, (letI := H.starRing; (P.oA.act (H.bar a)).left) ≫ φ = φ ≫ (act a).left := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL V _ _ _ _ t P yK x' hx' hgen
  obtain ⟨-, ⟨G, iG, α, β, hα, hβ, hLab, hf⟩, -, -⟩ := hL
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hgen
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  have gpA : IsGrpPullback P.A.A t.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK V))).congr
      (Category.id_comp _) rfl
  have w₁ : (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) ≫ t.G.hom = (P.A.A.hom ≫ 𝟙 _) ≫ jK V := by
    rw [gpA.1.w, Category.comp_id]
  let κ : P.A.A.left ⟶ tK.G.left := m₁.cart.1.lift _ _ w₁
  have hκ₁ : κ ≫ m₁.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) := m₁.cart.1.lift_fst _ _ _
  have hκ₂ : κ ≫ tK.G.hom = P.A.A.hom ≫ 𝟙 _ := m₁.cart.1.lift_snd _ _ _
  have gκ : IsGrpPullback P.A.A tK.G (𝟙 _) κ :=
    m₁.cart.cancel (gpA.congr (Category.id_comp _).symm hκ₁.symm) hκ₂
  have w₂ : m₂.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ x') ≫ u ≫ pullback.fst _ _ := by
    rw [m₂.cart.1.w]; simp only [Category.assoc]
  let lam : tK.G.left ⟶ G.left := hβ.1.lift _ _ w₂
  have hl₁ : lam ≫ β = m₂.φ := hβ.1.lift_fst _ _ _
  have hl₂ : lam ≫ G.hom = tK.G.hom ≫ x' := hβ.1.lift_snd _ _ _
  have gl : IsGrpPullback tK.G G x' lam :=
    hβ.cancel (m₂.cart.congr (Category.assoc _ _ _) hl₁.symm) hl₂
  refine ⟨κ ≫ lam ≫ α, (gκ.comp (gl.comp hα)).congr (by rw [Category.id_comp, hx']) rfl, ?_, ?_⟩
  · have hA := P.A.isLB
    have hT := t.PP.isLB
    have hK := tK.PP.isLB
    have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    obtain ⟨w, hw⟩ := P.U.ext
    have hc : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id]; rfl
    have e₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V))) :=
      GlobalTheory.GenSpread.lbIso_pull_comp P.U.gen.inv.left hc.symm rfl ⟨w, hw⟩
    rw [P.bundle, ← hκ₁] at e₁
    have e₀ : LBIso P.A.L (P.A.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id hA
    obtain ⟨w₁, hw₁, -⟩ := m₁.lin
    obtain ⟨w₂, hw₂, -⟩ := m₂.lin
    have e₂ : LBIso (tK.PP.L.pull κ) (t.PP.L.pull (κ ≫ m₁.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₁, hw₁⟩ κ rfl
    have e₃ : LBIso (tK.PP.L.pull κ) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₂, hw₂⟩ κ rfl
    have e₄ : LBIso (X₁.ρ.P.L.pull (κ ≫ lam ≫ α)) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp (κ ≫ lam) (Category.assoc _ _ _).symm
        (by rw [← hl₁, Category.assoc]) hLab
    refine LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) e₀ ?_
    refine LBIso.trans (pull_isLB hA _) (pull_isLB hT _) (pull_isLB hP _) e₁ ?_
    refine LBIso.trans (pull_isLB hT _) (pull_isLB hK _) (pull_isLB hP _) e₂.symm ?_
    refine LBIso.trans (pull_isLB hK _) (pull_isLB hU _) (pull_isLB hP _) e₃ ?_
    exact e₄.symm
  · intro a
    obtain ⟨f, hfα, hfβ⟩ := hf a
    letI := H.starRing
    have hext := P.lin.ext (H.bar a)
    have hg : (P.oA.act (H.bar a)).left ≫ P.U.gen.inv.left =
        P.U.gen.inv.left ≫ ((Over.pullback (jK V)).map (t.act.act (H.bar a))).left := by
      have : P.oA.act (H.bar a) ≫ P.U.gen.inv =
          P.U.gen.inv ≫ (Over.pullback (jK V)).map (t.act.act (H.bar a)) := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← hext, Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
      rw [← Over.comp_left, this, Over.comp_left]
    have s₁ : (P.oA.act (H.bar a)).left ≫ κ = κ ≫ (tK.act.act (H.bar a)).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, hκ₁, Category.assoc, m₁.act, ← Category.assoc κ, hκ₁, ← Category.assoc, hg,
          Category.assoc, Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, hκ₂, Category.assoc, Over.w, hκ₂, ← Category.assoc, Over.w]
    have s₂ : (tK.act.act (H.bar a)).left ≫ lam = lam ≫ f.left := by
      apply hβ.1.hom_ext
      · simp only [Category.assoc, hfβ]
        rw [hl₁, ← Category.assoc lam β, hl₁]
        exact m₂.act _
      · rw [Category.assoc, hl₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hl₂]
    rw [← Category.assoc, s₁, Category.assoc, ← Category.assoc _ lam, s₂, Category.assoc, hfα]
    simp only [Category.assoc]

end GlobalTheory.USepGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUniformisationGenericFibreIsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUniformisation_genericFibre_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (yK : X₁.S.R →+* FractionRing V) (x' : Sp (FractionRing V) ⟶ Sp (ratHull X₁.S.R)), x' ≫ spMap (toRat X₁.S.R) = spMap yK → GenOf Xo c (x' ≫ u) t → ∃ φ : P.A.A.left ⟶ X₁.ρ.P.A.left, IsGrpPullback P.A.A X₁.ρ.P.A (spMap yK) φ ∧ LBIso P.A.L (X₁.ρ.P.L.pull φ) ∧ ∀ a, (letI := H.starRing; (P.oA.act (H.bar a)).left) ≫ φ = φ ≫ (act a).left := by
  first | exact @GlobalTheory.USepGen.genfib_pull | exact GlobalTheory.USepGen.genfib_pull | (intros; apply GlobalTheory.USepGen.genfib_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberOfUnitaryMonomialUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

theorem member_of_monomial_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (m : ℕ) (s : Fin m → V) (β : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre s β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁) (r : Fin m → V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → (∀ k, r k ^ 2 = ρ (s k)) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ y ≫ C.i → ∃ (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev (Fin 1 → P.D.toPre.X) (mono !![(1 : ℤ)] r β) (fun a mu => a • mu)) (p : IsPullDeg ρ P.D.toPre 𝔪.D.toPre), ∀ mu, p.xe (𝔪.e₈ mu) = mu 0 := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ act u π hL z₁ V _ _ _ hV t y P hG m s β hmono V₁ _ _ _ ρ fK r hV₁ hinj hloc hfK hr ev hev hreg hpt
  obtain ⟨t₁, P₁, p, hG₁, hlin, hpsi⟩ := GlobalTheory.T.exists_unitaryUniformisation_baseChange_injective E H Dw l Xo c V hV t y P hG V₁ ρ fK hV₁ hinj hloc hfK
  obtain ⟨yK, x', hyK, hx', hx'u⟩ := GlobalTheory.GSep.valPt_lies_over_unitary E H Dw hpq l Xo c C X₁ act u π hL z₁ V₁ ev (spMap fK ≫ y) hreg
    (hpt.trans (Category.assoc _ _ _).symm)
  obtain ⟨φ, hcart, hwl, hact⟩ := GlobalTheory.T.unitaryUniformisation_genericFibre_isPullback E H Dw hpq l Xo c C X₁ act u π hL V₁ hV₁ t₁ P₁ yK x' hx'
    (by rw [hx'u]; exact hG₁)
  obtain ⟨wl, hwl⟩ := hwl
  let e₈ : (Fin 1 → P.D.toPre.X) ≃+ P₁.D.toPre.X := (AddEquiv.piUnique fun _ : Fin 1 => P.D.toPre.X).trans p.xe.symm
  have he₈ : ∀ mu, p.xe (e₈ mu) = mu 0 := fun mu => by simp [e₈]
  refine ⟨{
    cn := hV₁
    loc := hev
    reg := hreg
    yK := yK
    yK_eq := hyK
    D := P₁.D
    e₈ := e₈
    G := t₁.G
    semi := t₁.semi
    A := P₁.A
    U := P₁.U
    φ := φ
    cart := hcart
    wl := wl
    wl_gen := hwl
    equiv := fun a => ?_
    psi := fun mu => ?_ }, p, he₈⟩
  · obtain ⟨En, hEn, hh⟩ := GlobalTheory.USep.conjAct_endU_chars E H V₁ hV₁ t₁ P₁ a
    refine ⟨En, by rw [hEn]; exact hact a, fun mu => ?_⟩
    rw [hh]
    apply p.xe.injective
    rw [hlin, he₈, he₈]
    rfl
  · obtain ⟨u₀, n, hn, hc⟩ := hmono (mu 0)
    rw [← he₈ mu] at hc
    obtain ⟨w, hw⟩ := hpsi _ _ hc
    refine ⟨w * Units.map ρ.toMonoidHom u₀, ?_⟩
    have hmo : mono !![(1 : ℤ)] r β mu = ρ (∏ i, s i ^ n i) := by
      simp only [mono, qW, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val', _root_.one_mul, map_prod, map_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hn i, ← hr i, ← pow_mul]
      congr 1
    rw [hmo]
    have hu : (↑(w * Units.map ρ.toMonoidHom u₀) : V₁) * ρ (∏ i, s i ^ n i) = ↑w * ρ (↑u₀ * ∏ i, s i ^ n i) := by
      rw [map_mul, Units.val_mul, Units.coe_map, _root_.mul_assoc]; rfl
    rw [hu]
    exact hw

end GlobalTheory.USep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberOfUnitaryMonomialUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_of_unitary_monomial_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (z₁ : X₁.M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (m : ℕ) (s : Fin m → V) (β : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre s β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁) (r : Fin m → V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → (∀ k, r k ^ 2 = ρ (s k)) → ∀ ev : X₁.M.Z.presheaf.stalk z₁ →+* V₁, IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → jK V₁ ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ π = spMap fK ≫ y ≫ C.i → ∃ (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev (Fin 1 → P.D.toPre.X) (mono !![(1 : ℤ)] r β) (fun a mu => a • mu)) (p : IsPullDeg ρ P.D.toPre 𝔪.D.toPre), ∀ mu, p.xe (𝔪.e₈ mu) = mu 0 := by
  first | exact @GlobalTheory.USep.member_of_monomial_unif | exact GlobalTheory.USep.member_of_monomial_unif | (intros; apply GlobalTheory.USep.member_of_monomial_unif <;> assumption)
end
