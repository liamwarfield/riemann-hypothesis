module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsGrpPullbackOfEqId
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.SelfCmp

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} (hf : f = 𝟙 S) :
    IsGrpPullback G G f (𝟙 G.left) := by
  subst hf
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.LN.SelfCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletionUnif
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfIsGrpPullbackFst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isMonHom_of_isGrpPullback_fst {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    (bc : G' ≅ (Over.pullback s).obj G) (h : IsGrpPullback G' G s (bc.hom.left ≫ pullback.fst G.hom s)) :
    IsMonHom bc.hom := by
  obtain ⟨e, me, he⟩ := grpPullback_iso h (isGrpPullback_pullback G s)
  have : e.hom = bc.hom := Over.OverMorphism.ext (pullback.hom_ext he ((Over.w e.hom).trans (Over.w bc.hom).symm))
  exact this ▸ me

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory.UPoinc.TraitCompare

theorem exists_trait_lattice_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ (x : Y.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : Y.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsSemiAbelian G → IsGrpPullback G out.G (spMap j ≫ Y.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ ρT : D.toPre.X ≃+ T.P.D.toPre.X, (∀ y s, PsiCoord D.toPre y s → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (ψ s ^ 2) (T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r _hOver _hpt f _hf habl hT x R _ _ _ j hR _hj G _ _ gm hG hgm D A U hLB
    hPsi m hm T ψ hψ hTy
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hTV : GlobalTheory.Mum.Base T.V := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR T.cdvr, inferInstance⟩
  have hξT : spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x = spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [spMap_comp, Category.assoc]
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := by
    simp [spMap]
  obtain ⟨tW, mW, PW, e, he⟩ := GlobalTheory.UPoinc.TraitPull.exists_pull_unif E H Dw l Xo c T T.V hTV inferInstance (RingHom.id T.V)
    (fun _ _ h => h) inferInstance
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T _ hTy
  have hβ' : IsGrpPullback tW.G out.G (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) (mW.φ ≫ βT) :=
    (mW.cart.comp hβT).congr (by rw [hid, Category.id_comp, hξT]) rfl
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap ψ) ≫ (spMap j ≫ Y.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap ψ) w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap ψ := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap ψ) β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (LB.isLB_pull out.L.isLB _) (LB.isLB_pull U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (LB.isLB_pull T.t.PP.isLB _) (LB.isLB_pull out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm

  have hab : ∀ z, (spMap j ≫ Y.Z.fromSpecStalk x) z ∈ abLocus out.G ↔ z ∈ abLocus G :=
    abLocus_pullback abLocusOne out.semi hgm.1
  have hTy' : jK T.V ≫ (spMap ψ ≫ (spMap j ≫ Y.Z.fromSpecStalk x)) ≫ r = T.y ≫ C.i := by
    rw [← hξT]; exact hTy
  have hgen : spMap ψ (genericPoint (Sp T.V)) ∈
      (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    show _ ∈ abLocus G
    rw [← hab]
    apply habl
    let pt : Sp (FractionRing T.V) := ⟨⊥, Ideal.isPrime_bot⟩
    have hpt : jK T.V pt = genericPoint (Sp T.V) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun s => ?_)
      change algebraMap T.V (FractionRing T.V) s ∈ (⊥ : Ideal (FractionRing T.V)) ↔ s ∈ (⊥ : Ideal T.V)
      rw [Ideal.mem_bot, Ideal.mem_bot, IsFractionRing.to_map_eq_zero_iff]
    rw [← hpt]
    exact ⟨T.y pt, (congrArg (fun g : Sp (FractionRing T.V) ⟶ C.Z => g pt) hTy').symm⟩

  have hPsi' : ∀ y, PsiUnitOn D.toPre y (⟨abLocus G, GlobalTheory.AbLocusOpen.isOpen_abLocus_local G hG⟩ : (Sp R).Opens) := by
    intro y
    have hs : (⇑(spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G) = abLocus G := Set.ext hab
    have := hPsi y
    rw [hs] at this
    exact this

  let bc : tW.G ≅ (Over.pullback (specOf ψ)).obj G :=
    Over.isoMk hβ.1.isoPullback (by simp)
  have hbcβ : β = bc.hom.left ≫ pullback.fst G.hom (specOf ψ) := by
    simp [bc]
  have hbc : IsMonHom bc.hom := GlobalTheory.Mum.isMonHom_of_isGrpPullback_fst bc (hβ.congr rfl hbcβ)
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U T.V hTV.1 ψ hψ _ hPsi' hgen tW.G bc hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U T.V hTV tW.G tW.semi D₂ A₂ U₂ ψ β hψ bc hbc hbcβ hD hU

  have hid' : IsGrpPullback tW.G tW.G (spMap (RingHom.id T.V)) (𝟙 tW.G.left) :=
    GlobalTheory.LN.SelfCmp.isGrpPullback_of_eq_id tW.G hid
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U
    (RingHom.id T.V) (𝟙 _) hid'
  have hρs := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  have hρT := GlobalTheory.SpreadTorMatch.torMatch_of_spread T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id T.V) (𝟙 _) hid' ρ hρ
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.SpreadTrait.exists_spread T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂ U₂
    (RingHom.id T.V) (𝟙 _) hid'
  have hρ's := GlobalTheory.TorusOntoSpread.restrict_surjective T.V hTV tW.G tW.semi PW.D PW.A PW.U T.V hTV tW.G tW.semi D₂ A₂
    U₂ (RingHom.id T.V) (𝟙 _) hid' ρ' hρ'
  have hL₂ : LBIso PW.U.LG.L (U₂.LG.L.pull (𝟙 _)) :=
    LBIso.trans PW.U.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hLBW
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ (𝟙 _) (Category.id_comp β).symm).symm
  have hC₂ := TorCoord.coordMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV inferInstance tW.G tW.semi PW.D PW.A
    PW.U (RingHom.id _) (𝟙 _) (fun _ _ h => h) hid' hL₂ ρ hρT
  have hE₂ := equivMap_of_torMatch T.V hTV tW.G tW.semi D₂ A₂ U₂ T.V hTV tW.G tW.semi PW.D PW.A PW.U (RingHom.id _)
    (𝟙 _) (fun _ _ h => h) ρ hρT
  obtain ⟨-, -, -, -, n, ⟨eZ⟩⟩ := GlobalTheory.UPoinc.UTrait.balanced_posDef_lattice E H Dw l Xo c T
  haveI : Module.Finite ℤ T.P.D.toPre.X := Module.Finite.equiv eZ.symm
  haveI : Module.Finite ℤ PW.D.toPre.X := Module.Finite.equiv e.toAddEquiv.toIntLinearEquiv.symm
  have hρ'i : Function.Injective ρ' := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ.comp ρ').toIntLinearMap (hρs.comp hρ's)
    exact Function.Injective.of_comp (f := ⇑ρ) (g := ⇑ρ') h
  haveI : Module.Finite ℤ D₂.toPre.X := Module.Finite.of_surjective ρ'.toIntLinearMap hρ's
  have hρi : Function.Injective ρ := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (ρ'.comp ρ).toIntLinearMap (hρ's.comp hρs)
    exact Function.Injective.of_comp (f := ⇑ρ') (g := ⇑ρ) h
  let ρE : D₂.toPre.X ≃+ PW.D.toPre.X := AddEquiv.ofBijective ρ ⟨hρi, hρs⟩
  refine ⟨(hD.xe.symm.trans ρE).trans e.toAddEquiv, ?_, ?_⟩
  · intro y s hs
    obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm y)
    obtain ⟨h0, r', hr', hass⟩ := he (ρ (hD.xe.symm y))
    refine ⟨h0, ?_⟩
    have h1 : Associated (ψ s) r' := (hC₁ y s r₂ hs hr₂).trans (hC₂ _ r₂ r' hr₂ hr' : Associated r₂ r')
    exact (h1.pow_pow (n := 2)).trans hass
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom T.V hTV tW.G tW.semi D₂ A₂ U₂ (tW.act.act a) (tW.act.hom a)
    have h1 := hE₁ fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) m₂ hfRchar hm₂ y
    have h2 := hE₂ (tW.act.act a) (tW.act.act a) (tW.act.hom a) (tW.act.hom a) (by simp) m₂ _ hm₂
      (GlobalTheory.UPoinc.endChar_act E H T.V hTV tW PW a) (hD.xe.symm y)
    show e (ρ (hD.xe.symm (m a y))) = H.bar a • e (ρ (hD.xe.symm y))
    have h1' : hD.xe.symm (m a y) = m₂ (hD.xe.symm y) := h1
    rw [h1', h2]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeEquivCompletedLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_traitLattice_equiv_completedLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ (x : Y.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : Y.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsSemiAbelian G → IsGrpPullback G out.G (spMap j ≫ Y.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ Y.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ ρT : D.toPre.X ≃+ T.P.D.toPre.X, (∀ y s, PsiCoord D.toPre y s → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (ψ s ^ 2) (T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  first | exact @GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv | exact GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv | (intros; apply GlobalTheory.UPoinc.TraitCompare.exists_trait_lattice_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoAbelianSchemeSemiAbelianOfCommonGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoAbelianSchemeSemiAbelianOfCommonGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem iso_of_common_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (A G : Over (Sp O)) [GrpObj A] [GrpObj G] [IsCommMonObj G], IsAbelianScheme A → IsSemiAbelian G → ∀ (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (B : Over (Sp K)) [GrpObj B] (a : B.left ⟶ A.left) (g : B.left ⟶ G.left), IsGrpPullback B A (spMap (algebraMap O K)) a → IsGrpPullback B G (spMap (algebraMap O K)) g → ∃ i : A ≅ G, IsMonHom i.hom ∧ a ≫ i.hom.left = g ∧ (∀ (L : LB A.left) (L' : LB G.left), L.IsLB → L'.IsLB → LBIso (L.pull a) (L'.pull g) → LBIso L (L'.pull i.hom.left)) ∧ ∀ (e : A ⟶ A) (f : G ⟶ G) (eB : B ⟶ B), eB.left ≫ a = a ≫ e.left → eB.left ≫ g = g ≫ f.left → e ≫ i.hom = i.hom ≫ f := by
  intro O _ _ _ _ _ A G _ _ _ hA hG K _ _ _ B _ a g ha hg
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj := GlobalTheory.IsGenericPointHom.fractionField O K
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ :=
    GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions hS hj hA' hG ha hg
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian A hA'
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  refine ⟨E, hE, hEa, ?_, ?_⟩
  · intro L L' hL hL' h
    refine GlobalTheory.Poinc.Extend.lbIso_of_generic A hA ha.1 hL (pull_isLB hL' _) ?_
    exact LBIso.trans (pull_isLB hL _) (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) h
      (GlobalTheory.GenSpread.lbIso_pull_pull hL' a hEa.symm)
  · intro e f eB he hf
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback ha.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc a e.left, ← he, Category.assoc, hEa,
      reassoc_of% hEa]
    exact hf

end GlobalTheory.UPoinc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoAbelianSchemeSemiAbelianOfCommonGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_abelianScheme_semiAbelian_of_common_genericFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (A G : Over (Sp O)) [GrpObj A] [GrpObj G] [IsCommMonObj G], IsAbelianScheme A → IsSemiAbelian G → ∀ (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (B : Over (Sp K)) [GrpObj B] (a : B.left ⟶ A.left) (g : B.left ⟶ G.left), IsGrpPullback B A (spMap (algebraMap O K)) a → IsGrpPullback B G (spMap (algebraMap O K)) g → ∃ i : A ≅ G, IsMonHom i.hom ∧ a ≫ i.hom.left = g ∧ (∀ (L : LB A.left) (L' : LB G.left), L.IsLB → L'.IsLB → LBIso (L.pull a) (L'.pull g) → LBIso L (L'.pull i.hom.left)) ∧ ∀ (e : A ⟶ A) (f : G ⟶ G) (eB : B ⟶ B), eB.left ≫ a = a ≫ e.left → eB.left ≫ g = g ≫ f.left → e ≫ i.hom = i.hom ≫ f := by
  first | exact @GlobalTheory.UPoinc.iso_of_common_generic_fibre | exact GlobalTheory.UPoinc.iso_of_common_generic_fibre | (intros; apply GlobalTheory.UPoinc.iso_of_common_generic_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ActField

theorem exists_factor_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y : RatModel o Ω) (K : Type) [Field K]
    (s : Sp K ⟶ Y.Z), ∃ (z : Y.Z) (j : Sp (Y.O z) ⟶ Y.Z) (s' : Sp K ⟶ Sp (Y.O z)),
      spMap (algebraMap (Y.O z) Ω) ≫ j = Y.pt ∧ s' ≫ j = s ∧ j (IsLocalRing.closedPoint (Y.O z)) = z ∧ ∀ w, s w = z := by
  intro o Ω _ _ _ Y K _ s
  have hsz : ∀ w, s w = s (IsLocalRing.closedPoint K) := fun w => by
    rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
  let z := s (IsLocalRing.closedPoint K)
  let e := Y.stalkEquiv z
  let E : Y.Z.presheaf.stalk z ⟶ CommRingCat.of (Y.O z) := CommRingCat.ofHom e.toRingHom
  let E' : CommRingCat.of (Y.O z) ⟶ Y.Z.presheaf.stalk z := CommRingCat.ofHom e.symm.toRingHom
  have hEE : E ≫ E' = 𝟙 _ := by ext a; exact e.symm_apply_apply a
  refine ⟨z, Spec.map E ≫ Y.Z.fromSpecStalk z, Spec.map (E' ≫ Scheme.stalkClosedPointTo s), ?_, ?_, ?_, hsz⟩
  · have h1 : E ≫ CommRingCat.ofHom (algebraMap (Y.O z) Ω) =
        Y.Z.presheaf.stalkSpecializes (Y.pt_specializes (IsLocalRing.closedPoint Ω) z) ≫
          Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Y.pt := by
      ext a; rfl
    show Spec.map _ ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, hEE, Category.id_comp,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · haveI : IsLocalHom E.hom := ⟨fun a ha => by
      have h := ha.map e.symm.toRingHom
      have h' : e.symm.toRingHom (E.hom a) = a := e.symm_apply_apply a
      rwa [h'] at h⟩
    change Y.Z.fromSpecStalk z ((Spec.map E) (IsLocalRing.closedPoint (CommRingCat.of (Y.O z)))) = z
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem exists_factor_i : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (O : Type) [CommRing O] [IsLocalRing O] (g : Sp O ⟶ C.Z),
      g (IsLocalRing.closedPoint O) ∈ Set.range C.i → ∃ v : Sp O ⟶ Xo.XF c, g = v ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C O _ _ g hg
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  obtain ⟨x, hx⟩ := hg
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ C.z)
  have hpt : (Spec.map φ) (IsLocalRing.closedPoint O) =
      (spMap C.b) ((pullback.snd C.z (spMap C.b)) (C.iF x)) := by
    rw [hφ]
    change C.z (g _) = _
    rw [← hx]
    change ((C.iF ≫ pullback.fst C.z (spMap C.b)) ≫ C.z) x = ((C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ spMap C.b) x
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hbot : Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = ⊥ := by
    have hc := congrArg PrimeSpectrum.asIdeal hpt
    change Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = Ideal.comap C.b _ at hc
    haveI := ((pullback.snd C.z (spMap C.b)) (C.iF x)).isPrime
    rw [hc, Ideal.eq_bot_of_prime ((pullback.snd C.z (spMap C.b)) (C.iF x)).asIdeal]
    exact Ideal.comap_bot_of_injective _ C.inj
  have hunit : ∀ y : nonZeroDivisors C.o, IsUnit (φ.hom y) := fun y => by
    by_contra hy
    have hm : (y : C.o) ∈ Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) := (IsLocalRing.mem_maximalIdeal _).2 hy
    rw [hbot, Ideal.mem_bot] at hm
    exact nonZeroDivisors.ne_zero y.2 hm
  let ψF : c.F →+* O := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) hunit
  have hψF : ψF.comp C.b = φ.hom := IsLocalization.lift_comp hunit
  have w : g ≫ C.z = Spec.map (CommRingCat.ofHom ψF) ≫ spMap C.b := by
    rw [← hφ]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (RingHom.congr_fun hψF a).symm
  let g' : Sp O ⟶ pullback C.z (spMap C.b) := pullback.lift g _ w
  have hg'1 : g' ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) := (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  have hcl : g' (IsLocalRing.closedPoint O) ∈ Set.range C.iF := ⟨x, hinj (by
    change (C.iF ≫ pullback.fst _ _) x = (g' ≫ pullback.fst _ _) _
    rw [hg'1]; exact hx)⟩
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    haveI := C.iF_open
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map g'.continuous).mem_open C.iF.isOpenEmbedding.isOpen_range hcl
  haveI := C.iF_open
  refine ⟨IsOpenImmersion.lift C.iF g' hrange, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hg'1]

theorem isNoetherianRing_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (Y : RatModel o Ω)
    (z : Y.Z), IsNoetherianRing (Y.O z) := by
  intro o Ω _ _ _ _ Y z
  haveI := Y.lft
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  exact isNoetherianRing_of_ringEquiv _ (Y.stalkEquiv z)


set_option maxHeartbeats 4000000 in
theorem exists_action_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hr wi

  have hrange : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hO.ne (x := w) trivial
  let xU : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hrange
  have hxU : xU ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu₀ : xU ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen xU hxU
  have wℓ : wi.α ≫ X₁.ρ.P.A.hom = (wi.G.hom ≫ xU) ≫ out.u₀ := by
    rw [Category.assoc, hu₀]; exact wi.hα.1.w
  let ℓ : wi.G.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift wi.α (wi.G.hom ≫ xU) wℓ
  have hℓα : ℓ ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hℓ : IsGrpPullback wi.G ((Over.pullback out.u₀).obj X₁.ρ.P.A) xU ℓ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (wi.hα.congr hu₀.symm hℓα.symm)
      (pullback.lift_snd _ _ _)
  let ψ : wi.G.left ⟶ out.G.left := ℓ ≫ out.φ
  have hψ : IsGrpPullback wi.G out.G Y.pt ψ := (hℓ.comp out.cart).congr hxU rfl

  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c (Sp X₁.Ω₁) X₁.uΩ wi.G wi.β wi.hβ
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hψ (isGrpPullback_pullback out.G Y.pt)
  haveI := he
  have hf' : ∀ a, IsMonHom (e.inv ≫ f₀ a ≫ e.hom) := fun a => by
    haveI := (hf₀ a).1
    infer_instance
  have hF : ∀ a, ∃ F : out.G ⟶ out.G, IsMonHom F ∧ (Over.pullback Y.pt).map F = e.inv ≫ f₀ a ≫ e.hom :=
    fun a => (out.endo _ (hf' a)).exists
  choose F hFm hFe using hF
  have hmap : ∀ {S' : Scheme.{0}} (q : S' ⟶ Y.Z) (a : 𝓞 E),
      ((Over.pullback q).map (F a)).left ≫ pullback.fst out.G.hom q = pullback.fst out.G.hom q ≫ (F a).left :=
    fun q a => pullback.lift_fst _ _ _
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have gen₀ : ∀ a, (f₀ a).left ≫ ψ = ψ ≫ (F a).left := fun a => by
    have key : e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left = (f₀ a).left ≫ e.hom.left := by
      rw [hFe a, Over.comp_left, Over.comp_left, ← Category.assoc, hei, Category.id_comp]
    calc (f₀ a).left ≫ ψ = ((f₀ a).left ≫ e.hom.left) ≫ pullback.fst _ _ := by rw [← heψ, Category.assoc]
      _ = (e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left) ≫ pullback.fst _ _ := by rw [key]
      _ = ψ ≫ (F a).left := by rw [Category.assoc, hmap, ← Category.assoc, heψ]
  have uniq : ∀ (a : 𝓞 E) (e' : wi.G ⟶ wi.G), e'.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e' = f₀ a :=
    fun a e' h => Over.OverMorphism.ext (wi.hβ.1.hom_ext (h.trans (hf₀ a).2.symm) (by rw [Over.w, Over.w]))
  refine ⟨F, ψ, hFm, hψ, fun T w => ⟨w ≫ ℓ, Category.assoc _ _ _, by rw [Category.assoc, hℓα]⟩,
    fun a e' h => (uniq a e' h) ▸ gen₀ a, ?_⟩

  intro K _ s y hsy tK ⟨mm⟩
  haveI : IsNoetherianRing X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  obtain ⟨z₀, j, s', hj, hs', hjz, hsz⟩ := exists_factor_localRing _ _ Y K s
  haveI := isNoetherianRing_O _ _ Y z₀
  haveI := RatModel.isIntegrallyClosed_O hO.normal z₀
  have hpt : (j ≫ r) (IsLocalRing.closedPoint (Y.O z₀)) = C.i (y (IsLocalRing.closedPoint K)) := by
    change r (j (IsLocalRing.closedPoint (Y.O z₀))) = _
    rw [hjz, ← hsz (IsLocalRing.closedPoint K)]
    change (s ≫ r) _ = (y ≫ C.i) _
    rw [hsy]
  obtain ⟨v, hv⟩ := exists_factor_i E H Dw l Xo c C (Y.O z₀) (j ≫ r) ⟨_, hpt.symm⟩
  haveI := C.isPreimmersion_i
  have hsv : s' ≫ v = y := (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hs', hsy])
  have hgv : spMap (algebraMap (Y.O z₀) X₁.Ω₁) ≫ v = X₁.uΩ :=
    (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hj, hr])
  haveI : IsCommMonObj ((Over.pullback j).obj out.G) := Functor.isCommMonObj_obj
  have hAb : IsAbelianScheme ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) :=
    by
      have hA : IsAbelianScheme Xo.univ.t.G := (Obj.toPolAV Xo.univ).isAb
      haveI := hA.comm
      haveI := hA.smooth
      haveI := hA.proper
      haveI := hA.geomConnected
      exact ⟨Functor.isCommMonObj_obj,
        by change Smooth (pullback.snd _ _); infer_instance,
        by change IsProper (pullback.snd _ _); infer_instance,
        by change GeometricallyConnected (pullback.snd _ _); infer_instance⟩
  have hSe := IsSemiAbelian.pullback j out.G out.semi
  have wa : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ v ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hgv]; simp only [Category.assoc]
  let aa := pullback.lift _ _ wa
  have haa : aa ≫ pullback.fst _ _ = wi.β := pullback.lift_fst _ _ _
  have ha : IsGrpPullback wi.G ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G)
      (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) aa :=
    (isGrpPullback_pullback Xo.univ.t.G _).cancel (wi.hβ.congr (by rw [← hgv, Category.assoc]) haa.symm)
      (pullback.lift_snd _ _ _)
  have wg : ψ ≫ out.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ j := by
    rw [hψ.1.w, Category.assoc, hj]
  let gg := pullback.lift _ _ wg
  have hgg : gg ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hg : IsGrpPullback wi.G ((Over.pullback j).obj out.G) (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) gg :=
    (isGrpPullback_pullback out.G j).cancel (hψ.congr hj.symm hgg.symm) (pullback.lift_snd _ _ _)
  obtain ⟨i, hi, hai, hLi, hEi⟩ := GlobalTheory.T.iso_abelianScheme_semiAbelian_of_common_genericFibre (Y.O z₀) _ ((Over.pullback j).obj out.G) hAb hSe X₁.Ω₁ wi.G aa gg ha hg
  haveI := hi
  obtain ⟨f₁, hf₁, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c (Sp (Y.O z₀)) v ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) (pullback.fst _ _)
    (isGrpPullback_pullback Xo.univ.t.G (v ≫ pullback.fst _ _))
  have mm' : SABMap tK Xo.univ.t ((s' ≫ v) ≫ pullback.fst _ _) := hsv ▸ mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hactγ⟩ := hT (Sp K) s' tK mm'
  refine ⟨γ₀ ≫ i.hom.left ≫ pullback.fst out.G.hom j, ?_, ?_, ?_⟩
  · exact (hγ₀.comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback out.G j))).congr
      (by rw [Category.id_comp, hs']) rfl
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hOL := out.L.isLB
    have sA : LBIso (X₁.ρ.P.L.pull wi.α) (out.L.L.pull ψ) :=
      GenSpread.lbIso_pull_comp ℓ hℓα.symm rfl (LBIso.symm ⟨out.w, out.w_gen⟩)
    have sB : LBIso (Xo.univ.t.PP.L.pull wi.β) (out.L.L.pull ψ) :=
      LBIso.trans (pull_isLB hU _) (pull_isLB hP _) (pull_isLB hOL _) wi.hL.symm sA
    have sC : LBIso ((Xo.univ.t.PP.L.pull (pullback.fst _ _)).pull aa)
        ((out.L.L.pull (pullback.fst out.G.hom j)).pull gg) :=
      LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB (pull_isLB hOL _) _)
        (GenSpread.lbIso_pull_pull hU aa haa.symm).symm
        (LBIso.trans (pull_isLB hU _) (pull_isLB hOL _) (pull_isLB (pull_isLB hOL _) _) sB
          (GenSpread.lbIso_pull_pull hOL gg hgg.symm))
    have sD := hLi _ _ (pull_isLB hU _) (pull_isLB hOL _) sC
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hOL _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB hOL _)
        (GenSpread.lbIso_pullback sD γ₀)
        (LBIso.trans (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB (pull_isLB hOL _) _) (pull_isLB hOL _)
          (GenSpread.lbIso_pull_pull (pull_isLB hOL _) γ₀ rfl).symm
          (GenSpread.lbIso_pull_pull hOL (γ₀ ≫ i.hom.left) (Category.assoc _ _ _).symm).symm))
  · intro a
    have h1 : (f₀ a).left ≫ aa = aa ≫ (f₁ a).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, haa, Category.assoc, (hf₁ a).2, ← Category.assoc, haa, (hf₀ a).2]
      · have w1 := Over.w (f₁ a)
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h2 : (f₀ a).left ≫ gg = gg ≫ ((Over.pullback j).map (F a)).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hmap, hgg, ← Category.assoc gg, hgg, gen₀]
      · have w1 := Over.w ((Over.pullback j).map (F a))
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h3 := congrArg Over.Hom.left (hEi (f₁ a) ((Over.pullback j).map (F a)) (f₀ a) h1 h2)
    rw [Over.comp_left, Over.comp_left] at h3
    rw [← Category.assoc, hactγ a]
    simp only [Category.assoc]
    rw [← Category.assoc (f₁ a).left, h3, Category.assoc, hmap]

end GlobalTheory.UPoinc.ActField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianActionEqUniversalAtFieldPointsOfThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianAction_eq_universal_at_fieldPoints_of_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  first | exact @GlobalTheory.UPoinc.ActField.exists_action_field | exact GlobalTheory.UPoinc.ActField.exists_action_field | (intros; apply GlobalTheory.UPoinc.ActField.exists_action_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

private theorem fieldPt_lift_preimm {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

theorem oAct_along_traits_of_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨f, ψ, hfm, -, -, -, H0⟩ := GlobalTheory.T.semiAbelianAction_eq_universal_at_fieldPoints_of_thetaModel E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt wi
  refine ⟨f, hfm, ?_, ?_⟩
  · rintro z ⟨x, hx⟩ K _ _ t ⟨p, hp⟩
    haveI := C.isPreimmersion_i
    obtain ⟨y, hy⟩ := fieldPt_lift_preimm C.i (t ≫ r) x (by
      have e : (t ≫ r) (IsLocalRing.closedPoint K) = r (t p) := by
        rw [Subsingleton.elim (α := PrimeSpectrum K) (IsLocalRing.closedPoint K) p]
        exact Scheme.Hom.comp_apply _ _ _
      rw [e, hp, hx])
    obtain ⟨tK, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (y ≫ pullback.fst _ _) Xo.univ.t
    obtain ⟨γ, hγ, -, -⟩ := H0 K t y hy.symm tK ⟨m⟩
    haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
    haveI : IsProper tK.G.hom := MorphismProperty.of_isPullback m.cart.1 inferInstance
    rw [← hγ.1.isoPullback_inv_snd]
    infer_instance
  · intro T ξ hξ
    obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
    obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) (jK T.V ≫ ξ) T.y (by rw [Category.assoc]; exact hξ) tK ⟨m₂⟩
    obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi Y.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart hγ
    refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
    have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have hL := out.L.isLB
    refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
    exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
      (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
        (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  first | exact @GlobalTheory.UPoinc.oAct_along_traits_of_over | exact GlobalTheory.UPoinc.oAct_along_traits_of_over | (intros; apply GlobalTheory.UPoinc.oAct_along_traits_of_over <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GPeriods

theorem exists_completion_unif {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)
    (hO : S.Over₀ M U₀) (x : M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R)
      (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R))
      (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsSemiAbelian G ∧
      IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧
      ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _, IsSemiAbelian.pullback ξ FinalForm.G FinalForm.semi,
    isGrpPullback_pullback _ _, hL, hP⟩

end GlobalTheory.UPoinc.GPeriods

theorem GlobalTheory.UPoinc.GPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = T.be (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt x
  obtain ⟨f, hf, hab, hβ⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hS, hG, hL, hP⟩ :=
    GlobalTheory.UPoinc.GPeriods.exists_completion_unif out hO x
  have hm : ∀ a : 𝓞 E, ∃ m : D.toPre.X →+ D.toPre.X, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧
      EndChar U fR m := by
    intro a
    haveI := hf a
    obtain ⟨fR, hfR, e⟩ := GlobalTheory.PullAction.exists_lift_end hG (f a)
    obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hB G hS D A U fR hfR
    exact ⟨m, fR, hfR, e, hm⟩
  choose m hm using hm
  have key := fun (T : UTrait Xo c) (ψ : R →+* T.V) (hψ : IsLocalHom ψ) hc =>
    GlobalTheory.T.exists_traitLattice_equiv_completedLocalRing E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt f hf hab hβ x R j hB hC G gm hS hG D A U hL hP m hm T ψ hψ hc
  haveI : CharZero R := hB.2
  have hco : ∀ y : D.toPre.X, ∃ s, PsiCoord D.toPre y s := fun y =>
    ((GlobalTheory.PsiCoordLocal.main R D hB.1.2.2.1 y).1).imp fun _ h => h.1
  choose s hs using hco
  by_cases hex : ∃ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ ∧
      jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i
  · obtain ⟨T₀, ψ₀, hψ₀, hc₀⟩ := hex
    obtain ⟨ρ₀, -, hρ₀⟩ := key T₀ ψ₀ hψ₀ hc₀
    refine ⟨R, inferInstance, inferInstance, inferInstance, j, T₀.P.D.toPre.X, inferInstance, inferInstance,
      fun y => s (ρ₀.symm y) ^ 2, hB, hC, ?_⟩
    intro T ψ hψ hc
    obtain ⟨ρT, hord, heq⟩ := key T ψ hψ hc
    have hsymm : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), ρ₀.symm (H.bar a • v) = m a (ρ₀.symm v) := fun a v => by
      apply ρ₀.injective
      rw [AddEquiv.apply_symm_apply, hρ₀, AddEquiv.apply_symm_apply]
    let e₀ : T₀.P.D.toPre.X ≃+ T.P.D.toPre.X := ρ₀.symm.trans ρT
    have hlin : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), e₀ (a • v) = a • e₀ v := fun a v => by
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      show ρT (ρ₀.symm (H.bar b • v)) = H.bar b • ρT (ρ₀.symm v)
      rw [hsymm, heq]
    refine ⟨{ e₀ with map_smul' := hlin }, fun y => ?_⟩
    obtain ⟨h0, hA⟩ := hord (ρ₀.symm y) (s (ρ₀.symm y)) (hs _)
    refine ⟨(T.be (ρT (ρ₀.symm y)) (ρT (ρ₀.symm y))).toNat, Int.toNat_of_nonneg h0, ?_⟩
    rw [map_pow]
    exact hA
  · refine ⟨R, inferInstance, inferInstance, inferInstance, j, PUnit, inferInstance, inferInstance, fun _ => 0, hB, hC,
      fun T ψ hψ hc => (hex ⟨T, ψ, hψ, hc⟩).elim⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLocalPeriodsThetaModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.UPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R) (c₀ : ℕ), IsNoetherianRing R ∧ CharZero R ∧ GlobalTheory.Poinc.Eq8.IsCpl j ∧ 1 ≤ c₀ ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → T.y ≫ C.i = jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ a, ∃ k : ℕ, (k : ℤ) = c₀ * T.be (e a) (e a) ∧ Associated (ψ (p a)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ Y U₀ EE out πY hAdm _ hHom x
  have hpt : Y.pt ≫ πY ≫ X₁.π = X₁.uΩ ≫ C.i := by
    have h1 : Y.pt ≫ πY = X₁.M.pt := by
      have := hHom
      unfold RatModel.IsHom at this
      rw [this]
      show Spec.map (CommRingCat.ofHom (RingHom.id X₁.Ω₁)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [← Category.assoc, h1, X₁.comp]
    exact (Category.assoc _ _ _).symm
  obtain ⟨R, i1, i2, i3, j, Λ, i4, i5, p, hB, hC, h⟩ :=
    GlobalTheory.UPoinc.GPeriods.main E H Dw l Xo c C X₁ Y U₀ EE out (πY ≫ X₁.π) hAdm.1 hpt x
  refine ⟨R, i1, i2, i3, j, Λ, i4, i5, p, 1, hB.1.1, hB.2, hC, le_rfl, fun T ψ hψ ht => ?_⟩
  obtain ⟨e, he⟩ := h T ψ hψ (by rw [ht])
  refine ⟨e, fun a => ?_⟩
  obtain ⟨k, hk, hA⟩ := he a
  exact ⟨k, by rw [hk]; push_cast; ring, hA⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLocalPeriodsThetaModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_local_periods_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R) (c₀ : ℕ), IsNoetherianRing R ∧ CharZero R ∧ GlobalTheory.Poinc.Eq8.IsCpl j ∧ 1 ≤ c₀ ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → T.y ≫ C.i = jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ a, ∃ k : ℕ, (k : ℤ) = c₀ * T.be (e a) (e a) ∧ Associated (ψ (p a)) (T.ϖ ^ k) := by
  first | exact @GlobalTheory.UPoinc.UPeriods.main | exact GlobalTheory.UPoinc.UPeriods.main | (intros; apply GlobalTheory.UPoinc.UPeriods.main <;> assumption)
end
