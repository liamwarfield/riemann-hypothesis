module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsWitnessesBaseChangeAlongTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsWitnessesBaseChangeAlongTower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.TermsTrans

open GlobalTheory.TermsMove GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull

theorem tfk_hom (V : Type) [CommRing V] [IsDomain V] : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

theorem gw_stalk {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (r : Z ⟶ Y)
    (g : Y ⟶ X') (z : Z) {j : L.ι} {k : L'.ι} (hj : F (g (r z)) ∈ L.U j) (hk : g (r z) ∈ L'.U k) :
    (Geo.Tor.gw w (r ≫ g) z j k).val = (r.stalkMap z).hom (Geo.Tor.gw w g (r z) j k).val := by
  have hm : g (r z) ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (gs_unit (r ≫ g) z _ hm _).symm.trans ((LiftTest.gs_comp r g z _ hm _).trans
    (congrArg _ (gs_unit g (r z) _ hm _)))

theorem exists_theta {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V]
    [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A))
    (fr : ∀ a, FrAt (x a)) (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    (hfr : ∀ a z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∃ th : SecA 𝔪.A (FractionRing V) 1, ∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := by
  have gp := 𝔪.cart
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [tfk_hom]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨th, fun a => ?_⟩
  have H : GlobalTheory.ThetaPtMove.GenThrough 𝔪.wl _ _ _ (fr a) (X₁.ρ.fr a)
      (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) := by
    intro Z r z J J' hJ hJ'
    have e := congrArg (fun u => (r.stalkMap z).hom (Units.val u))
      (hfr a (r z) _ _ (LevelExpansion.good_comp r hJ) (LevelExpansion.good_comp r hJ'))
    rw [Fin.prod_univ_one, zpow_one]
    refine Units.ext ((LevelExpansion.val_comp _ r _ hJ).trans (e.symm.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ ?_))))
    · refine (gw_stalk 𝔪.wl r (x a).left z (hJ (r ≫ (x a).left ≫ 𝔪.φ)) (hJ' (r ≫ (x a).left))).symm.trans ?_
      rw [← Category.assoc]
      rfl
    · exact (LevelExpansion.val_comp _ r (𝟙 _) hJ').symm.trans (by rw [Category.comp_id])
  have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
    (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) H (s₀ := X₁.ρ.th₁) (s := th) hth
    (X₁.ρ.th_val a)
  intro z J hJ
  have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at e
  refine e.trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
  congr 1
  exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
    ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

theorem exists_moved {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    [Algebra (FractionRing R) (FractionRing R')] {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {Φ : A'.A.left ⟶ A.A.left} {v : LB.Iso A'.L (A.L.pull Φ)} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} (hI : I.map φ ≤ I') (hbc : IsMonHom bc.hom)
    (hU : IsPullUnif φ hD bc U U') (hF : Compat φ (FractionRing R'))
    (gΦ : IsPullback Φ A'.A.hom A.A.hom (spMap (algebraMap (FractionRing R) (FractionRing R')))) (hv : v.IsGen)
    (hΦ : U'.gen.hom.left ≫ Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {th : SecA A (FractionRing R) 1} {s : Fam D.toPre (FractionRing R) 1}
    (hE : U.ExpandsF (FractionRing R) 1 w₀ th s) :
    ∃ (w₀' : W0 U'.toUnifPre) (th' : SecA A' (FractionRing R') 1) (s' : Fam D'.toPre (FractionRing R') 1),
      w₀'.IsGen ∧ U'.ExpandsF (FractionRing R') 1 w₀' th' s' ∧
      (∀ (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R') (FractionRing R') ⟶ A'.A)
        (fr' : FrAt x') (ρ : (FractionRing R')ˣ) (c : FractionRing R),
        x'.left ≫ Φ = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ x.left →
        FrPull v (algebraMap _ _) x' fr' x fr ρ → ValAt th x fr c →
        ValAt th' x' fr' (algebraMap (FractionRing R) (FractionRing R') c * (ρ⁻¹).val)) ∧
      ∀ (g : GtPtF D.toPre (FractionRing R)) (w : GlobalTheory.UT.Frm D.toPre (FractionRing R) 1 g.b) (ρ : (FractionRing R')ˣ),
        w.IsGen → ∃ (g' : GtPtF D'.toPre (FractionRing R')) (w' : GlobalTheory.UT.Frm D'.toPre (FractionRing R') 1 g'.b), w'.IsGen ∧
        (∀ n, (∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) → ∃ o, GtPtF.IsNsmul n g' o ∧ o.IsZero) ∧
        (∀ α, coef s' g' w' α * ρ = algebraMap (FractionRing R) (FractionRing R') (coef s g w (hD.xe α))) ∧
        ∀ (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R') (FractionRing R') ⟶ A'.A)
          (fr' : FrAt x'), fr.IsGen → x'.left ≫ Φ = spMap (algebraMap (FractionRing R) (FractionRing R')) ≫ x.left →
          FrPull v (algebraMap _ _) x' fr' x fr ρ → LiesOver U.toUnifPre (FractionRing R) w₀ g w x fr →
          LiesOver U'.toUnifPre (FractionRing R') w₀' g' w' x' fr' := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  have hg₂ : jFK (R := R') (FractionRing R') ≫ spMap (algebraMap (FractionRing R) (FractionRing R')) =
      jFK (R := R) (FractionRing R') := by
    rw [show jFK (R := R') (FractionRing R') = 𝟙 _ from tfk_hom R']
    exact Category.id_comp _
  obtain ⟨w₀', hw₀', Ω, h₁, h₂, H⟩ := exists_expand hG hbc hU hF hg₂ gΦ hv hΦ hw₀ hκ
  obtain ⟨th', s', E', up, fup⟩ := (H 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing R') U.toUnifPre hG hE)
  have frup : ∀ {x : TFK (R := R) (FractionRing R) ⟶ A.A} {fr : FrAt x} {x' : TFK (R := R') (FractionRing R') ⟶ A'.A}
      {fr' : FrAt x'} {ρ : (FractionRing R')ˣ}, FrPull v (algebraMap _ _) x' fr' x fr ρ →
      FrUp v fr' (frExt (FractionRing R') fr) ρ := fun {x fr x' fr' ρ} h z J J' hJ hJ' => by
    refine (h z J J' hJ hJ').trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    exact ((val_frExt fr (𝟙 _) hJ).trans (by rw [Category.id_comp])).symm
  refine ⟨w₀', th', s', hw₀', E', fun x fr x' fr' ρ c hx hp hc => ?_, fun g w ρ hw => ?_⟩
  · have := valAt_pull h₁ h₂ up (x := fieldMap (R := R) (FractionRing R) (FractionRing R') ≫ x) hx (frup hp)
      (valAt_ext hc)
    rwa [pow_one] at this
  obtain ⟨g₁, w₁, hw₁, t₁, c₁, l₁⟩ := exists_ext (F := FractionRing R') hG U hw₀ g hw
  obtain ⟨g', w', hw', t₂, c₂, l₂⟩ := exists_point hG hI hF hκ h₁ h₂ (fun k hk => (H k hk).2) g₁ hw₁ ρ
  refine ⟨g', w', hw', fun n h => t₂ n (t₁ n h), fun α => (c₂ _ _ fup α).trans (c₁ s _),
    fun x fr x' fr' gen hx hp hl => ?_⟩
  have a := l₁ x fr gen hl
  have b : (frExt (FractionRing R') fr).IsGen := pullGen_isGen _ _ _ _ gen _
  exact l₂ x' fr' (fieldMap (R := R) (FractionRing R) (FractionRing R') ≫ x) (frExt (FractionRing R') fr) b hx (frup hp) a

theorem terms_witnesses_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro I X₁ act 𝔗 z₁ z₂ _ x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C lab x fr th w₀ s g' w hx hfr hth hw₀ hE hc V' _ _ _ io f hf hinj hfin
    ev₂ 𝔪₂ ψ hD bc _ hy gψ wψ hwψ hφ hbc hU hxe hgen x₂ fr₂ hx₂ hfr₂ ρ hρ
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := by
    have := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
    exact Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit io v hv
  obtain ⟨w₀₂, th', s', hw₀₂, E', hval, hpt⟩ := exists_moved (v := wψ) hI hbc hU hf gψ.1 hwψ hgen hw₀ hE
  have hxx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = spMap f ≫ (x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · have e : spMap 𝔪₂.yK ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK :=
        (Spec.map_comp (CommRingCat.ofHom 𝔗.om) (CommRingCat.ofHom 𝔪₂.yK)).symm.trans
          ((congrArg spMap hy).trans (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom f)))
      rw [Category.assoc, ← hφ, ← Category.assoc, hx₂, Category.assoc, Category.assoc, hx]
      exact (congrArg (_ ≫ ·) (𝔗.lam_pt b)).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
        (Category.assoc _ _ _)))
    · rw [Category.assoc, gψ.1.w, ← Category.assoc, Over.w (x₂ (𝔗.lam b)), Category.assoc, Over.w (x b), tfk_hom, tfk_hom]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hv' := fun b => hval _ _ _ _ (ρ b) _ (hxx b) (hρ b) (hth b)
  have hne : (show AbSec 𝔪₂.A (FractionRing V') 1 from th') ≠ 0 := fun h => by
    have h₀ := hv' x₀
    rw [show th' = _ from h] at h₀
    exact mul_ne_zero ((map_ne_zero_iff f f.injective).2
      (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)) (Units.ne_zero _)
      (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨th₂, hth₂⟩ := exists_theta 𝔪₂ x₂ fr₂ hx₂ fun a => (hfr₂ a).2
  obtain ⟨K, hK⟩ := exists_eq_smul hne th₂
  choose g₂ w₂ hw₂ ht₂ hc₂ hl₂ using fun c => hpt (g' c) (w c) (ρ (lab c)) (hc c).2.1
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') (k := 1) le_rfl w₀₂ hw₀₂
  refine ⟨th₂, w₀₂, K • s', g₂, w₂, K, hth₂, hw₀₂, (he _ _).2 ?_, fun c => ⟨?_, hw₂ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e hK).trans ((map_smul e K _).trans (congrArg (K • ·) ((he _ _).1 E')))
  · letI := @TorusExt.gtGroup
    obtain ⟨o, o₁, o₂⟩ := ht₂ c _ (hc c).1
    rw [TorusExt.isNsmul_iff_eq] at o₁
    rw [TorusExt.isZero_iff_eq] at o₂
    refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [𝔗.lev, mul_nsmul, ← o₁, o₂, nsmul_zero]
  · exact hl₂ c _ _ _ _ (hfr _).1 (hxx _) (hρ _) (hc c).2.2
  · rw [coef_smul (hw₂ c), _root_.mul_assoc, hc₂, hxe]
    rfl
  · have a := valAt_lin (hv' b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at a
    rw [valAt_unique (hth₂ _) a, _root_.mul_assoc, Units.inv_mul_cancel_right]
    rfl

end GlobalTheory.GSep.TermsTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsWitnessesBaseChangeAlongTowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.termsWitnesses_baseChange_along_tower : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  first | exact @GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange | exact GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange | (intros; apply GlobalTheory.GSep.TermsTrans.terms_witnesses_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointsTransportedFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointsTransportedFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep

theorem exists_points_frames : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X)
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  refine ⟨x, fr, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩⟩
  have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
  rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
  exact e.symm

end GlobalTheory.GSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointsTransportedFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoints_transported_frames : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X)
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
    (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) := by
  first | exact @GlobalTheory.GSep.exists_points_frames | exact GlobalTheory.GSep.exists_points_frames | (intros; apply GlobalTheory.GSep.exists_points_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTowerFramesPullbackConstantRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTowerFramesPullbackConstantRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.TowerFrames

open GlobalTheory.ConstFam GlobalTheory.FrameMove

section General

variable {S : Scheme.{0}} {P : PolAV S} {T : Over S}

theorem torsFrame_vals {rig : LB.Gen (P.L.pull (eSec P.A))} {n : ℕ} {x : T ⟶ P.A} {τ} (H : IsTorsFrame P rig n x τ) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (y : T.left) J, Good P.L y J → val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α x.left y J * rval rig T.hom y J ∧
        val α (T.hom ≫ eSec P.A) y J = rval rig T.hom y J ^ ((n : ℤ) ^ 2) * (rval rig T.hom y J)⁻¹ := by
  obtain ⟨-, -, α, hα, hN, hc⟩ := H
  refine ⟨α, hα, fun y J hJ => ⟨?_, ?_⟩⟩
  · have a : val τ (𝟙 _) y J ^ ((n : ℤ) ^ 2) = val α (𝟙 _ ≫ x.left) y J * rval rig (𝟙 _ ≫ T.hom) y J ^ (1 : ℤ) :=
      (map_zpow _ _ _).symm.trans ((val_corr hJ hc (𝟙 _)).trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_rigT _ _ _ hJ))))
    rwa [Category.id_comp, Category.id_comp, zpow_one] at a
  · exact (val_pull hJ α (eSec P.A) T.hom).symm.trans ((val_corr hJ hN T.hom).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (map_zpow _ _ _) (val_inv _ _))))

theorem torsFrame_ratio_pow [IsLocallyNoetherian S] {rig₁ rig₂ : LB.Gen (P.L.pull (eSec P.A))} {n d : ℕ} {x : T ⟶ P.A}
    {τ₁ τ₂} (H₁ : IsTorsFrame P rig₁ n x τ₁) (H₂ : IsTorsFrame P rig₂ (n * d) x τ₂) (y : T.left) (J)
    (hJ : Good P.L y J) : (val τ₂ (𝟙 _) y J * (val τ₁ (𝟙 _) y J)⁻¹) ^ ((n * d) ^ 2) =
      (rval rig₂ T.hom y J * (rval rig₁ T.hom y J)⁻¹) ^ ((n * d) ^ 2) := by
  obtain ⟨α₁, h₁, v₁⟩ := torsFrame_vals H₁
  obtain ⟨α₂, h₂, v₂⟩ := torsFrame_vals H₂
  obtain ⟨β, hβ⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulPull S P d
  have e : (mulA P.A n).left ≫ (mulA P.A d).left = (mulA P.A (n * d)).left := by
    rw [comp_mulA, ← pow_mul]
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const P.isLB P.A.hom (eSec P.A) (Over.w η[P.A])
    (GlobalTheory.abelianSchemeLaws_all.1.globalFns S P.A P.isAb).2 (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ h₂) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.powGen_isGen _ _ _ _ h₁ (d ^ 2)) (DVR.pullGen_isGen _ _ _ _ hβ (mulA P.A n).left)))
  have p : ∀ r : T.left ⟶ P.A.left, val (GeneratorPullback.powGen P.L _ _ α₁ (d ^ 2)) r y J = val α₁ r y J ^ (d ^ 2) :=
    fun r => map_pow _ _ _
  have c₁ := ha _ x.left y J hJ
  have c₂ := ha _ (T.hom ≫ eSec P.A) y J hJ
  have e₀ : (T.hom ≫ eSec P.A) ≫ P.A.hom = T.hom := Over.w (1 : T ⟶ P.A)
  rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, p] at c₁ c₂
  rw [comp_mulA, H₁.1, Over.w x] at c₁
  rw [e₀, Category.assoc, eSec_mulA] at c₂
  have c := c₁.trans c₂.symm
  have c' : (val α₂ x.left y J)⁻¹ * val α₁ x.left y J ^ (d ^ 2) =
      (val α₂ (T.hom ≫ eSec P.A) y J)⁻¹ * val α₁ (T.hom ≫ eSec P.A) y J ^ (d ^ 2) := by
    rw [← _root_.mul_assoc, ← _root_.mul_assoc] at c
    exact mul_right_cancel c
  obtain ⟨a₁, b₁⟩ := v₁ y J hJ
  obtain ⟨a₂, b₂⟩ := v₂ y J hJ
  apply Additive.ofMul.injective
  replace a₁ := congrArg Additive.ofMul a₁
  replace a₂ := congrArg Additive.ofMul a₂
  replace b₁ := congrArg Additive.ofMul b₁
  replace b₂ := congrArg Additive.ofMul b₂
  replace c' := congrArg Additive.ofMul c'
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow] at a₁ a₂ b₁ b₂ c' ⊢
  linear_combination (norm := module) a₂ - (d ^ 2) • a₁ - c' + b₂ - (d ^ 2) • b₁

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem transport_ext (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) {x' : Y' ⟶ X'} {x : Y ⟶ X}
    {h : Y' ⟶ Y} (hx : x' ≫ F = h ≫ x) {t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => x) (fun _ => 1))} (ht : t.IsGen)
    {a : LB.Gen (LB.LinComb L' (K := Fin 1) (fun _ => x') (fun _ => 1))}
    (H : ∀ z J J', Good L z J → Good L' z J' → wVal w z J J' x' * val a (𝟙 _) z J' = val t h z J)
    {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J J') (hJ : Good L z J) (hJ' : Good L' z J') :
    wVal w z J J' (r ≫ x') * val a r z J' = val t (r ≫ h) z J := by
  obtain ⟨b, -, hb⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x') (h := h) hw hL hL' (fun _ => hx) t ht
  have c : LB.Gen.Corr L' _ _ _ _ a b := corr_of_val hL' fun y I' hI' => by
    obtain ⟨I, hI⟩ := exists_good' hL y
    have e := hb _ (𝟙 _) y I I' hI hI'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp, ← H y I I' hI hI'] at e
    exact mul_left_cancel e
  rw [val_corr hJ' c r, hb _ r z J J' hJ hJ', Fin.prod_univ_one, zpow_one]

theorem exists_square_unit {X₁ X₂ X₃ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {F₁ : X₁ ⟶ X} {F₂ : X₂ ⟶ X}
    {G₁ : X₃ ⟶ X₁} {G₂ : X₃ ⟶ X₂} (e : G₁ ≫ F₁ = G₂ ≫ F₂) (hL : L.IsLB) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (h₃ : L₃.IsLB)
    {w₁ : LB.Iso L₁ (L.pull F₁)} {w₂ : LB.Iso L₂ (L.pull F₂)} {v₁ : LB.Iso L₃ (L₁.pull G₁)} {v₂ : LB.Iso L₃ (L₂.pull G₂)}
    (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) (k₁ : v₁.IsGen) (k₂ : v₂.IsGen) :
    ∃ u : Γ(X₃, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X₃) (z : Z) J J₁ J₂ J₃, Good L z J → Good L₁ z J₁ → Good L₂ z J₂ →
      Good L₃ z J₃ → wVal w₁ z J J₁ (r ≫ G₁) * wVal v₁ z J₁ J₃ r =
        gm r z ⊤ u * (wVal w₂ z J J₂ (r ≫ G₂) * wVal v₂ z J₂ J₃ r) := by
  rw [isGen_iff] at g₁ g₂ k₁ k₂
  obtain ⟨s₁, T₁⟩ := exists_comp h₁ w₁ v₁ g₁ k₁ hL h₃
  obtain ⟨s₂, T₂⟩ := exists_comp h₂ w₂ v₂ g₂ k₂ hL h₃
  have key : ∀ (H H' : X₃ ⟶ X) (_ : H = H') (s : LB.Iso L₃ (L.pull H)) (s' : LB.Iso L₃ (L.pull H')), PGen s → PGen s' →
      ∃ u : Γ(X₃, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X₃) (y : Z) (j : L.ι) (k : L₃.ι), H (r y) ∈ L.U j → r y ∈ L₃.U k →
        Geo.Tor.gw s r y j k = gm r y ⊤ u * Geo.Tor.gw s' r y j k := by
    rintro H _ rfl s s' hs hs'
    exact TrivDescentCompare.exists_iso_ratio hL h₃ ((isGen_iff _).2 hs) ((isGen_iff _).2 hs')
  obtain ⟨u, hu⟩ := key _ _ e s₁ s₂ (T₁.pgen_comp h₁ g₁ k₁) (T₂.pgen_comp h₂ g₂ k₂)
  refine ⟨u, fun Z r z J J₁ J₂ J₃ hJ hJ₁ hJ₂ hJ₃ => ?_⟩
  have e' : (r ≫ G₂) ≫ F₂ = (r ≫ G₁) ≫ F₁ := by rw [Category.assoc, Category.assoc, e]
  have a := T₁ Z r z _ _ _ (hJ ((r ≫ G₁) ≫ F₁)) (hJ₁ (r ≫ G₁)) (hJ₃ r)
  have b := T₂ Z r z _ _ _ (hJ ((r ≫ G₂) ≫ F₂)) (hJ₂ (r ≫ G₂)) (hJ₃ r)
  have c := hu Z r z _ _ (hJ ((r ≫ G₁) ≫ F₁)) (hJ₃ r)
  refine a.symm.trans (c.trans (congrArg (_ * ·) (Eq.trans ?_ b)))
  rw [e']

end General

theorem exists_root_ratio {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] {P₁ : PolAV (Sp R₁)}
    {P₂ : PolAV (Sp R₂)} {f : Sp R₂ ⟶ Sp R₁} {φ : P₂.A.left ⟶ P₁.A.left} (gp : IsGrpPullback P₂.A P₁.A f φ)
    {w : LB.Iso P₂.L (P₁.L.pull φ)} (hw : w.IsGen) {rig₁ : LB.Gen (P₁.L.pull (eSec P₁.A))} (h₁ : rig₁.IsGen)
    {rig₂ : LB.Gen (P₂.L.pull (eSec P₂.A))} (h₂ : rig₂.IsGen) {n d : ℕ} (hn : 0 < n * d) {ζ : R₂}
    (hζ : IsPrimitiveRoot ζ ((n * d) ^ 2)) : ∃ u : R₂ˣ,
    ∀ (x₁ : baseOver (Sp R₁) ⟶ P₁.A) (x₂ : baseOver (Sp R₂) ⟶ P₂.A) τ₁ τ₂, x₂.left ≫ φ = f ≫ x₁.left →
      IsTorsFrame P₁ rig₁ n x₁ τ₁ → IsTorsFrame P₂ rig₂ (n * d) x₂ τ₂ → ∃ k : ℕ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver (Sp R₂)).left) (z : Z) J J', Good P₁.L z J → Good P₂.L z J' →
        (wVal w z J J' (r ≫ x₂.left) * val τ₂ r z J').val =
          gs r z ⊤ (fn (u * ζ ^ k)) * (val τ₁ (r ≫ (f : (baseOver (Sp R₂)).left ⟶ (baseOver (Sp R₁)).left)) z J).val := by
  have : IsLocallyNoetherian (Sp R₂) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R₂)))
  obtain ⟨rig', hrig', Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P₂.A) (φ := fun _ => eSec P₁.A)
    (ε := fun _ => 1) (h := f) hw P₁.isLB P₂.isLB (fun _ => PolBaseChange.eSec_comm gp) rig₁ h₁
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R₂))).left) (z : Z) J J', Good P₁.L z J → Good P₂.L z J' →
      rval rig₁ (r ≫ f) z J = wVal w z J J' (r ≫ eSec P₂.A) * rval rig' r z J' := fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  obtain ⟨u, hu⟩ := CommutatorPairing.exists_ratio (K := PUnit) (K' := PUnit) (φ := fun _ => eSec P₂.A)
    (φ' := fun _ => eSec P₂.A) (ε := fun _ => 1) (ε' := fun _ => 1) P₂.isLB (fun _ _ _ => rfl) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (fun a => ⟨a, by simp⟩) h₂ hrig'
  let E : Γ((baseOver (Sp R₂)).left, ⊤) ≃+* R₂ := (Scheme.ΓSpecIso (CommRingCat.of R₂)).commRingCatIsoToRingEquiv
  let E' : Γ((baseOver (Sp R₂)).left, ⊤)ˣ →* R₂ˣ := Units.map E.toRingHom.toMonoidHom
  refine ⟨E' u, fun x₁ x₂ τ₁ τ₂ hx H₁ H₂ => ?_⟩
  obtain ⟨τ', hτ', Hτ⟩ := exists_gen_through (φ' := fun _ : Fin 1 => x₂.left)
    (h := (f : (baseOver (Sp R₂)).left ⟶ (baseOver (Sp R₁)).left)) hw P₁.isLB P₂.isLB (fun _ => hx) τ₁ H₁.2.1
  have H' : IsTorsFrame P₂ rig' n x₂ τ' := isTorsFrame_move gp hw hr hx H₁ hτ' fun z J J' hJ hJ' => by
    have := Hτ _ (𝟙 _) z J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this
  obtain ⟨v, hv⟩ := CommutatorPairing.exists_ratio P₂.isLB (fun _ _ _ => rfl) (𝟙 _) (𝟙 _)
    (Category.id_comp _) (fun a => ⟨a, by simp⟩) H₂.2.1 hτ'
  have e : v ^ ((n * d) ^ 2) = (show Γ((baseOver (Sp R₂)).left, ⊤)ˣ from u) ^ ((n * d) ^ 2) := unit_ext fun y _ => by
    obtain ⟨J, hJ⟩ := exists_good' P₂.isLB y
    have a := torsFrame_ratio_pow H' H₂ y J hJ
    have b : rval rig₂ (baseOver (Sp R₂)).hom y J = rval rig' (baseOver (Sp R₂)).hom y J * gm (𝟙 _ ≫ 𝟙 _) y ⊤ u :=
      hu _ (𝟙 _) y J hJ
    rw [hv _ _ y J hJ, b, mul_inv_cancel_comm, mul_inv_cancel_comm, Category.id_comp] at a
    rw [map_pow, map_pow]
    exact a.trans (congrArg (fun q => gm q y ⊤ u ^ ((n * d) ^ 2)) (Category.id_comp (𝟙 (Sp R₂))))
  have e' : ((E' v * (E' u)⁻¹ : R₂ˣ) : R₂) ^ ((n * d) ^ 2) = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← map_pow, ← map_pow, e, mul_inv_cancel, Units.val_one]
  have : NeZero ((n * d) ^ 2) := ⟨pow_ne_zero _ hn.ne'⟩
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one e'
  have hv' : fn ((E' u : R₂) * ζ ^ k) = v.val := by
    rw [hk, ← Units.val_mul, mul_comm, inv_mul_cancel_right]
    exact E.symm_apply_apply v.val
  refine ⟨k, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hv', Hτ Z r z J J' hJ hJ', hv Z r z J' hJ', Fin.prod_univ_one, zpow_one, Category.comp_id, gs_unit r z ⊤ trivial,
    ← Units.val_mul, ← _root_.mul_assoc, mul_comm]

theorem tfk_hom (V : Type) [CommRing V] [IsDomain V] : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := Spec.map_id _

end GlobalTheory.GSep.TowerFrames

namespace GlobalTheory.GSep

open TowerFrames GlobalTheory.ConstFam GlobalTheory.FrameMove

theorem exists_frPull_tower : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (t' : X' → V')
      (δ' : I → X' → X') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  intro I X₁ act 𝔗
  have := X₁.ar.ded
  have := 𝔗.X₂.ar.ded
  have : IsNoetherianRing 𝔗.X₂.o₁ := by
    have := 𝔗.X₂.ar.ft
    exact Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsNoetherianRing 𝔗.X₂.S.R := isNoetherianRing_of_fg 𝔗.X₂.S.fg
  obtain ⟨w₀, hw₀⟩ := 𝔗.lb
  have hζ : IsPrimitiveRoot (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R)
      ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := by
    rw [← 𝔗.lev]
    exact IsPrimitiveRoot.of_map_of_injective (f := 𝔗.X₂.S.R.val) (𝔗.X₂.S.prim.map_of_injective 𝔗.X₂.ar.inj)
      Subtype.val_injective
  have hn : 0 < X₁.S.r * X₁.S.N * 𝔗.d :=
    Nat.mul_pos (Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)) 𝔗.d_pos
  obtain ⟨u, hu⟩ := exists_root_ratio 𝔗.cart hw₀ X₁.ρ.rig_gen 𝔗.X₂.ρ.rig_gen hn hζ
  choose k hk using fun b => hu _ _ _ _ (𝔗.lam_pt b) (X₁.ρ.fr_tors b) (by
    rw [← 𝔗.lev]; exact 𝔗.X₂.ρ.fr_tors (𝔗.lam b))
  refine ⟨k, ?_⟩
  intro z₁ z₂ _ V _ _ _ ev X _ t δ 𝔪 V' _ _ _ io f _ ev₂ X' _ t' δ' 𝔪₂ ψ w hw _ hy gp hφ x fr hx hfr x₂ fr₂ hx₂ hfr₂
  obtain ⟨a, ha⟩ := exists_square_unit hφ.symm X₁.ρ.P.isLB 𝔪.A.isLB 𝔗.X₂.ρ.P.isLB 𝔪₂.A.isLB 𝔪.wl_gen hw₀ hw 𝔪₂.wl_gen
  obtain ⟨a₀, ha₀⟩ := (GlobalTheory.abelianSchemeLaws_all.1.globalFns _ 𝔪₂.A.A 𝔪₂.A.isAb).2 a.val
  obtain ⟨c₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V'))).inv).2 a₀
  have hc : ∀ (p : TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A) z,
      (gm p.left z ⊤ a).val = GlobalTheory.UT.cst (R := V') (FractionRing V') z c₀ := fun p z => by
    refine (gs_unit _ z ⊤ trivial a).symm.trans ((congrArg (gs p.left z ⊤) ha₀.symm).trans
      ((gs_pull p.left 𝔪₂.A.A.hom z ⊤ trivial _).trans ?_))
    rw [Over.w p, tfk_hom]
    rfl
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    let z : (TFK (R := V') (FractionRing V')).left := (⊥ : PrimeSpectrum (FractionRing V'))
    refine (gm (1 : TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A).left z ⊤ a).ne_zero ((hc 1 z).trans ?_)
    exact (gs_eq (𝟙 _) z ⊤ trivial _).trans (by simp only [map_zero])
  refine ⟨Units.mk0 c₀ hc₀ * Units.map 𝔪₂.yK.toMonoidHom u, fun b z J J' hJ hJ' => ?_⟩
  obtain ⟨J₁, hJ₁⟩ := exists_good' X₁.ρ.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := exists_good' 𝔗.X₂.ρ.P.isLB z
  have hs : spMap 𝔪₂.yK ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, hy]
  have hp : (x₂ (𝔗.lam b)).left ≫ ψ =
      (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) ≫ (x b).left := by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · have e₁ : ((x₂ (𝔗.lam b)).left ≫ ψ) ≫ 𝔪.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left ≫ 𝔗.φ := by
        rw [Category.assoc, ← hφ, ← Category.assoc, hx₂]
        exact Category.assoc _ _ _
      refine e₁.trans ((congrArg (_ ≫ ·) (𝔗.lam_pt b)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hs).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hx b).symm).trans
          (Category.assoc _ _ _).symm)))))
    · rw [Category.assoc, Category.assoc, gp.1.w, Over.w (x b), ← Category.assoc, Over.w (x₂ _), tfk_hom, tfk_hom]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have q₁ := transport_ext X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.wl_gen (hx b) (X₁.ρ.fr_tors b).2.1 (hfr b).2
    (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) z J₁ J hJ₁ hJ
  have q₂ : wVal 𝔪₂.wl z J₂ J' (x₂ (𝔗.lam b)).left * _ = _ := (hfr₂ (𝔗.lam b)).2 z J₂ J' hJ₂ hJ'
  have q₃ := hk b _ (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK)
    z J₁ J₂ hJ₁ hJ₂
  have q₄ := ha _ (x₂ (𝔗.lam b)).left z J₁ J J₂ J' hJ₁ hJ hJ₂ hJ'
  rw [← hp] at q₁
  have q₅ := (congrArg (fun q => val (X₁.ρ.fr b) q z J₁) hs).trans q₁.symm
  have q₆ := congrArg (fun q => wVal w₀ z J₁ J₂ q) (hx₂ (𝔗.lam b))
  have q₇ := ((congrArg₂ (fun s t => (s * t).val) q₆ q₂).trans q₃).trans
    (congrArg₂ (fun s t => s * Units.val t) (gs_spMap 𝔪₂.yK z _) q₅)
  have m : ∀ s t, GlobalTheory.UT.cst (R := V') (FractionRing V') z (s * t) =
      GlobalTheory.UT.cst (R := V') (FractionRing V') z s * GlobalTheory.UT.cst (R := V') (FractionRing V') z t := fun s t =>
    (congrArg (gs _ z ⊤) (map_mul _ _ _)).trans (gs_mul _ z ⊤ trivial _ _)
  have m' : GlobalTheory.UT.cst (R := V') (FractionRing V') z (((Units.mk0 c₀ hc₀ * Units.map 𝔪₂.yK.toMonoidHom u :
      (FractionRing V')ˣ) : FractionRing V') *
        𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) = _ * _ :=
    (congrArg _ (by rw [map_mul, map_pow, Units.val_mul, _root_.mul_assoc]; rfl)).trans (m c₀
      (𝔪₂.yK (u * ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b)))
  have key : ∀ {O : Type} [CommRing O] (Wl W W₀ W₂ A F F₂ : Oˣ) (C U : O), Wl * W = A * (W₀ * W₂) → A.val = C →
      (W₀ * (W₂ * F₂)).val = U * (Wl * F).val → W.val * F₂.val = C * U * F.val := by
    intro O _ Wl W W₀ W₂ A F F₂ C U h₁ h₂ h₃
    refine (Units.mul_right_inj Wl).1 ?_
    replace h₁ := congrArg Units.val h₁
    simp only [Units.val_mul] at h₁ h₃
    rw [← h₂]
    linear_combination F₂.val * h₁ + A.val * h₃
  exact (key _ _ _ _ _ _ _ _ _ q₄ (hc _ z) q₇).trans (congrArg (· * _) m'.symm)

end GlobalTheory.GSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTowerFramesPullbackConstantRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tower_frames_pullback_constant_root : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (t' : X' → V')
      (δ' : I → X' → X') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  first | exact @GlobalTheory.GSep.exists_frPull_tower | exact GlobalTheory.GSep.exists_frPull_tower | (intros; apply GlobalTheory.GSep.exists_frPull_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerThetaMemberTermsBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.GSep.BaseTerms

theorem terms_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  intro I X₁ act 𝔗 z₁ z₂ hp x₀ hdiv
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_tower_frames_pullback_constant_root X₁ act 𝔗
  set M := (𝔗.X₂.S.r * 𝔗.X₂.S.N) ^ 2 with hM
  refine ⟨fun b => k x₀ + (M - 1) * k b, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab T hT V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart hw hφ hmon hU he₈ hgen zt hzt
  obtain ⟨x, fr, th, w₀, s, g', w, h1, h2, h3, h4, h5, h6, h7⟩ := hT
  obtain ⟨wψ, hwψ⟩ := hw
  obtain ⟨x₂, fr₂, h1', h2'⟩ := GlobalTheory.T.exists_torsionPoints_transported_frames 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ 𝔪₂
  obtain ⟨c₀, hc₀⟩ := hk z₁ z₂ hp V ev X t δ 𝔪 V' io f hf ev₂ X (fun k => io (t k)) δ 𝔪₂ ψ wψ hwψ hExt hyK hcart hφ
    x fr h1 h2 x₂ fr₂ h1' h2'
  set ζ' : FractionRing V' := 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ with hζ'
  have hζM : ζ' ^ M = 1 := by
    rw [hζ', ← map_pow]
    have : (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R) ^ M = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hM, 𝔗.X₂.S.prim.pow_eq_one, map_one]
    rw [this, map_one]
  have hMpos : M ≠ 0 := by
    rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := 𝔗.X₂.S.r_pos; omega) (by have := 𝔗.X₂.S.N_ge; omega))
  have hζ0 : ζ' ≠ 0 := by
    intro h0
    rw [h0, zero_pow hMpos] at hζM
    exact zero_ne_one hζM
  let ρ : X₁.S.Gam → (FractionRing V')ˣ := fun b => c₀ * (Units.mk0 ζ' hζ0) ^ k b
  have hρ : ∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b) := by
    intro b
    simpa [ρ] using hc₀ b
  obtain ⟨th₂, w₀₂, s₂, g'₂, w₂, K, h3', h4', h5', h6', hcoef, hval⟩ := GlobalTheory.T.termsWitnesses_baseChange_along_tower X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V ev X t δ 𝔪 C lab
    x fr th w₀ s g' w h1 h2 h3 h4 h5 h6 V' io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen
    x₂ fr₂ h1' h2' ρ hρ
  refine ⟨x₂, fr₂, th₂, w₀₂, s₂, g'₂, w₂, h1', h2', h3', h4', h5', h6', ?_⟩
  intro mu c
  have hz : algebraMap V' (FractionRing V') (ev₂ zt) = ζ' := by
    haveI : IsLocalHom ev₂ := 𝔪₂.loc
    rw [← GlobalTheory.GSep.TwistModel.val_stalkHom (X₁ := 𝔗.X₂) (z₁ := z₂) (V := V') (ev := ev₂) zt, hzt, hζ', 𝔪₂.yK_eq]
  have hF0 : f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) ≠ 0 :=
    (map_ne_zero_iff f f.injective).2 (GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hdiv)
  have hρc : (ρ (lab c) : FractionRing V') ≠ 0 := (ρ (lab c)).ne_zero
  have e1 := hcoef mu c
  have e2 := hval x₀
  have e3 := h7 mu c
  have eρ : (ρ x₀ : FractionRing V') = ρ (lab c) * ζ' ^ (k x₀ + (M - 1) * k (lab c)) := by
    simp only [ρ, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [_root_.mul_assoc, ← pow_add]
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 hMpos
    have hsum : (M - 1) * k (lab c) + k (lab c) = M * k (lab c) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM1]
    rw [show k (lab c) + (k x₀ + (M - 1) * k (lab c)) = k x₀ + ((M - 1) * k (lab c) + k (lab c)) by ring, hsum,
      pow_add, pow_mul, hζM, one_pow, _root_.mul_one]
  have e3' : f (coef s (g' c) (w c) (𝔪.e₈ mu)) =
      algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) := by
    rw [← e3, map_mul, hf]
  show algebraMap V' (FractionRing V') (ev₂ zt ^ (k x₀ + (M - 1) * k (lab c)) * io (T mu c)) *
    𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩ = coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu)
  rw [map_mul, map_pow, hz]
  apply mul_right_cancel₀ (mul_ne_zero hρc hF0)
  linear_combination (-(algebraMap V' (FractionRing V') (io (T mu c))) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) *
      𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩) * eρ +
    (algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) * e2 -
    f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e1 - K * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e3'

end GlobalTheory.GSep.BaseTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTowerThetaMemberTermsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisTower_thetaMember_terms_baseChange : ∀ {I : Type} (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  first | exact @GlobalTheory.GSep.BaseTerms.terms_baseChange | exact GlobalTheory.GSep.BaseTerms.terms_baseChange | (intros; apply GlobalTheory.GSep.BaseTerms.terms_baseChange <;> assumption)
end
