module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.CxPts Topology Set

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isRatSec_tens {A B : LB Z} {r : A.ι → Z.functionFieldˣ} {s : B.ι → Z.functionFieldˣ}
    (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem div_tens (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ} {s : N.B.ι → Z.functionFieldˣ}
    (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).div (isRatSec_tens hr hs) = M.div hr + N.div hs :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨a, ha⟩ := exists_chart M.isLB z
    obtain ⟨b, hb⟩ := exists_chart N.isLB z
    exact ⟨_, (presents_divOfRatSec (M.tens N).isLB (isRatSec_tens hr hs)).isEqn (a, b) z ⟨ha, hb⟩,
      ((presents_divOfRatSec M.isLB hr).isEqn a z ha).add ((presents_divOfRatSec N.isLB hs).isEqn b z hb)⟩

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem curveDeg_tens [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ}
    {s : N.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).curveDeg (isRatSec_tens hr hs) = M.curveDeg hr + N.curveDeg hs := by
  have := hZ.isNoetherian
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have h₂ (σ) (y : CxPts q σ) : logNorm ((M.tens N).φ σ) (fun c : M.B.ι × N.B.ι => r c.1 * s c.2) y =
      logNorm (M.φ σ) r y + logNorm (N.φ σ) s y := by
    have hy : under y = genericPoint Z := hZ.under_eq_genericPoint y
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have ha := mem_pick (M.φ σ).isLB y
    have hb := mem_pick (N.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    refine (logNorm_eq ((M.tens N).φ σ) (isRatSec_tens hr hs) (ho _) (i := (pick (M.φ σ).isLB y, pick (N.φ σ).isLB y))
      (mem_ptsIn_inf.2 ⟨ha, hb⟩)).trans ?_
    change Real.log ‖ratVal ((r (pick (M.φ σ).isLB y) * s (pick (N.φ σ).isLB y) : Z.functionFieldˣ) : Z.functionField) y‖ -
      ((M.φ σ).φ (pick (M.φ σ).isLB y) y + (N.φ σ).φ (pick (N.φ σ).isLB y) y) / 2 = _
    rw [logNorm, logNorm, Units.val_mul,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), norm_mul, Real.log_mul (hu _) (hu _)]
    ring
  have := SmallSecHeight.numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (SmallSecHeight.ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  unfold HermLB.curveDeg
  rw [div_tens M N hr hs]
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  rw [finsum_add_distrib (hfin _) (hfin _)]
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem height_tens (hX : IsArithVar p D) {L M : HermLB p} {h h' h'' : X → ℝ} (H : L.IsArithHeight h)
    (H' : M.IsArithHeight h') (H'' : (L.tens M).IsArithHeight h'') {x : X} (hx : IsAlgPt x) :
    h'' x = h x + h' x := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨s, hs⟩ := exists_isRatSec (M.restr i).isLB
  obtain ⟨t, ht, h₁, h₂⟩ := (HermLB.isometric_pull_tens (L := L) (M := M) i rfl).symm.exists_isRatSec
    (isRatSec_tens hr hs)
  rw [H''.point Z i hcΓ hd t ht, H.point Z i hcΓ hd r hr, H'.point Z i hcΓ hd s hs,
    ← curveDeg_tens hZ hc' (L.restr i) (M.restr i) hr hs, HermLB.curveDeg, h₁]
  refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h₂ σ (mem_offSupp.2 ?_))
  rw [hZ.under_eq_genericPoint]
  exact CartierDiv.genericPoint_notMem_supp _

end GlobalTheory.PtHtComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut LevelMod)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev pullG (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) : Over X' :=
  (Over.pullback (φ ≫ (barComp TF.Y Z).ι)).obj TF.Y.t.G

abbrev pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    (pullG TF Z φ).left ⟶ TF.Y.t.G.left :=
  pullback.fst _ _

abbrev pullAct (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    OAct (𝓞 E) (pullG TF Z φ) :=
  OAct.pullback (φ ≫ (barComp TF.Y Z).ι) TF.Y.t.G TF.Y.t.act

instance grpObj_pullG (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    GrpObj (pullG TF Z φ) :=
  inferInstance

theorem isGrpPullback_pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) :
    IsGrpPullback (pullG TF Z φ) TF.Y.t.G (φ ≫ (barComp TF.Y Z).ι) (pullψ TF Z φ) :=
  isGrpPullback_pullback _ _

theorem pullAct_pullψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (a : 𝓞 E) :
    ((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ = pullψ TF Z φ ≫ (TF.Y.t.act.act a).left :=
  pullback.lift_fst _ _ _

variable {Γ : Type} [Group Γ]

def IsEqvAct {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X') [GrpObj G'] (act' : OAct (𝓞 E) G')
    (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  (∀ γ, IsGrpPullback G' G' (ρ' γ).asIso.hom (m γ)) ∧ (∀ γ a, (act'.act a).left ≫ m γ = m γ ≫ (act'.act a).left) ∧
    ∀ γ₁ γ₂, m (γ₁ * γ₂) = m γ₂ ≫ m γ₁

def MovesEta (TF : TorFlag Xo c) (Z : Comp Xo c) (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z))
    {X' : Scheme.{0}} (ℓ : V₀ TF.Y Z ⟶ X') (G' : Over X') (ψ : G'.left ⟶ TF.Y.t.G.left)
    (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  ∀ (γ : Γ) (a b : Dw.La), (Submodule.Quotient.mk b : LevelMod Dw l) = (ι γ)⁻¹ (Submodule.Quotient.mk a) →
    ∀ w w' : V₀ TF.Y Z ⟶ G'.left, w ≫ G'.hom = ℓ → w' ≫ G'.hom = ℓ →
      w ≫ ψ = i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ →
      w' ≫ ψ = i₀ TF.Y Z ≫ (TF.Y.oF.eta a).left ≫ TF.Y.m.φ →
      w ≫ m γ = (ρ γ).asIso.hom ≫ w'

def IsTorsI (I : Ideal (𝓞 E)) {X' : Scheme.{0}} {G' : Over X'} [GrpObj G'] (act' : OAct (𝓞 E) G') {T : Over X'}
    (P : T ⟶ G') : Prop :=
  ∀ a ∈ I, P ≫ act'.act a = 1

def TorsLevel (I : Ideal (𝓞 E)) (ι : Γ →* LevelAut Dw l) {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X')
    [GrpObj G'] (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X'), ∃ e : (Over.mk t ⟶ G') → LevelMod Dw l,
    (∀ P Q, IsTorsI I act' P → IsTorsI I act' Q → e (P * Q) = e P + e Q) ∧
    (∀ P (a : 𝓞 E), IsTorsI I act' P → e (P ≫ act'.act a) = a • e P) ∧
    (∀ P Q, IsTorsI I act' P → IsTorsI I act' Q → e P = e Q → P = Q) ∧
    ∀ γ, t ≫ (ρ' γ).asIso.hom = t → ∀ P Q : Over.mk t ⟶ G', IsTorsI I act' P → Q.left = P.left ≫ m γ →
      e Q = ι γ (e P)

end GlobalTheory.EqvAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Obj.toSieg {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    SiegPre h M ζ t₁ where
  A := o.A
  ab := o.ab
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  lev := lev
  lev_add := hl.1
  lev_tors := hl.2.1
  geom := hl.2.2

theorem Obj.toSieg_ample {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B]
    {ζ : B} {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    Out.RelAmple (o.toSieg hl).A (o.toSieg hl).diag := o.ample

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CombForm

section Atlas

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def tAtlas (A : FinHolAtlas e X) (h : X ≃ₜ X') : FinHolAtlas e X' where
  n := A.n
  chart j := h.symm.transOpenPartialHomeomorph (A.chart j)
  cover x := (A.cover (h.symm x)).imp fun _ hj => hj
  holo j k := by
    have e₁ : (h.symm.transOpenPartialHomeomorph (A.chart k)) ∘ (h.symm.transOpenPartialHomeomorph (A.chart j)).symm =
        A.chart k ∘ (A.chart j).symm := funext fun y => by simp
    have e₂ : (h.symm.transOpenPartialHomeomorph (A.chart j)).target ∩
        (h.symm.transOpenPartialHomeomorph (A.chart j)).symm ⁻¹' (h.symm.transOpenPartialHomeomorph (A.chart k)).source =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
      ext y; simp
    rw [e₁, e₂]
    exact A.holo j k

theorem tAtlas_symm (A : FinHolAtlas e X) (h : X ≃ₜ X') (j : Fin (tAtlas A h).n) (y : Fin e → ℂ) :
    ((tAtlas A h).chart j).symm y = h ((A.chart j).symm y) := rfl

end Atlas

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

section Met

variable {σ : F →+* ℂ} {Δ : Y.Dv}

end Met

end GlobalTheory.Mean4O.CombForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

def lo : Localization.Away P'.f →+* O := IsLocalization.Away.lift P'.f hu

theorem lo_comp : (lo P' x0 hu).comp (algebraMap R _) = x0 := IsLocalization.Away.lift_comp _ _

@[nolint unusedArguments]
def OL (_P : GlobalTheory.HTMap.FP t ξ q) (_x : R →+* O) (_h : IsUnit (_x _P.f)) : Type := O

instance : CommRing (OL P' x0 hu) := inferInstanceAs (CommRing O)

instance : Algebra O (OL P' x0 hu) := inferInstanceAs (Algebra O O)

instance : Algebra (Localization.Away P'.f) (OL P' x0 hu) := (lo P' x0 hu).toAlgebra

instance : SMulCommClass (Localization.Away P'.f) O (OL P' x0 hu) :=
  ⟨fun a b c => @mul_left_comm O _ (lo P' x0 hu a) b c⟩

abbrev Bt : Type := OL P' x0 hu ⊗[Localization.Away P'.f] P'.B

def inB : P'.B →+* Bt P' x0 hu :=
  (Algebra.TensorProduct.includeRight : P'.B →ₐ[Localization.Away P'.f] Bt P' x0 hu).toRingHom

theorem inB_str : (inB P' x0 hu).comp P'.str = (algebraMap O (Bt P' x0 hu)).comp x0 := by
  refine RingHom.ext fun r => ?_
  change (Algebra.TensorProduct.includeRight : P'.B →ₐ[Localization.Away P'.f] Bt P' x0 hu)
    (algebraMap (Localization.Away P'.f) P'.B (algebraMap R _ r)) = algebraMap O (Bt P' x0 hu) (x0 r)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
  congr 1
  exact RingHom.congr_fun (lo_comp P' x0 hu) r

abbrev Hs : Over (Sp O) := specO O (Bt P' x0 hu)

theorem sq : (spMap (inB P' x0 hu) ≫ P'.u.left) ≫ t.G.hom = spMap (algebraMap O (Bt P' x0 hu)) ≫ spMap x0 ≫ ξ := by
  rw [Category.assoc, GlobalTheory.HTMap.over_w P'.u, GlobalTheory.HTMap.spc_assoc, GlobalTheory.HTMap.spc_assoc, GlobalTheory.HTMap.spc_assoc]
  congr 1
  rw [← inB_str P' x0 hu]
  rfl

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

def aH (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Hs P' x0 hu ⟶ G' :=
  Over.homMk (hπ.lift _ _ (sq P' x0 hu)) (hπ.lift_snd _ _ _)

theorem aH_left_π (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) :
    (aH P' x0 hu hπ).left ≫ π = spMap (inB P' x0 hu) ≫ P'.u.left := hπ.lift_fst _ _ _

def jH [GrpObj G'] (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) (h : aH P' x0 hu hπ ^ q = 1) :
    Hs P' x0 hu ⟶ torsion G' q :=
  GlobalTheory.KernelNoTorsion.torsionLift _ h

theorem jH_ι [GrpObj G'] (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) (h : aH P' x0 hu hπ ^ q = 1) :
    jH P' x0 hu hπ h ≫ torsion.ι G' q = aH P' x0 hu hπ :=
  GlobalTheory.KernelNoTorsion.torsionLift_ι _ h

def liftB {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D) (hβ : β.comp P'.str = (algebraMap O D).comp x0) :
    Bt P' x0 hu →ₐ[O] D :=
  letI : Algebra (Localization.Away P'.f) D := ((algebraMap O D).comp (lo P' x0 hu)).toAlgebra
  have e : β.comp (algebraMap (Localization.Away P'.f) P'.B) = algebraMap (Localization.Away P'.f) D :=
    IsLocalization.ringHom_ext (Submonoid.powers P'.f) (by
      rw [RingHom.comp_assoc]
      refine hβ.trans ?_
      change _ = (algebraMap O D).comp ((lo P' x0 hu).comp (algebraMap R _))
      rw [lo_comp])
  let f : OL P' x0 hu →ₐ[Localization.Away P'.f] D :=
    { (algebraMap O D : O →+* D) with commutes' := fun _ => rfl }
  let F : Bt P' x0 hu →ₐ[Localization.Away P'.f] D :=
    Algebra.TensorProduct.lift f { β with commutes' := fun r => RingHom.congr_fun e r } fun _ _ => Commute.all _ _
  { F.toRingHom with
    commutes' := fun c => by
      change F (algebraMap O (Bt P' x0 hu) c) = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl }

theorem liftB_inB {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D)
    (hβ : β.comp P'.str = (algebraMap O D).comp x0) (z : P'.B) : liftB P' x0 hu β hβ (inB P' x0 hu z) = β z := by
  simp [liftB, inB]

def ptOf {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D) (hβ : β.comp P'.str = (algebraMap O D).comp x0) :
    specO O D ⟶ Hs P' x0 hu :=
  ptMap (liftB P' x0 hu β hβ)

theorem ptOf_aH_π {D : Type} [CommRing D] [Algebra O D] (β : P'.B →+* D)
    (hβ : β.comp P'.str = (algebraMap O D).comp x0) (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) :
    (ptOf P' x0 hu β hβ ≫ aH P' x0 hu hπ).left ≫ π = spMap β ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π, ← Category.assoc]
  change spMap (liftB P' x0 hu β hβ).toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]
  congr 2
  exact RingHom.ext fun z => liftB_inB P' x0 hu β hβ z

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem alg_dual_mk {O : Type} [CommRing O] (I : Ideal O) :
    (algebraMap (O ⧸ I) (DualNumber (O ⧸ I))).comp (Ideal.Quotient.mk I) = algebraMap O (DualNumber (O ⧸ I)) :=
  RingHom.ext fun r => TrivSqZeroExt.ext rfl rfl

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem dualBC_eq {O : Type} [CommRing O] (I : Ideal O) :
    (dualBC (Algebra.ofId O (O ⧸ I))).toRingHom = dualMap (Ideal.Quotient.mk I) := by
  refine RingHom.ext fun z => ?_
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), dualBC, TrivSqZeroExt.lift_apply_inl,
    TrivSqZeroExt.lift_apply_inr]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap] <;> rfl

theorem ptMap_dualBC_left {O : Type} [CommRing O] (I : Ideal O) :
    (ptMap (dualBC (Algebra.ofId O (O ⧸ I)))).left = spMap (dualMap (Ideal.Quotient.mk I)) := by
  change Spec.map (CommRingCat.ofHom (dualBC (Algebra.ofId O (O ⧸ I))).toRingHom) = _
  rw [dualBC_eq]

theorem cmp_of_corr {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
    [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : GlobalTheory.HTLat.Point p v O Λ) (n : ℕ)
    {x : specO O (DualNumber O) ⟶ P.Gt} {y : specO O (DualNumber O) ⟶ P.G} (h : Corr P x y)
    (hn : IsNilpotent (p : DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) :
    P.cmp _ hn (ptMap (dualBC (Algebra.ofId O (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x) =
      ptMap (dualBC (Algebra.ofId O (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ y := by
  have hz : ∀ a ∈ Ideal.span {(p : DualNumber O) ^ n},
      dualBC (Algebra.ofId O (O ⧸ Ideal.span {(p : O) ^ n})) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast]
    have h0 : (p : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})) ^ n = 0 := by
      rw [← map_natCast (algebraMap (O ⧸ Ideal.span {(p : O) ^ n}) (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))),
        ← map_pow, ← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_span_singleton_self _), map_zero]
    rw [h0, MulZeroClass.mul_zero]
  have e : (Ideal.Quotient.liftₐ _ _ hz).comp (redR p O (DualNumber O) n) =
      dualBC (Algebra.ofId O (O ⧸ Ideal.span {(p : O) ^ n})) := Ideal.Quotient.liftₐ_comp _ _ _
  rw [← e, ← TangentPow.ptMap_comp_ptMap, Category.assoc, Category.assoc, h n,
    P.cmp_nat _ _ (nilpR n) hn]

end GlobalTheory.FinPartAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNine
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.TwistDeg

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem logSum_bad_le {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) :
    logSum (GlobalTheory.FlatTw.badPrimes H l) ≤ Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' := by
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hd := H.d_prime.ne_zero
  have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hd) hD) hM
  have h0 : ∀ p ∈ (2 * H.d * (discr E).natAbs * l.M').primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : Real.log 2 + Real.log H.d + Real.log |(discr E : ℝ)| + Real.log l.M' =
      Real.log ((2 * H.d * (discr E).natAbs * l.M' : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]
  rw [e, logSum, GlobalTheory.FlatTw.badPrimes, ← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hne) (Nat.prod_primeFactors_dvd _))
  exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

theorem lrd_eq (E : Type) [Field E] [NumberField E] :
    lrd E = Real.log |(discr E : ℝ)| / (Module.finrank ℚ E : ℝ) := by
  have h : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  rw [lrd, rootDiscr_def, Int.cast_abs, Real.log_rpow h, div_eq_inv_mul]

theorem numeric {f r L q a b s c : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hq : q ≤ r)
    (hb0 : 0 ≤ b) (hb : b ≤ 3 * L) (hs0 : 0 ≤ s) (hs : s ≤ 6 * f * r) (hc : |a| ≤ 9 * r * L * s)
    (hB : c ≤ 1 + 2 * b + 2 * f * b + 30 * L) : -(120 * (f * r * L) ^ 2) ≤ a - q * b * s - c := by
  have h1 : q * b * s ≤ r * (3 * L) * (6 * f * r) := by gcongr
  have h2 : 9 * r * L * s ≤ 9 * r * L * (6 * f * r) := by gcongr
  have h3 : f * b ≤ f * (3 * L) := by gcongr
  have h4 : f * r ^ 2 * L ≤ (f * r * L) ^ 2 := by
    rw [show (f * r * L) ^ 2 = f * r ^ 2 * L * (f * L) by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hf hL)
  have h5 : f * L ≤ f * r ^ 2 * L := by
    rw [show f * r ^ 2 * L = f * L * r ^ 2 by ring]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hr)
  have h6 : L ≤ f * L := le_mul_of_one_le_left (by positivity) hf
  have h7 := (abs_le.1 hc).1
  nlinarith

end GlobalTheory.TwistDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

def omegaMod {h : ℕ} (M : ℕ) (x y : Fin h ⊕ Fin h → ZMod M) : ZMod M :=
  ∑ i, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))

def sympSimGrp (h M : ℕ) :
    Subgroup ((Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) where
  carrier := {g | ∃ m : (ZMod M)ˣ, ∀ x y, omegaMod M (g x) (g y) = m * omegaMod M x y}
  one_mem' := ⟨1, fun x y => by simp⟩
  mul_mem' := by
    rintro g g' ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m * m', fun x y => ?_⟩
    change omegaMod M (g (g' x)) (g (g' y)) = _
    rw [hm, hm', Units.val_mul, _root_.mul_assoc]
  inv_mem' := by
    rintro g ⟨m, hm⟩
    refine ⟨m⁻¹, fun x y => ?_⟩
    have hg := hm (g⁻¹ x) (g⁻¹ y)
    have e : ∀ z, g (g⁻¹ z) = z := fun z => by
      change (g * g⁻¹) z = z
      rw [mul_inv_cancel]; rfl
    rw [e, e] at hg
    rw [hg, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

instance sympSimGrp_finite (h M : ℕ) [NeZero M] : Finite (sympSimGrp h M) := by
  haveI : Finite ((Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) :=
    Finite.of_injective (fun g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M) =>
      (g : (Fin h ⊕ Fin h → ZMod M) → (Fin h ⊕ Fin h → ZMod M))) DFunLike.coe_injective
  infer_instance

def reduceMod {h : ℕ} (M : ℕ) (a : Fin h ⊕ Fin h → ℤ) : Fin h ⊕ Fin h → ZMod M := fun i => (a i : ZMod M)

def liftMod {h : ℕ} {M : ℕ} (x : Fin h ⊕ Fin h → ZMod M) : Fin h ⊕ Fin h → ℤ := fun i => ((x i).val : ℤ)

theorem reduceMod_liftMod {h M : ℕ} [NeZero M] (x : Fin h ⊕ Fin h → ZMod M) : reduceMod M (liftMod x) = x := by
  funext i
  simp [reduceMod, liftMod]

def sympTwist {h M : ℕ} {T : Type*} (g : sympSimGrp h M) (l : (Fin h ⊕ Fin h → ℤ) → T) :
    (Fin h ⊕ Fin h → ℤ) → T :=
  fun a => l (liftMod ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M a)))

def IsMultOf {h M : ℕ} (g : sympSimGrp h M) (n : ℕ) : Prop :=
  ∀ x y, omegaMod M ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x)
    ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y) = n * omegaMod M x y

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HarrisTaylorSymplecticLevelFamilyUniversalProperty (b : Base D R) (N h M : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
    (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
    ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

def SympActs {b : Base D R} {N h M : ℕ} {X : Scheme.{0}} (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (ρ : sympSimGrp h M → (X ⟶ X)) : Prop :=
  ∀ a, ρ a ≫ s = s ∧
    (∃ (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n ∧ σ (zetaAway M) = zetaAway M ^ n ∧
      ρ a ≫ s₁ = s₁ ≫ spMap σ) ∧
    ∃ m : ObjMap u u (ρ a), ∀ x, (sympTwist a lev x).left ≫ m.φ = ρ a ≫ (lev x).left

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivOfLam

open GlobalTheory.CechPic

theorem cls_cube_pair {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (x y : T ⟶ A) (h : (cubeLB A ![x, y] L).IsLB) :
    cls _ h = pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
      pull (1 : T ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.ulift.symm.sum_comp]
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := mul_one x
  have p₂ : psum A ![x, y] {1} = y := mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (mul_one y)
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Equiv.ulift_symm_apply, p₀, p₁, p₂, p₃]
  rw [Finset.card_pair (by decide)]
  simp
  abel

theorem pull_eq_zero_of_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i : L.ι)
    (hf : ∀ y, f y ∈ L.U i) : pull f (cls L hL) = 0 :=
  (cls_eq_zero_iff (pull_isLB hL f)).2 (GlobalTheory.IsoExtend.exists_gen_of_chart hL f i hf)

theorem exists_chart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : X) : ∃ i, z ∈ L.U i := by
  have : z ∈ (⊤ : X.Opens) := trivial
  rw [← hL.cover] at this
  exact TopologicalSpace.Opens.mem_iSup.1 this

theorem kTriv_of_lam_iso : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (P : LB (G2 B).left), P.IsLB →
    (∀ (T : Over S) (x : T ⟶ B), (∃ t : (P.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (L : LB B.left), L.IsLB → LBIso (abelian₂ B L) P → KTriv B L := by
  intro S B _ _ _ P hP H L hL hiso R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ B).left fun p => ?_)
  obtain ⟨V, hpV, c₀, hc₀⟩ := hx p
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  obtain ⟨j, hj⟩ := exists_chart hL ((1 : Over.mk t ⟶ B).left p)
  let W : (Spec (CommRingCat.of R)).Opens := V ⊓ x.left ⁻¹ᵁ L.U i ⊓ (1 : Over.mk t ⟶ B).left ⁻¹ᵁ L.U j
  refine ⟨W, ⟨⟨hpV, hi⟩, hj⟩, ?_⟩
  let T₀ : Over S := Over.mk t
  let TW : Over S := Over.mk (W.ι ≫ t)
  let ιW : TW ⟶ T₀ := Over.homMk W.ι rfl
  suffices key : ιW ≫ x = 1 by
    have := congrArg (fun q => q.left) (key.trans (MonObj.comp_one ιW).symm)
    exact this
  refine H TW (ιW ≫ x) ?_
  let c := cls L hL
  have hLam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hTD : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _

  let O : (T₀ ⊗ B).left.Opens := (fst T₀ B).left ⁻¹ᵁ V
  have h₀ : pull O.ι (cls _ hTD) = 0 := (cls_eq_zero_iff (pull_isLB hTD _)).2 ⟨c₀, hc₀⟩
  let N : B ⊗ TW ⟶ T₀ ⊗ B := lift (snd B TW ≫ ιW) (fst B TW)
  have hN : Set.range N.left.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T₀ B).left (N.left z) ∈ V
    have k : N.left ≫ (fst T₀ B).left = (snd B TW).left ≫ W.ι := by rw [← Over.comp_left, lift_fst]; rfl
    rw [← Scheme.Hom.comp_apply, k, Scheme.Hom.comp_apply]
    exact ((snd B TW).left z).2.1.1
  have h₁ : pull N.left (cls _ hTD) = 0 := by
    rw [← IsOpenImmersion.lift_fac O.ι N.left hN, pull_comp, h₀, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B]).left c - pull (snd T₀ B).left c := by
    refine (cls_linComb hL _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, c]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : pull ((snd B TW ≫ ιW ≫ x) * fst B TW).left c = pull (fst B TW).left c := by
    have k₁ : N ≫ lift (fst T₀ B ≫ x) (snd T₀ B) ≫ μ[B] = (snd B TW ≫ ιW ≫ x) * fst B TW := by
      rw [← Category.assoc, comp_lift, ← Category.assoc, lift_fst, lift_snd, Category.assoc]; rfl
    have k₂ : N ≫ snd T₀ B = fst B TW := lift_snd _ _
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₁, k₂] at h₁
    exact sub_eq_zero.1 h₁
  have hcP : cls _ hP = cls _ hLam := ((cls_eq_iff hLam hP).2 hiso).symm
  have hC : cls _ hLam = pull (fst B B * snd B B).left c - pull (fst B B).left c - pull (snd B B).left c +
      pull (1 : G2 B ⟶ B).left c := cls_cube_pair hL (fst B B) (snd B B) hLam
  have e₃ : pull (snd B TW ≫ ιW ≫ x).left c = 0 := by
    rw [Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ x).left i ?_, map_zero]
    intro y
    exact y.2.1.2
  have e₄ : pull (1 : B ⊗ TW ⟶ B).left c = 0 := by
    have k : (1 : B ⊗ TW ⟶ B) = snd B TW ≫ ιW ≫ (1 : T₀ ⟶ B) := by rw [MonObj.comp_one, MonObj.comp_one]
    rw [k, Over.comp_left, pull_comp, pull_eq_zero_of_chart hL (ιW ≫ (1 : T₀ ⟶ B)).left j ?_, map_zero]
    intro y
    exact y.2.2
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  show pull _ (cls _ hP) = 0
  rw [hcP, hC, map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_one,
    e₂, e₃, e₄]
  abel

end GlobalTheory.KTrivOfLam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndex
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.DetImMeas

theorem measurableSet_det_im_pos : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  intro κ _ p q ρ₀
  haveI : BorelSpace (UpqT (p ρ₀) (q ρ₀)) := (GlobalTheory.UpqTopology.upq_lcsc (p ρ₀) (q ρ₀)).2.2.2.2.1
  have hc : Continuous fun g : UpqT (p ρ₀) (q ρ₀) => (UpqT.mat g).det.im :=
    Complex.continuous_im.comp ((continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat)
  have hm : Measurable fun b : (∀ ρ, UpqT (p ρ) (q ρ)) => (UpqT.mat (b ρ₀)).det.im :=
    hc.measurable.comp (measurable_pi_apply ρ₀)
  exact measurableSet_lt measurable_const hm

end GlobalTheory.CovTop.VolUp.DetImMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndexStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_det_im_pos_at_index : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  first | exact @GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos | exact GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos | (intros; apply GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitary
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem countable_inReal_of_numberField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)), Countable (inReal Ψ G Γ) := by
  intro E _ _ _ r Ψ G Γ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Units.val_injective.countable
  have h : ((Γ.map (embGL Ψ r) : Subgroup (Ψ → GL (Fin r) ℂ)) : Set (Ψ → GL (Fin r) ℂ)).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  haveI : Countable (Γ.map (embGL Ψ r)) := h.to_subtype
  refine Function.Injective.countable
    (f := fun x : inReal Ψ G Γ => (⟨x.1.1, x.2⟩ : Γ.map (embGL Ψ r))) ?_
  intro x y hxy
  have h2 : x.1.1 = y.1.1 := Subtype.mk.inj hxy
  exact Subtype.ext (Subtype.ext h2)

end GlobalTheory.CovTop.VolUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)), Countable (inReal Ψ G Γ) := by
  first | exact @GlobalTheory.CovTop.VolUp.countable_inReal_of_numberField | exact GlobalTheory.CovTop.VolUp.countable_inReal_of_numberField | (intros; apply GlobalTheory.CovTop.VolUp.countable_inReal_of_numberField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
noncomputable section

namespace GlobalTheory.UPel.HT.Gen.Unique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    Nonempty (GObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _
     φ₂ := 𝟙 _
     cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
     sq := ⟨by simp, by simp⟩
     act := fun c => by simp
     pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
     eta := fun y => by simp }⟩

private theorem lbIso_pull_comp_of_lbIso {X Y Z : Scheme.{0}} {M : LB X} {P : LB Y} {Q : LB Z} {a : X ⟶ Y} {c : Y ⟶ Z}
    (H₁ : LBIso M (P.pull a)) (H₂ : LBIso P (Q.pull c)) (hM : M.IsLB) (hP : P.IsLB) (hQ : Q.IsLB) :
    LBIso M (Q.pull (a ≫ c)) := by
  have E : LBIso (P.pull a) ((Q.pull c).pull a) := SiegelDescent.lbIso_square hP hQ H₂ rfl
  have F : LBIso ((Q.pull c).pull a) ((Q.pull (a ≫ c)).pull (𝟙 X)) :=
    GlobalTheory.FiniteAmple.lbIso_pull_pull c hQ (g := a) (g' := 𝟙 X) (f' := a ≫ c) (by rw [Category.id_comp])
  have hPa := pull_isLB hP a
  have hQc := pull_isLB hQ (a ≫ c)
  exact LBIso.trans hM hPa hQc H₁ (LBIso.trans hPa (pull_isLB (pull_isLB hQ c) a) hQc E
    (LBIso.trans (pull_isLB (pull_isLB hQ c) a) (pull_isLB hQc (𝟙 X)) hQc F (GlobalTheory.SiegLower.lbIso_pull_id hQc).symm))

theorem gObjMap_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₃ (f ≫ g)) :=
  ⟨{ φ := h₁.φ ≫ h₂.φ
     φ₂ := h₁.φ₂ ≫ h₂.φ₂
     cart := IsGrpPullback.comp h₁.cart h₂.cart
     sq := ⟨by rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc],
       by rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]⟩
     act := fun c => by rw [← Category.assoc, h₁.act c, Category.assoc, h₂.act c, ← Category.assoc]
     pol := lbIso_pull_comp_of_lbIso h₁.pol h₂.pol o₁.isLB o₂.isLB o₃.isLB
     eta := fun y => by rw [← Category.assoc, h₁.eta y, Category.assoc, h₂.eta y, ← Category.assoc] }⟩

end GlobalTheory.UPel.HT.Gen.Unique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolume
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open MeasureTheory
open scoped Pointwise

theorem packing_set_covolume_le :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  intro H _ _ _ ν Γ _
  classical
  by_cases hF : HasFundamentalDomain Γ H ν
  swap
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp [covolume, hF]
    · intro γ _ y hy; exact absurd hy (Set.notMem_empty y)
  · set s := hF.ExistsIsFundamentalDomain.choose with hs_def
    have hs : IsFundamentalDomain Γ s ν := hF.ExistsIsFundamentalDomain.choose_spec
    have hcov : covolume Γ H ν = ν s := by simp [covolume, hF, hs_def]
    obtain ⟨t, hts, htm, hte⟩ := hs.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hsmul : ∀ g : Γ, (g • t : Set H) = (fun y => (g : H)⁻¹ * y) ⁻¹' t := by
      intro g; ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
    have hmeas : ∀ g : Γ, MeasurableSet (g • t : Set H) := by
      intro g; rw [hsmul g]; exact (measurable_const_mul _) htm
    let U : Set H := ⋃ g : {g : Γ // g ≠ 1}, (g.1 • t : Set H)
    have hUm : MeasurableSet U := MeasurableSet.iUnion (fun g => hmeas g.1)
    have hnull : ν (t ∩ U) = 0 := by
      rw [Set.inter_iUnion]
      refine measure_iUnion_null (fun g => ?_)
      have h1 := hs.aedisjoint (Ne.symm g.2 : (1 : Γ) ≠ g.1)
      have h2 : ν ((1 : Γ) • s ∩ g.1 • s) = 0 := h1
      rw [one_smul] at h2
      exact measure_mono_null (Set.inter_subset_inter hts (Set.smul_set_mono hts)) h2
    refine ⟨t \ U, htm.diff hUm, ?_, ?_⟩
    · rw [hcov, ← Set.sdiff_self_inter, measure_sdiff_null hnull]
      exact (measure_congr hte).ge
    · intro γ hγ y hy hγy
      by_contra hne
      have hne' : (⟨γ, hγ⟩ : Γ) ≠ 1 := fun h => hne (congrArg Subtype.val h)
      apply hγy.2
      refine Set.mem_iUnion.2 ⟨⟨⟨γ, hγ⟩, hne'⟩, ?_⟩
      exact ⟨y, hy.1, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPackingSetMeasureGeCovolumeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_packingSet_measure_ge_covolume : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  first | exact @GlobalTheory.packing_set_covolume_le | exact GlobalTheory.packing_set_covolume_le | (intros; apply GlobalTheory.packing_set_covolume_le <;> assumption)
end
end
