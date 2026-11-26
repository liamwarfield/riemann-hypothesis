module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PCoverInv
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pull_eq_of_eq {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

private theorem splits_inv (hSP : SplitsPts) {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsIso s] :
    Splits s (𝟙 Z) (fun _ : Unit => inv s) := by
  refine hSP s (𝟙 Z) Unit _ (fun _ => by simp) ?_
  intro Ω _ _ x y hxy
  refine ⟨(), ?_, fun _ _ => rfl⟩
  rw [← cancel_mono s, hxy]
  simp

theorem UpperTheory.Gal.G3.pCoverInv :
    GalInv.{u} → SplitsPts → CoverInv.{u} := by
  intro hGal hSP k L O _ _ _ _ H θ C hC R _ _ T hT
  have hG := C.isGalois hC
  have ha : ∀ δ, C.a δ ≫ H.q = H.q := by
    intro δ
    obtain ⟨hspl, -⟩ := hG.2.2.2.2.2
    rw [← piK_snd C, ← Category.assoc]
    exact congrArg (· ≫ pullback.snd C.p (gen O k)) (hspl δ)
  refine ⟨hT.inj _ _ (piK C) (piK_snd C) C.Δ C.a hG, fun y hy => ?_⟩
  refine (hGal T hT _ _ (piK C) (piK_snd C) C.Δ C.a ha hG y).2 (fun δ => ?_)
  obtain ⟨g, hiso, hts, hθ⟩ := C.fix δ
  haveI := hiso
  obtain ⟨tr, htr, hfix⟩ := hy g hiso hθ
  have hq : inv (H.s g) ≫ (H.s g ≫ H.q) = H.q := by simp
  have key : ∀ z, tr z = T.pull (inv (H.s g)) hq z := by
    intro z
    have := htr H.Z H.q (𝟙 _) (by simp) Unit (fun _ => inv (H.s g)) (fun _ => hq)
      (splits_inv hSP (H.s g)) z
    rw [T.pull_id] at this
    simpa using this
  have h1 : (H.s g ≫ C.a δ) ≫ H.q = H.s g ≫ H.q := by rw [Category.assoc, ha]
  have h2 : (inv (H.s g) ≫ H.s g) ≫ H.q = H.q := by simp
  have h3 : 𝟙 H.Z ≫ H.q = H.q := by simp
  conv_rhs => rw [← hfix]
  rw [key]
  symm
  calc T.pull (inv (H.s g)) hq (T.pull (H.t g) (H.comm g) y)
      = T.pull (inv (H.s g)) hq (T.pull (H.s g ≫ C.a δ) h1 y) :=
        congrArg _ (pull_eq_of_eq T hts _ h1 y)
    _ = T.pull (inv (H.s g)) hq (T.pull (H.s g) rfl (T.pull (C.a δ) (ha δ) y)) := by
        rw [T.pull_comp (H.s g) (C.a δ) rfl (ha δ) h1]
    _ = T.pull (inv (H.s g) ≫ H.s g) h2 (T.pull (C.a δ) (ha δ) y) :=
        (T.pull_comp _ _ _ _ _ _).symm
    _ = T.pull (𝟙 H.Z) h3 (T.pull (C.a δ) (ha δ) y) :=
        pull_eq_of_eq T (IsIso.inv_hom_id _) _ _ _
    _ = _ := T.pull_id _ _ _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtGood
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtGood :
    (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → ExtGood.{u} := by
  intro htr B R _ T L _ _ hG
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have hinj := hG.inj p r c hc G a hgal
    show Function.Injective (LinearMap.baseChange L (T.pull c hc))
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro Z Y p q s _ _ hs
    obtain ⟨tr, htr'⟩ := hG.tr p q s hs
    exact ⟨tr.baseChange L, htr T L p q s tr htr'⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPieceLe
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem unit_sp (l : ℕ) (Ω : Type) [Field Ω] (h : (l : Ω) ≠ 0) : IsUnit (l : Γ(sp Ω, ⊤)) := by
  have hu : IsUnit ((l : Ω)) := h.isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using this

private theorem bc_apply {R : Type} [CommRing R] (L : Type) [CommRing L] [Algebra R L] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (y : L ⊗[R] M) :
    (g ∘ₗ f).baseChange L y = g.baseChange L (f.baseChange L y) := by
  rw [LinearMap.baseChange_comp]; rfl

private theorem fEt_iso {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsIso f] : FEt f 1 := by
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨x ≫ inv f, by simp⟩⟩⟩
  rw [← cancel_mono f, a.2, b.2]

theorem UpperTheory.Gal.G3.pPieceLe :
    EtGood → BcGood.{1} → ExtGood.{1} → (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{1} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → HopSpec → CoverInv.{1} → PieceLe := by
  intro hEt hBc hExt hExtTr hHop hCov l _ k L O _ _ _ _ _ hl H θ C hC Ω _ _
  have hlΩ : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    apply hl
    have : algebraMap k Ω (l : k) = 0 := by simpa using h0
    exact (algebraMap k Ω).injective (by simpa using this)
  have hT0 : (etG l k Ω).Good := hBc _ _ (hEt l _ (unit_sp l Ω hlΩ))
  have hT : ((etG l k Ω).ext L).Good := hExt _ L hT0
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  obtain ⟨hinj, hsurj⟩ := hCov C hC ((etG l k Ω).ext L) hT
  refine ⟨hinj, fun y hy => hsurj y ?_⟩
  intro g hiso hθ
  haveI := hiso
  obtain ⟨tr0, htr0⟩ := hT0.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  refine ⟨tr0.baseChange L, hExtTr _ L H.q (H.s g ≫ H.q) (H.s g) tr0 htr0, ?_⟩
  have hop_eq := (hHop l hl H Ω g 1 (fEt_iso (H.s g))).2 tr0 htr0
  have hy' : y ∈ Module.End.eigenspace ((hop l H Ω g).baseChange L) (θ g) :=
    (Submodule.mem_iInf _).1 hy g
  rw [Module.End.mem_eigenspace_iff, hθ, one_smul, hop_eq] at hy'
  change tr0.baseChange L (((etG l k Ω).pull (H.t g) _).baseChange L y) = y
  exact (bc_apply L _ _ y).symm.trans hy'
end

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct

universe u v

namespace UpperTheory.Gal.G3

theorem pExtPts : ExtPts := by
  intro W Z B _ p _ f g hfg hpt
  let X' : Over B := Over.mk (f ≫ p)
  let Y' : Over B := Over.mk p
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hfg.symm
  have : IsSeparated Y'.hom := ‹_›
  have hsurj : Surjective (equalizer.ι f' g').left := by
    constructor
    intro x
    let K := W.residueField x
    let Ω := AlgebraicClosure K
    let y : Spec (CommRingCat.of Ω) ⟶ W :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x
    have hy : y ≫ f = y ≫ g := hpt Ω y
    let U' : Over B := Over.mk (y ≫ f ≫ p)
    let y' : U' ⟶ X' := Over.homMk y
    have hy' : y' ≫ f' = y' ≫ g' := by
      ext1
      exact hy
    let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
    refine ⟨(equalizer.lift y' hy').left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    show (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x) pt = x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have := isIso_of_isClosedImmersion_of_surjective (Y := W) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

theorem pExtTr :
    ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) := by
  intro B R _ T L _ _ Z Y p q s tr h W r c hc J _ σ hσ hs x
  change LinearMap.baseChange L (T.pull c hc) (LinearMap.baseChange L tr x) =
    ∑ j, LinearMap.baseChange L (T.pull (σ j) (hσ j)) x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [LinearMap.baseChange_tmul]
    rw [h W r c hc J σ hσ hs y, TensorProduct.tmul_sum]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]

theorem isoPts_holds : IsoPts := @pIsoPts

theorem ptsOfSplits_holds : PtsOfSplits := @pPtsOfSplits

theorem splitsPts_holds : SplitsPts := pSplitsPts isoPts_holds

theorem extPts_holds : ExtPts := @pExtPts

theorem fEtBasic_holds : FEtBasic := pFEtBasic ptsOfSplits_holds

theorem splitsBasic_holds : SplitsBasic := pSplitsBasic splitsPts_holds ptsOfSplits_holds

theorem splitsComp_holds : SplitsComp := pSplitsComp splitsPts_holds ptsOfSplits_holds

theorem bcSplits_holds : BcSplits := @pBcSplits @splitsBasic_holds

theorem bcGal_holds : BcGal := pBcGal bcSplits_holds

theorem ordStep_holds : OrdStep := @pOrdStep

theorem ordEx_holds : OrdEx := pOrdEx ordStep_holds

theorem galClosD_holds : GalClosD := pGalClosD splitsPts_holds ordEx_holds

theorem galClos_holds : GalClos := pGalClos galClosD_holds

theorem multiSplit_holds : MultiSplit := pMultiSplit fEtBasic_holds splitsBasic_holds galClosD_holds

theorem algIsoPts_holds : AlgIsoPts := pAlgIsoPts isoPts_holds

theorem algSplit_holds : AlgSplit := @pAlgSplit @algIsoPts_holds

theorem algTr_holds : AlgTr := @pAlgTr

theorem hodgeFun_holds : ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := pHodgeFun ptsOfSplits_holds algSplit_holds algTr_holds

theorem hodgeTr_holds : HodgeTr := @pHodgeTr @hodgeFun_holds

theorem hodgeInj_holds : HodgeInj := @pHodgeInj

theorem hodgeGood_holds : HodgeGood := @pHodgeGood @hodgeTr_holds @hodgeInj_holds

theorem etTr_holds : EtTr := @pEtTr

theorem etnGood_holds : EtnGood := @pEtnGood @fEtBasic_holds @etTr_holds

theorem etGood_holds : EtGood := @pEtGood @etnGood_holds

theorem bcGood_holds : BcGood.{u} := pBcGood bcSplits_holds bcGal_holds

theorem extTr_holds : ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) :=
  @pExtTr.{u}

theorem extGood_holds : ExtGood.{u} := pExtGood extTr_holds

theorem opTr_holds : OpTr.{u} := @pOpTr.{u}

theorem opEx_holds : OpEx.{u} := pOpEx opTr_holds

theorem galInv_holds : GalInv.{u} := @pGalInv.{u}

theorem opEt_holds : OpEt := @pOpEt

theorem opBc_holds : OpBc.{u} := pOpBc bcSplits_holds bcGal_holds

theorem fEtInj_holds : FEtInj.{u} := pFEtInj galClosD_holds

theorem trBase_holds : TrBase.{u} := pTrBase fEtBasic_holds splitsBasic_holds galClosD_holds

theorem trPushM_holds : TrPushM.{u} := pTrPushM fEtBasic_holds splitsBasic_holds splitsComp_holds multiSplit_holds fEtInj_holds

theorem liesAbs_holds : LiesAbs.{u} := pLiesAbs fEtBasic_holds trBase_holds trPushM_holds

theorem hopSpec_holds : HopSpec := pHopSpec etGood_holds bcGood_holds galClos_holds opEx_holds opTr_holds opEt_holds opBc_holds bcSplits_holds

theorem liesGen_holds : LiesGen := @pLiesGen

theorem liesOp_holds : LiesOp.{u} := pLiesOp liesGen_holds liesAbs_holds

theorem coverInv_holds : CoverInv.{u} := pCoverInv galInv_holds splitsPts_holds

theorem pieceLe_holds : PieceLe := pPieceLe etGood_holds bcGood_holds extGood_holds extTr_holds hopSpec_holds coverInv_holds

theorem twSplit_holds : TwSplit := pTwSplit splitsPts_holds

theorem twGal_holds : TwGal := pTwGal twSplit_holds

end UpperTheory.Gal.G3
