module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
public import Development.EtaleCohomology.WeilConjectures.StabPf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEx :
    OpTr.{u} → OpEx.{u} := by
  intro hTr B R _ T hG Z Y Z' p p' s _ _ t hcomm
  obtain ⟨tr, htr⟩ := hG.tr p (s ≫ p) s rfl
  have key := fun A => hTr T hG p (s ≫ p) p' s t rfl hcomm tr htr A
  refine ⟨fun hgs => ⟨tr ∘ₗ T.pull t hcomm, (key _).2 hgs rfl, fun A hA => (key A).1 hA⟩, ?_⟩
  intro A hA W r c hc J _ σ h hsp x
  have hσ : ∀ j, σ j ≫ (s ≫ p) = r := by
    intro j
    rw [← hcomm, ← Category.assoc]
    exact h j
  rw [(key A).1 hA, LinearMap.comp_apply, htr W r c hc J σ hσ hsp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [T.pull_comp (σ j) t (hσ j) hcomm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pBcGood :
    BcSplits → BcGal → BcGood.{u} := by
  intro hS hG B B' R _ T g hT
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have ha : ∀ x, a x ≫ r = r := fun x => by
      rw [← hc, ← Category.assoc, hgal.2.2.2.2.2.1 x]
    exact hT.inj (pullback.snd p g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) G
      (fun x => bcMap g (a x) (ha x)) (hG g p r c hc G a ha hgal)
  · intro Z Y p q s _ _ hs
    obtain ⟨hfin, het, -⟩ := hS g p q q s hs s hs Empty Empty.elim (fun j => j.elim)
    obtain ⟨tr, htr⟩ := hT.tr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) (bcMap_snd g s hs)
    refine ⟨tr, ?_⟩
    intro W r c hc J _ σ hσ hspl x
    exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
      (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j))
      ((hS g p q r s hs c hc J σ hσ).2.2 hspl) x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bcMap_isPullback {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X)
    (h : f ≫ p = q) : IsPullback (pullback.fst q g) (bcMap g f h) f (pullback.fst p g) := by
  subst h
  refine IsPullback.of_bot ?_ (bcMap_fst g f rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (f ≫ p) g

theorem UpperTheory.Gal.G3.pBcGal :
    BcSplits → BcGal := by
  intro hB B B' Z W g p r c hc G _ _ a ha hG
  obtain ⟨hfin, het, hsur, h1, hmul, hsp⟩ := hG
  obtain ⟨f1, f2, f3⟩ := @hB B B' Z W W g p r r c hc c hc G _ a ha hfin het
  refine ⟨f1, f2, ?_, ?_, ?_, f3 hsp⟩
  · exact MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback g c hc) hsur
  · apply pullback.hom_ext
    · rw [bcMap_fst, h1, Category.comp_id, Category.id_comp]
    · rw [bcMap_snd, Category.id_comp]
  · intro x y
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, hmul]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pullIdentity_move {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} {r r' : W ⟶ B} (e : r = r') (c : W ⟶ Z) {J : Type} [Fintype J]
    (t : J → (W ⟶ Z')) (y : T.H p) (x : T.H p') (h : c ≫ p = r) (h' : c ≫ p = r')
    (k : ∀ j, t j ≫ p' = r) (k' : ∀ j, t j ≫ p' = r')
    (H : T.pull c h y = ∑ j, T.pull (t j) (k j) x) :
    T.pull c h' y = ∑ j, T.pull (t j) (k' j) x := by
  subst e
  exact H

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e
  rfl

private theorem bcMap_comp' {B B' X Y V : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : V ⟶ B'}
    (f : Y ⟶ X) (f' : V ⟶ Y) (h : f ≫ p = q) (h' : f' ≫ q = r) (h'' : (f' ≫ f) ≫ p = r) :
    bcMap g (f' ≫ f) h'' = bcMap g f' h' ≫ bcMap g f h := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc (bcMap g f' h'), bcMap_fst,
      Category.assoc]
  · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]

theorem UpperTheory.Gal.G3.pOpBc :
    BcSplits → BcGal → OpBc.{u} := by
  intro hS hG B B' R _ T g Z Y Z' p q p' s _ _ t hs ht A hA
  obtain ⟨W, c, G, _, _, a, J, _, σ, hh, hgal, hspl, hsum⟩ := hA
  have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
    rw [← hs, ← Category.assoc, hspl.1 j]
  have ha : ∀ x, a x ≫ (c ≫ p) = c ≫ p := fun x => by
    rw [← Category.assoc, hgal.2.2.2.2.2.1 x]
  refine ⟨pullback (c ≫ p) g, bcMap g c rfl, G, inferInstance, inferInstance,
    fun x => bcMap g (a x) (ha x), J, inferInstance, fun j => bcMap g (σ j) (hσ j), ?_,
    hG g p (c ≫ p) c rfl G a ha hgal, (hS g p q (c ≫ p) s hs c rfl J σ hσ).2.2 hspl, ?_⟩
  · intro j
    rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  · intro x
    have e : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j ≫ t) (hh j)) (bcMap_snd g _ (hh j)) x := hsum x
    have e2 : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j) (hσ j) ≫ bcMap g t ht)
          (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x := by
      rw [e]
      exact Finset.sum_congr rfl fun j _ =>
        pull_congr T (bcMap_comp' g t (σ j) ht (hσ j) _) _ _ x
    exact pullIdentity_move T (bcMap_snd g c rfl).symm _ _ _ _ _ _ _ _ e2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pGalClos :
    GalClosD → GalClos := by
  intro hD Z Y s _ _ d h
  obtain ⟨W, c, G, iG, fG, a, σ, hg, hs⟩ := hD s d ⟨inferInstance, inferInstance, h⟩
  exact ⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hg, hs⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h
    apply hl
    apply (algebraMap k Ω).injective
    rw [map_natCast, h, map_zero]
  have h2 : IsUnit (l : Ω) := isUnit_iff_ne_zero.mpr h1
  have h3 := h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  simpa using h3

theorem UpperTheory.Gal.G3.pHopSpec :
    EtGood → BcGood.{1} → GalClos → OpEx.{1} → OpTr.{1} → OpEt → OpBc.{1} → BcSplits → HopSpec := by
  intro hEt hBc hClos hEx hTr hOpEt hOpBc hSpl l _ k _ hl H Ω _ _ g d hd
  obtain ⟨_, _, hcard⟩ := hd
  have gs : GalSplit (H.s g) := hClos (H.s g) d hcard
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hT : (et l (sp Ω)).Good := hEt l (sp Ω) (l_unit l hl Ω)
  have hT' : ((et l (sp Ω)).bc g₀).Good := hBc _ g₀ hT
  have hs : H.sΩ Ω g = bcMap g₀ (H.s g) rfl := rfl
  have ht : H.tΩ Ω g = bcMap g₀ (H.t g) (H.comm g) := rfl
  have hfe := hSpl g₀ H.q (H.s g ≫ H.q) H.q (H.s g) rfl (𝟙 _) (Category.id_comp _) PEmpty (fun j => j.elim) (fun j => j.elim)
  obtain ⟨_, _, -⟩ := hfe
  have hEq := hOpEt l (pullback.snd H.q g₀) (pullback.snd H.q g₀) (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g))
    ((bcMap_snd g₀ (H.t g) (H.comm g)).trans (bcMap_snd g₀ (H.s g) rfl).symm)
  have toCorr : ∀ A, ((et l (sp Ω)).bc g₀).IsOp H.q H.q (H.s g) (H.t g) A → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    intro A hA
    have h1 := hOpBc (et l (sp Ω)) g₀ H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) A hA
    exact (hEq A).1 h1
  have hex : ∃ A, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    obtain ⟨A, hA, -⟩ := (hEx _ hT' H.q H.q (H.s g) (H.t g) (H.comm g)).1 gs
    exact ⟨A, toCorr A hA⟩
  have hspec : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) := by
    unfold hop
    rw [dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨hspec, fun tr htr => ?_⟩
  have hA := ((hTr _ hT' H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) tr htr) _).2 gs rfl
  have hcorr := toCorr _ hA
  obtain ⟨tr', htr'⟩ := hT.tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  have key := fun A => hTr _ hT (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (pullback.snd H.q g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) (bcMap_snd _ _ _) tr' htr' A
  have e1 := (key _).1 ((hEq _).2 hspec)
  have e2 := (key _).1 ((hEq _).2 hcorr)
  exact e1.trans e2.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtInj
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pFEtInj :
    GalClosD → FEtInj.{u} := by
  intro hGC B R _ T hT Z W p r c hc d hd hfet
  obtain ⟨V, e, G, _, _, a, σ, hgal, hspl⟩ := hGC c d hfet
  have h0 : σ ⟨0, hd⟩ ≫ c = e := hspl.1 _
  subst h0
  have hinj := hT.inj p ((σ ⟨0, hd⟩ ≫ c) ≫ p) (σ ⟨0, hd⟩ ≫ c) rfl G a hgal
  have hσr : σ ⟨0, hd⟩ ≫ r = (σ ⟨0, hd⟩ ≫ c) ≫ p := by
    rw [← hc, Category.assoc]
  have hcomp := T.pull_comp (σ ⟨0, hd⟩) c hσr hc rfl
  intro x y hxy
  apply hinj
  rw [hcomp x, hcomp y, hxy]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV

namespace UpperTheory.Gal.G3

def SplitDesc : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), Splits s c σ → IsFinite s ∧ Etale s

def CharVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) = 0 → ∀ {X : Scheme.{0}} (_ : X ⟶ sp k) (n i : ℤ),
  Subsingleton (Hl l (sch.obj X) n i)

def CorrUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (_ : Z ⟶ sp k) (s : Y ⟶ Z) (t : Y ⟶ Z')
  (A A' : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)), IsCorrOp l s t A → IsCorrOp l s t A' → A = A'

def VBcS : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] (φ : k →+* Ω),
  IsUnit (l : k) → ∀ {X : Scheme.{0}} (p : X ⟶ sp k) [IsProper p] [Smooth p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) n i)

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesOp
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pLiesOp :
    LiesGen → LiesAbs.{u} → LiesOp.{u} := by
  intro hGen hAbs k L O _ _ _ _ H θ C g D s t hst m d hL hd R _ T hT tr trg htr htrg x
  obtain ⟨κ, h, hκt, hfet⟩ := hGen C g s t hst m hL
  exact hAbs T hT _ _ _ _ (piK C) (piK_snd C) (H.s g) (H.t g) (H.comm g) _ _
    (bcMap_snd _ _ _) κ h d m rfl (bcMap_snd _ _ _) hκt hd hfet tr trg htr htrg x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHodgeTr :
    (∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b)) → HodgeTr := by
  intro h k _ a b Z Y p q s _ _ hs W r c hc J _ σ hσq hsp x
  obtain ⟨hσ, _⟩ := hsp
  have hom := GlobalTheory.GalTrace.omegaTrace_omegaPull (k := k) hs hc Finset.univ hσ hσq
    (fun U hU b => by simpa using h k p q r s c J σ hσ ⟨hσ, ‹_›⟩ U hU b) a
  exact GlobalTheory.GalTrace.hodgePull_hodgeTrace hs hc Finset.univ hσ hσq a hom b x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHodgeGood :
    HodgeTr → HodgeInj → HodgeGood := by
  intro hT hI k _ _ i j
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a h
    obtain ⟨h1, h2, h3, -⟩ := h
    haveI := h1
    haveI := h2
    haveI := h3
    exact hI k i j p r c hc
  · intro Z Y p q s _ _ hs
    exact ⟨hodgeTrace hs i j, hT k i j p q s hs⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrBase
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrBase :
    FEtBasic → SplitsBasic → GalClosD → TrBase.{u} := by
  intro hF hS hC B R _ T hT P Y Z' Z p q p' q' v s' s g d hv hg hq' hpb hs tr tr' htr htr' x
  haveI : IsFinite s := hs.1
  haveI : Etale s := hs.2.1
  obtain ⟨W, c, G, _, _, a, σ, hgal, hspl⟩ := hC s' d (hF.1 v s' s g d hpb hs)
  have hσs : ∀ j, σ j ≫ s' = c := hspl.1
  have hσ' : ∀ j, σ j ≫ q' = c ≫ p' := fun j => by
    rw [← hq', ← Category.assoc, hσs j]
  have hσv : ∀ j, (σ j ≫ v) ≫ q = c ≫ p' := fun j => by
    rw [Category.assoc, hv, hσ' j]
  have hcg : (c ≫ g) ≫ p = c ≫ p' := by rw [Category.assoc, hg]
  have hspl2 : Splits s (c ≫ g) (fun j => σ j ≫ v) :=
    (hS.2 v s' s g hpb c (Fin d) σ hσs).1 hspl
  apply hT.inj p' (c ≫ p') c rfl G a hgal
  rw [← T.pull_comp c g rfl hg hcg, htr W (c ≫ p') (c ≫ g) hcg (Fin d) (fun j => σ j ≫ v) hσv hspl2 x,
    htr' W (c ≫ p') c rfl (Fin d) σ hσ' hspl]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact T.pull_comp (σ j) v (hσ' j) hv (hσv j) x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pPlInv :
    GalInv.{u} → TwGal → PlInv.{u} := by
  intro hG hT B G _ X R _ _ T hgood m j hmj
  constructor
  · obtain ⟨m', hm'j, hnorm, hS⟩ := X.deep j {(m, 1)}
    have hm'm : X.K m' ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m' j (X.isAdmissibleIntegralBasisChange_one hm'j) hnorm
    have hinj := hgood.inj (X.q j) (X.q m') _ (X.tr_q m' j 1 _ _) Γ _ hgal
    have key : ∀ z, X.pl T m' j 1 z = X.pl T m' m 1 (X.pl T m j 1 z) := fun z => by
      rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hm'm) (X.isAdmissibleIntegralBasisChange_one hmj), one_mul]
    intro x y hxy
    apply hinj
    rw [← X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hm'j), key, key, hxy]
  · intro hnorm y hy
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m j (X.isAdmissibleIntegralBasisChange_one hmj) hnorm
    have ha : ∀ g : Γ, X.tr m m (r g) (c g).1 (c g).2 ≫ X.q m = X.q m := fun g => X.tr_q _ _ _ _ _
    have hsurj := (hG T hgood (X.q j) (X.q m) _ (X.tr_q m j 1 _ _) Γ _ ha hgal y).2
    obtain ⟨x, hx⟩ := hsurj (fun g => by rw [← X.pl_eq T (c g)]; exact hy _ (hr g))
    exact ⟨x, by rw [X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hmj)]; exact hx⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsComp
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pSplitsComp :
    SplitsPts → PtsOfSplits → SplitsComp := by
  intro hS hP Y P Z W κ s _ _ _ _ c I J _ _ τ σ hτ hσ
  have hτc : ∀ i, τ i ≫ s = c := hτ.1
  have hσc : ∀ i j, σ i j ≫ κ = τ i := fun i => (hσ i).1
  refine hS (κ ≫ s) c (I × J) (fun x => σ x.1 x.2)
    (fun x => by rw [← Category.assoc, hσc, hτc]) ?_
  intro Ω _ _ x y hy
  obtain ⟨i, hi, hiu⟩ := hP s c I τ hτ Ω x (y ≫ κ) (by simpa using hy)
  obtain ⟨j, hj, hju⟩ := hP κ (τ i) J (σ i) (hσ i) Ω x y hi.symm
  refine ⟨(i, j), hj, ?_⟩
  rintro ⟨i', j'⟩ h'
  have h'' : x ≫ σ i' j' = y := h'
  have hi' : i' = i := hiu i' (by
    show x ≫ τ i' = y ≫ κ
    rw [← hσc i' j', ← Category.assoc, h''])
  subst hi'
  have hj' : j' = j := hju j' h''
  subst hj'
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem trace_pi_eq_sum {C J : Type} [CommRing C] [Fintype J] (a : J → C) :
    Algebra.trace C (J → C) a = ∑ j, a j := by
  classical
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace C (Pi.basisFun C J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, Pi.single_apply]

theorem UpperTheory.Gal.G3.pAlgTr :
    AlgTr := by
  intro A A' C _ _ _ _ _ _ _ J _ τ e he b
  letI : Algebra A' (C ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Projective A A' := projective_of_etale A A'
  haveI : Module.Free C (C ⊗[A] A') := Module.Free.of_equiv e.symm.toLinearEquiv
  haveI : Module.Finite C (C ⊗[A] A') := Module.Finite.equiv e.symm.toLinearEquiv
  have h1 := algTrace_of_isPushout (B := A) (B' := A') (C := C) (C' := C ⊗[A] A') b
  have h2 : (etTrace A A') b = (algTrace A A') b := rfl
  rw [h2, ← h1, algTrace_eq_trace]
  have h3 : algebraMap A' (C ⊗[A] A') b = e.symm (e (1 ⊗ₜ[A] b)) := by
    rw [AlgEquiv.symm_apply_apply]
    rfl
  rw [h3, Algebra.trace_eq_of_algEquiv e.symm, trace_pi_eq_sum]
  exact Finset.sum_congr rfl fun j _ => he b j
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultiSplit
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pMultiSplit :
    FEtBasic → SplitsBasic → GalClosD → MultiSplit := by
  intro hF hS hG Z n
  induction n with
  | zero =>
    intro Y s d _
    exact ⟨Z, 𝟙 Z, 1, one_pos, UpperTheory.Gal.Int.Geo.fEt_id Z, fun i => i.elim0⟩
  | succ n ih =>
    intro Y s d hs
    obtain ⟨W, c, e, he, hc, hspl⟩ := ih (fun i => Y i.castSucc) (fun i => s i.castSucc)
      (fun i => d i.castSucc) (fun i => hs i.castSucc)
    have hP : FEt (pullback.snd (s (Fin.last n)) c) (d (Fin.last n)) :=
      hF.1 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c _
        (IsPullback.of_hasPullback _ _) (hs _)
    obtain ⟨W2, c2, G, _, _, a, σ, hgal, hσ⟩ := hG (pullback.snd (s (Fin.last n)) c) _ hP
    have hc2 : FEt c2 (Nat.card G) := hF.2.2 c2 G a hgal
    refine ⟨W2, c2 ≫ c, e * Nat.card G, Nat.mul_pos he Nat.card_pos,
      hF.2.1 c2 c e (Nat.card G) hc2 hc, ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · haveI := (hs (Fin.last n)).1
      haveI := (hs (Fin.last n)).2.1
      exact ⟨fun j => σ j ≫ pullback.fst _ _,
        (hS.2 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c
          (IsPullback.of_hasPullback _ _) c2 (Fin (d (Fin.last n))) σ hσ.1).mp hσ⟩
    · obtain ⟨τ, hτ⟩ := hspl i
      haveI := (hs i.castSucc).1
      haveI := (hs i.castSucc).2.1
      exact ⟨fun j => c2 ≫ τ j, hS.1 (s i.castSucc) c _ τ c2 hτ⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesAbs
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pLiesAbs :
    FEtBasic → TrBase.{u} → TrPushM.{u} → LiesAbs.{u} := by
  intro hF hB hP B R _ T hT Z Y C D pZ pY pC pD π hπ sg tg htg s t ht κ h d m hsg hs hκt hsd hℓ tr trg htr htrg x
  have hpb : IsPullback (pullback.snd π s) (pullback.fst π s) s π := (IsPullback.of_hasPullback π s).flip
  have hfst : FEt (pullback.fst π s) d := hF.1 _ _ s π d hpb hsd
  haveI : IsFinite (pullback.fst π s) := hfst.1
  haveI : Etale (pullback.fst π s) := hfst.2.1
  obtain ⟨tr1, htr1⟩ := hT.tr pZ (pullback.fst π s ≫ pZ) (pullback.fst π s) rfl
  have hsndp : pullback.snd π s ≫ pD = pullback.fst π s ≫ pZ := by
    rw [← hs, ← Category.assoc, ← pullback.condition, Category.assoc, hπ]
  have base := hB T hT pY pD pZ (pullback.fst π s ≫ pZ) (pullback.snd π s) (pullback.fst π s) s π d
    hsndp hπ rfl hpb hsd tr tr1 htr htr1 ((T.pull t ht) x)
  have htrg' : T.IsTr pZ pC (pullback.lift sg κ h ≫ pullback.fst π s) trg := by
    rw [pullback.lift_fst]; exact htrg
  have hℓq : pullback.lift sg κ h ≫ (pullback.fst π s ≫ pZ) = pC := by
    rw [← Category.assoc, pullback.lift_fst, hsg]
  have push := hP T hT pZ (pullback.fst π s ≫ pZ) pC (pullback.lift sg κ h) (pullback.fst π s) d m hℓq rfl
    hfst hℓ tr1 trg htr1 htrg' ((T.pull (pullback.snd π s) hsndp) ((T.pull t ht) x))
  have hcongr : ∀ {W : Scheme} {r : W ⟶ B} (f f' : W ⟶ Y) (e : f = f') (hf : f ≫ pY = r) (hf' : f' ≫ pY = r),
      T.pull f hf x = T.pull f' hf' x := by
    intro W r f f' e hf hf'
    subst e
    rfl
  have h1 : (tg ≫ π) ≫ pY = pC := by rw [Category.assoc, hπ, htg]
  have h2 : (pullback.snd π s ≫ t) ≫ pY = pullback.fst π s ≫ pZ := by rw [Category.assoc, ht, hsndp]
  have h3 : (pullback.lift sg κ h ≫ pullback.snd π s ≫ t) ≫ pY = pC := by
    rw [Category.assoc, h2, hℓq]
  have hmor : tg ≫ π = pullback.lift sg κ h ≫ pullback.snd π s ≫ t := by
    rw [← Category.assoc, pullback.lift_snd, hκt]
  rw [← T.pull_comp tg π htg hπ h1, hcongr _ _ hmor h1 h3,
    T.pull_comp (pullback.lift sg κ h) (pullback.snd π s ≫ t) hℓq h2 h3,
    T.pull_comp (pullback.snd π s) t hsndp ht h2, push, base]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHopDeep :
    PlInv.{u} → HopDeep.{u} := by
  classical
  intro hPl B G _ X R _ _ T hT j f hf
  have hfin := hf.2.2
  have hpush : ∀ (n n' : X.ι), X.K n' ≤ X.K n → (∀ g, f g ≠ 0 → X.admitted n j g⁻¹) → ∀ x : T.H (X.q j),
      X.pl T n' n 1 (∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n j z.out⁻¹ x) =
        ∑ᶠ z : G ⧸ X.K j, f z.out • X.pl T n' j z.out⁻¹ x := by
    intro n n' hn'n hadn x
    rw [map_finsum _ (hfin.subset ?_)]
    · refine finsum_congr fun z => ?_
      rw [map_smul]
      by_cases h0 : f z.out = 0
      · simp [h0]
      · rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hn'n) (hadn _ h0), mul_one]
    · intro z hz
      simp only [Set.mem_setOf_eq]
      intro h0
      exact hz (by simp [h0])
  constructor
  · obtain ⟨m, hmj, -, hS⟩ := X.deep j (hfin.toFinset.image fun z => (j, (Quotient.out z)⁻¹))
    refine ⟨m, hmj, fun g hg => ⟨hf.2.1 g hg, fun u hu => ?_⟩⟩
    obtain ⟨⟨h, hh⟩, hheq⟩ := QuotientGroup.mk_out_eq_mul (X.K j) g
    have hz : (g : G ⧸ X.K j) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hheq, (hf.1 h hh g).2]
      exact hg
    have hc := hS (j, (Quotient.out (g : G ⧸ X.K j))⁻¹) (Finset.mem_image_of_mem _ hz) u hu
    simp only [hheq] at hc
    have hmem := mul_mem (mul_mem hh hc) (inv_mem hh)
    convert hmem using 1
    group
  · intro A m hmj hadm hA m' hm'j hadm' x
    obtain ⟨n, -, -, hS⟩ := X.deep j {(m, 1), (m', 1)}
    have hnm : X.K n ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    have hnm' : X.K n ≤ X.K m' := fun u hu => by simpa using hS (m', 1) (by simp) u hu
    apply (hPl X T hT n m' hnm').1
    rw [hpush m' n hnm' hadm', X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm') (X.isAdmissibleIntegralBasisChange_one hm'j), ← hpush m n hnm hadm, ← hA,
      X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hnm) (X.isAdmissibleIntegralBasisChange_one hmj)]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private lemma etale_specMap (D E : Type) [CommRing D] [CommRing E] [Algebra D E] [Algebra.Etale D E] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap D E))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.etale_algebraMap.mpr ‹_›

theorem UpperTheory.Gal.G3.pAlgIsoPts :
    IsoPts → AlgIsoPts := by
  intro hI D E _ _ _ _ hpts
  let φ : CommRingCat.of D ⟶ CommRingCat.of E := CommRingCat.ofHom (algebraMap D E)
  have : Etale (Spec.map φ) := etale_specMap D E
  have hiso : IsIso (Spec.map φ) := by
    refine hI (Spec.map φ) ?_
    intro Ω _ _ z
    obtain ⟨y, hy, hyu⟩ := hpts Ω (Spec.preimage z).hom
    refine ⟨Spec.map (CommRingCat.ofHom y), ?_, ?_⟩
    · show Spec.map (CommRingCat.ofHom y) ≫ Spec.map φ = z
      rw [← Spec.map_comp]
      conv_rhs => rw [← Spec.map_preimage z]
      congr 1
      ext d
      exact congrArg (fun f : D →+* Ω => f d) hy
    · intro w hw
      rw [← Spec.map_preimage w]
      congr 1
      ext e
      have hx : (Spec.preimage w).hom.comp (algebraMap D E) = (Spec.preimage z).hom := by
        have h2 : Spec.map (φ ≫ Spec.preimage w) = Spec.map (Spec.preimage z) := by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
          exact hw
        have h3 := Spec.map_injective h2
        ext d
        exact congrArg (fun f => (CommRingCat.Hom.hom f) d) h3
      exact congrArg (fun f : E →+* Ω => f e) (hyu _ hx)
  have hφ : IsIso φ := by
    refine ⟨⟨Spec.preimage (inv (Spec.map φ)), ?_, ?_⟩⟩
    · apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.inv_hom_id]
    · apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.hom_inv_id]
  exact ConcreteCategory.bijective_of_isIso φ
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrPushM
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrPushM :
    FEtBasic → SplitsBasic → SplitsComp → MultiSplit → FEtInj.{u} → TrPushM.{u} := by
  intro hF hSB hSC hMS hInj B R _ T hT Y P Z p q r κ s d m hκ hs hd hm tr tr' htr htr' x
  haveI : IsFinite s := hd.1
  haveI : Etale s := hd.2.1
  haveI : IsFinite κ := hm.1
  haveI : Etale κ := hm.2.1
  obtain ⟨W1, c1, e1, he1, hc1, hτ0⟩ := hMS 1 (fun _ => P) (fun _ => s) (fun _ => d) (fun _ => hd)
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin d → (W1 ⟶ P), Splits s c1 τ := hτ0 0
  have hPb : ∀ i : Fin d, FEt (pullback.snd κ (τ i)) m := fun i =>
    hF.1 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i) m
      (IsPullback.of_hasPullback κ (τ i)) hm
  obtain ⟨W2, c2, e2, he2, hc2, hρ0⟩ :=
    hMS d (fun i => pullback κ (τ i)) (fun i => pullback.snd κ (τ i)) (fun _ => m) hPb
  have hρ1 : ∀ i : Fin d, ∃ ρ : Fin m → (W2 ⟶ pullback κ (τ i)),
      Splits (pullback.snd κ (τ i)) c2 ρ := hρ0
  choose ρ hρ using hρ1
  have key : ∀ i j, (ρ i j ≫ pullback.fst κ (τ i)) ≫ κ = c2 ≫ τ i := fun i j => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, (hρ i).1 j]
  have hsκ : ∀ i, Splits κ (c2 ≫ τ i) (fun j => ρ i j ≫ pullback.fst κ (τ i)) := fun i =>
    (hSB.2 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i)
      (IsPullback.of_hasPullback κ (τ i)) c2 (Fin m) (ρ i) (hρ i).1).1 (hρ i)
  have hss : Splits s (c2 ≫ c1) (fun i => c2 ≫ τ i) := hSB.1 s c1 (Fin d) τ c2 hτ
  have hcomp := hSC κ s (c2 ≫ c1) (Fin d) (Fin m) (fun i => c2 ≫ τ i)
    (fun i j => ρ i j ≫ pullback.fst κ (τ i)) hss hsκ
  have hfc : FEt (c2 ≫ c1) (e1 * e2) := hF.2.1 c2 c1 e1 e2 hc2 hc1
  have hστ : ∀ i, (c2 ≫ τ i) ≫ q = (c2 ≫ c1) ≫ p := fun i => by
    rw [← hs]
    simp only [Category.assoc]
    rw [← Category.assoc (τ i) s p, hτ.1 i]
  have hσ' : ∀ y : Fin d × Fin m, (ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) ≫ r = (c2 ≫ c1) ≫ p :=
    fun y => by
      rw [← hκ, ← Category.assoc, key]
      exact hστ y.1
  have move : ∀ (f : W2 ⟶ Y) (g : W2 ⟶ P) (hf : f ≫ r = (c2 ≫ c1) ≫ p)
      (hg : g ≫ q = (c2 ≫ c1) ≫ p), f ≫ κ = g → T.pull f hf (T.pull κ hκ x) = T.pull g hg x := by
    intro f g hf hg e
    subst e
    exact (T.pull_comp f κ hf hκ hg x).symm
  apply hInj T hT p ((c2 ≫ c1) ≫ p) (c2 ≫ c1) rfl (e1 * e2) (Nat.mul_pos he1 he2) hfc
  rw [htr' W2 _ (c2 ≫ c1) rfl (Fin d × Fin m) (fun y => ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) hσ' hcomp]
  rw [map_smul, htr W2 _ (c2 ≫ c1) rfl (Fin d) (fun i => c2 ≫ τ i) hστ hss]
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun j _ => move _ _ (hσ' (i, j)) (hστ i) (key i j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul R m _).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private lemma supp_fin {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R] (T : Th.{u} B R)
    {j m : X.ι} {f : G → R} (hf : X.IsFn j f) (x : T.H (X.q j)) :
    (Function.support fun y : G ⧸ X.K j => f y.out • X.pl T m j y.out⁻¹ x).Finite := by
  refine hf.2.2.subset ?_
  intro y hy h0
  exact hy (by simp only [h0, zero_smul])

theorem UpperTheory.Gal.G3.pHopLin :
    FnRing → HopDeep.{u} → HopEx.{u} → HopLin.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' c hf hf'
  obtain ⟨⟨m1, hm1, ha1⟩, -⟩ := hD X T hT j f hf
  obtain ⟨⟨m2, hm2, ha2⟩, -⟩ := hD X T hT j f' hf'
  obtain ⟨m, hmm1, -, hS⟩ := X.deep m1 {(m2, 1)}
  have hmm2 : X.K m ≤ X.K m2 := by
    intro u hu
    simpa using hS (m2, 1) (by simp) u hu
  have hmj : X.K m ≤ X.K j := hmm1.trans hm1
  have hA1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm1).mul (ha1 g hg)
  have hA2 : ∀ g, f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one hmm2).mul (ha2 g hg)
  have e1 := (hE X T hT j f hf).1 m hmj hA1
  have e2 := (hE X T hT j f' hf').1 m hmj hA2
  have hsum := ((hR X R j).2.2.1 f f' hf hf').1
  have hc := (hR X R j).2.2.2 c f hf
  constructor
  · symm
    apply (hE X T hT j (f + f') hsum).2
    apply (hD X T hT j (f + f') hsum).2 _ m hmj
    · intro g hg
      by_cases h1 : f g = 0
      · apply hA2 g
        intro h2
        apply hg
        simp [h1, h2]
      · exact hA1 g h1
    · intro x
      rw [LinearMap.add_apply, map_add (f := _), e1 x, e2 x,
        ← finsum_add_distrib (supp_fin (m := m) X T hf x) (supp_fin (m := m) X T hf' x)]
      apply finsum_congr
      intro y
      simp [add_smul]
  · symm
    apply (hE X T hT j (c • f) hc).2
    apply (hD X T hT j (c • f) hc).2 _ m hmj
    · intro g hg
      apply hA1 g
      intro h
      apply hg
      simp [h]
    · intro x
      rw [LinearMap.smul_apply, map_smul, e1 x, smul_finsum]
      apply finsum_congr
      intro y
      simp [smul_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTwGal :
    TwSplit → TwGal := by
  intro hS B G _ X m j b hnorm
  classical
  haveI hN : ((X.K m).subgroupOf (X.K j)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    push_cast
    exact hnorm g g.2 n hn⟩
  haveI : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx m j)
  have admr : ∀ c : X.K j ⧸ (X.K m).subgroupOf (X.K j), X.admitted m m ((c.out : X.K j) : G)⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hnorm _ (inv_mem c.out.2) u hu⟩
  have uniq : ∀ k ∈ X.K j, ∃! c : X.K j ⧸ (X.K m).subgroupOf (X.K j),
      k * (((c.out : X.K j) : G))⁻¹⁻¹ ∈ X.K m := by
    intro k hk
    refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
      simp only [inv_inv]
      rw [hu]
      have hu' : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
      simpa [mul_assoc] using hu'
    · intro c hc
      simp only [inv_inv] at hc
      rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_inv_rev] using inv_mem hc
  have trc : ∀ (g1 g2 : G) (e : g1 = g2) (p1 : X.admitted m m g1) (p2 : X.admitted m m g2),
      X.tr m m g1 p1.1 p1.2 = X.tr m m g2 p2.1 p2.2 := by
    intro g1 g2 e p1 p2
    subst e
    rfl
  have tl : ∀ (g k : G) (hg : X.admitted m m g) (hk : k ∈ X.K m) (hkg : X.admitted m m (k * g)),
      X.tr m m (k * g) hkg.1 hkg.2 = X.tr m m g hg.1 hg.2 := by
    intro g k hg hk hkg
    rw [← X.tr_mul m m m g k hg.1 hg.2 (X.K_le m k hk) (X.tower_admissible_self hk).2 hkg.1 hkg.2,
      X.tr_self m k _ _ hk, Category.comp_id]
  refine ⟨X.K j ⧸ (X.K m).subgroupOf (X.K j), inferInstance, inferInstance,
    fun c => ((c.out : X.K j) : G)⁻¹, admr, fun c => inv_mem c.out.2, uniq, ?_⟩
  unfold GlobalTheory.GalV.IsGalois
  refine ⟨X.fin m j b.1 b.2, X.etale m j b.1 b.2, X.onto m j b.1 b.2, ?_, ?_,
    hS X m m j b b le_rfl hnorm _ _ admr (fun c => inv_mem c.out.2) uniq⟩
  · have h1 : ((1 : X.K j ⧸ (X.K m).subgroupOf (X.K j)).out : G) ∈ X.K m :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp (QuotientGroup.out_eq' 1))
    exact X.tr_self m _ _ _ (inv_mem h1)
  · intro g g'
    set w : X.K j := ((g.out : X.K j) * g'.out)⁻¹ * (g * g').out with hwdef
    have hw : w ∈ (X.K m).subgroupOf (X.K j) := by
      rw [hwdef, ← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']
    have hw' : ((w : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp hw
    have e : (((g * g').out : X.K j) : G)⁻¹ =
        ((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) := by
      simp only [hwdef, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hA : X.admitted m m ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹) :=
      Tower.admitted.mul (admr g) (admr g')
    have hB : X.admitted m m (((w : X.K j) : G)⁻¹ * ((((g'.out : X.K j) : G))⁻¹ * (((g.out : X.K j) : G))⁻¹)) :=
      Tower.admitted.mul hA (X.tower_admissible_self (inv_mem hw'))
    exact ((trc _ _ e (admr (g * g')) hB).trans (tl _ _ hA (inv_mem hw') hB)).trans
      (X.tr_mul m m m _ _ (admr g).1 (admr g).2 (admr g').1 (admr g').2 hA.1 hA.2).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem affine_point_comp {X Y : Scheme.{0}} (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) {Ω : Type} [Field Ω] (x : Γ(X, V) →+* Ω) :
    (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (x.comp (f.appLE U V i).hom)) ≫ hU.fromSpec := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV i, ← Category.assoc, ← Spec.map_comp]
  rfl

private theorem affine_point_injective {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Ω : Type} [Field Ω]
    {a b : Γ(X, V) →+* Ω}
    (h : Spec.map (CommRingCat.ofHom a) ≫ hV.fromSpec = Spec.map (CommRingCat.ofHom b) ≫ hV.fromSpec) : a = b := by
  have h' := Spec.map_injective ((cancel_mono _).1 h)
  exact congrArg CommRingCat.Hom.hom h'

private theorem cech_section_local_split (hP : PtsOfSplits) (hS : AlgSplit) (hT : AlgTr) {k : Type} [Field k] {Z Y W : Scheme.{0}}
    (p : Z ⟶ sp k) (q : Y ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J]
    (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c) (hsp : Splits s c σ) (U : Z.Opens) (hU : IsAffineOpen U)
    (V : W.Opens) (hV : IsAffineOpen V) (hVU : V ≤ c ⁻¹ᵁ U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) :
    (c.appLE U V hVU).hom (secTrace p q hU b) =
      ∑ j, ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom b := by
  letI : Algebra (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := secAlg p q s U
  haveI : Module.Finite (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_finite hU
  haveI : Algebra.Etale (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_etale hU
  letI : Algebra (GlobalTheory.CechDR.Sec p U) Γ(W, V) := (c.appLE U V hVU).hom.toAlgebra
  have hcomp : ∀ j, s.app U ≫ (σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) =
      c.appLE U V hVU := by
    intro j
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hσ j]
  let τ : J → GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U) →ₐ[GlobalTheory.CechDR.Sec p U] Γ(W, V) := fun j =>
    { toRingHom := ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom
      commutes' := fun a => congrArg (fun f => CommRingCat.Hom.hom f a) (hcomp j) }
  have hA' : IsAffineOpen (s ⁻¹ᵁ U) := hU.preimage s
  obtain ⟨e, he⟩ := hS _ _ _ J τ (by
    intro Ω _ _ x y hxy
    have hring : y.comp (s.appLE U (s ⁻¹ᵁ U) le_rfl).hom = x.comp (c.appLE U V hVU).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hxy
    have hpt : (Spec.map (CommRingCat.ofHom y) ≫ hA'.fromSpec) ≫ s =
        (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ c :=
      (affine_point_comp s hU hA' le_rfl y).trans
        ((congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec) hring).trans
          (affine_point_comp c hU hV hVU x).symm)
    obtain ⟨j, hj, huniq⟩ := hP s c J σ hsp Ω _ _ hpt
    refine ⟨j, ?_, fun j' hj' => huniq j' ?_⟩
    · exact affine_point_injective hA'
        ((affine_point_comp (σ j) hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) x).symm.trans hj)
    · exact (affine_point_comp (σ j') hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j') U)) x).trans
        (congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hA'.fromSpec) hj'))
  exact hT _ _ _ J τ e he b

theorem UpperTheory.Gal.G3.pHodgeFun :
    PtsOfSplits → AlgSplit → AlgTr → ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := by
  intro hP hS hT k _ Z Y W p q r s _ _ c J _ σ hσ hsp U hU b
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf (fun i : {V : W.Opens // IsAffineOpen V ∧ V ≤ c ⁻¹ᵁ U} => i.1) (c ⁻¹ᵁ U) (fun i => homOfLE i.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hxV⟩
  · rintro ⟨V, hV, hVU⟩
    have key := cech_section_local_split hP hS hT p q s c J σ hσ hsp U hU V hV hVU b
    refine key.trans ((Finset.sum_congr rfl fun j _ => ?_).trans (map_sum (W.presheaf.map (homOfLE hVU).op).hom _ _).symm)
    change _ = ((σ j).app (s ⁻¹ᵁ U) ≫ W.presheaf.map (homOfLE (GlobalTheory.GalTrace.preimage_le (hσ j) U)).op ≫ W.presheaf.map (homOfLE hVU).op).hom b
    rw [← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
end
