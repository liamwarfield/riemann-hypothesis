module

public import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj
public import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness
public import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianNeighbourhood

def IsPtNb {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) : Prop :=
  s default = x ∧ (∀ j, IsIso (e j)) ∧ (∀ j, l j ≫ e j ≫ (a j).left = s) ∧
  (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
  (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧
  (∀ (j k : J) (f : j ⟶ k), l k ≫ Spec.map (CommRingCat.ofHom (D.map f).hom) = l j) ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (l' : Spec (CommRingCat.of Ω) ⟶ U'.left), l' ≫ b.left = s →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left ∧ l j ≫ e j ≫ g = l') ∧
  (∀ (U' : B.Etale) (b : U' ⟶ U) (j : J) (g g' : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left →
      g' ≫ b.left = (a j).left → l j ≫ e j ≫ g = l j ≫ e j ≫ g' →
      ∃ (k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g =
        Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ g')

def LeafSHNbSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left),
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (s : Spec (CommRingCat.of Ω) ⟶ U.left)
    (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t

def LeafSHLoc : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt

def LeafSHHens : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (c : Cocone D), IsColimit c → ∀ (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
  (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t → IsLocalRing c.pt →
  SH c.pt

theorem LeafSHNb_of (hS : LeafSHNbSys) (hL : LeafSHLoc) (hH : LeafSHHens) : LeafSHNb := by
  intro _ q _ k _ hq B U s0 x
  obtain ⟨Ω, _, _, s, J, _, _, D, c, hc, V, a, l, e, t, hP⟩ := hS U x
  obtain ⟨hs, he, hl, hcomp, ht, -, hcof, -⟩ := id hP
  refine ⟨J, inferInstance, inferInstance, D, c, hc, V, a, fun j => (l j ≫ e j) default, e, t, he, ?_, ?_, hcomp, ht,
    hH U x Ω s D c hc V a l e t hP (hL U x Ω s D c hc V a l e t hP), ?_⟩
  · intro j
    rw [← hs, ← hl j]
    rfl
  · intro j
    have := hq.map (Spec.preimage (e j ≫ (a j).left ≫ s0)).hom
    simpa using this
  · intro U' b y' hy'
    obtain ⟨l', hl', -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed b.left s y' (hy'.trans hs.symm)
    obtain ⟨j, g, hg, -⟩ := hcof U' b l' hl'
    exact ⟨j, g, hg⟩

end LateralTheory.E.StrictHenselianNeighbourhood
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFiniteness
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFiniteness

def LeafSpreadSmooth1 : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadLQFMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {CA CB A B : Scheme.{0}} (cB : CB ⟶ Sp Ω) (γ : CA ⟶ CB) (qB : B ⟶ Sp R) (g : A ⟶ B) (vA : CA ⟶ A)
    (vB : CB ⟶ B), (LocallyOfFinitePresentation qB ∧ QuasiCompact qB ∧ QuasiSeparated qB) →
    (LocallyOfFinitePresentation (g ≫ qB) ∧ QuasiCompact (g ≫ qB) ∧ QuasiSeparated (g ≫ qB)) →
    IsPullback vB cB qB (toR R) → IsPullback vA (γ ≫ cB) (g ≫ qB) (toR R) → γ ≫ vB = vA ≫ g →
    LocallyQuasiFinite γ →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (EA EB : Scheme.{0})
      (qB' : EB ⟶ Sp R') (h : EA ⟶ EB) (rA : EA ⟶ A) (rB : EB ⟶ B), IsPullback rB qB' qB (incl hR) →
      IsPullback rA (h ≫ qB') (g ≫ qB) (incl hR) → h ≫ rB = rA ≫ g → LocallyQuasiFinite h

def LeafSpreadLQFGraph : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (f : D0 ⟶ X) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsPullback v0 c0 q (toR R) → v0 ≫ f = e →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E0 : Scheme.{0})
      (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0), IsPullback r q' q (incl hR) →
      ∀ (hf' : (r ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
        LocallyQuasiFinite (pullback.lift q' (r ≫ f) hf'.symm)

def LeafBaseChangePreR : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR) ∧
      w0 ≫ r0 = v0 ∧ e1 ≫ r0 = r1 ≫ d1 ∧ e2 ≫ r1 = r2 ≫ d2

theorem incl_toK {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated) (hSm : LeafSpreadSmooth1)
    (hG : LeafSpreadLQFGraph) (hM : LeafSpreadLQFMap) (hB : LeafBaseChangePreR) :
    LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := by
  intro k _ X p _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 e he hc0 h1 h2 qf0 qf1 qf2 D0 D1 D2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨f0, f1, f2, p0, p1, p2, m1, m2⟩ := id hpre
  obtain ⟨S0, a0, g0, H0⟩ := hSep k Ω R hR c0 q v0 f0 hc0.2.1.toIsSeparated p0
  obtain ⟨S1, a1, g1, H1⟩ := hSep k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1.toIsSeparated p1
  obtain ⟨S2, a2, g2, H2⟩ := hSep k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1.toIsSeparated p2
  obtain ⟨T0, b0, k0, K0⟩ := hSm k Ω R hR c0 q v0 f0 hc0.2.2 p0
  obtain ⟨T1, b1, k1, K1⟩ := hSm k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.2 p1
  obtain ⟨T2, b2, k2, K2⟩ := hSm k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.2 p2
  obtain ⟨G, aG, gG, HG⟩ := hG k p Ω R hR c0 q v0 f e he hf f0 p0 hve qf0
  obtain ⟨M1, aM1, gM1, HM1⟩ := hM k Ω R hR c0 γ1 q d1 v1 v0 f0 f1 p0 p1 m1 qf1
  obtain ⟨M2, aM2, gM2, HM2⟩ := hM k Ω R hR (γ1 ≫ c0) γ2 (d1 ≫ q) d2 v2 v1 f1 f2 p1 p2 m2 qf2
  let T := S0 ⊔ S1 ⊔ S2 ⊔ T0 ⊔ T1 ⊔ T2 ⊔ G ⊔ M1 ⊔ M2
  have gT : T.FG := ((((((((g0.sup g1).sup g2).sup k0).sup k1).sup k2).sup gG).sup gM1).sup gM2)
  have lS0 : S0 ≤ T := (((((((le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have literatureStatementsS1 : S1 ≤ T := (((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have logSupBoundLevelFree : S2 ≤ T := ((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT0 : T0 ≤ T := (((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT1 : T1 ≤ T := ((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT2 : T2 ≤ T := (((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lG : G ≤ T := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have familyMassFirstBound : M1 ≤ T := (le_sup_right).trans le_sup_left
  have familyMassSecondBound : M2 ≤ T := le_sup_right
  have hRT : R ≤ T := a0.trans lS0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2, n0, n1, n2⟩ :=
    hB k Ω R T hRT c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  have hf' : (r0 ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
    rw [Category.assoc, hf, ← Category.assoc, Q0.w, Category.assoc, incl_toK]
  haveI := f0.2.1; haveI := f1.2.1; haveI := f2.2.1
  refine ⟨T, gT, E0, E1, E2, q', e1, e2, r0 ≫ f, w0, w1, w2, hf', ?_⟩
  exact ⟨H0 T lS0 hRT E0 q' r0 Q0, MorphismProperty.of_isPullback (P := @QuasiCompact) Q0 inferInstance,
    K0 T lT0 hRT E0 q' r0 Q0,
    H1 T literatureStatementsS1 hRT E1 (e1 ≫ q') r1 Q1, MorphismProperty.of_isPullback (P := @QuasiCompact) Q1 inferInstance,
    K1 T lT1 hRT E1 (e1 ≫ q') r1 Q1,
    H2 T logSupBoundLevelFree hRT E2 (e2 ≫ e1 ≫ q') r2 Q2, MorphismProperty.of_isPullback (P := @QuasiCompact) Q2 inferInstance,
    K2 T lT2 hRT E2 (e2 ≫ e1 ≫ q') r2 Q2,
    HG T lG hRT E0 q' r0 Q0 hf', HM1 T familyMassFirstBound hRT E1 E0 q' e1 r1 r0 Q0 Q1 n1,
    HM2 T familyMassSecondBound hRT E2 E1 (e1 ≫ q') e2 r2 r1 Q1 Q2 n2, P0, P1, P2, c1, c2,
    by rw [← Category.assoc, n0, hve]⟩

end LateralTheory.E.SpreadingOutQuasiFiniteness

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafObjGluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjGluePf

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

def DescAt (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D), FP q ∧ IsPullback v f q (toR R)

theorem toR_eq {R R' : Subalgebra k Ω} (h : R ≤ R') : toR R' ≫ incl h = toR R := by
  simp only [toR, incl]
  rw [← Spec.map_comp]
  rfl

theorem fp_snd {X Y Z : Scheme.{0}} (q : X ⟶ Z) (g : Y ⟶ Z) (hq : FP q) : FP (pullback.snd q g) := by
  obtain ⟨h1, h2, h3⟩ := hq
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem descAt_mono {R R' : Subalgebra k Ω} (h : R ≤ R') {X : Scheme.{0}} {f : X ⟶ Sp Ω}
    (hd : DescAt R f) : DescAt R' f := by
  obtain ⟨D, q, v, hq, hp⟩ := hd
  refine ⟨pullback q (incl h), pullback.snd q (incl h),
    pullback.lift v (f ≫ toR R') (by rw [hp.w, Category.assoc, toR_eq]), fp_snd _ _ hq, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst q (incl h)) (v₁₃ := q) (h₂₂ := incl h) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback q (incl h))
  rw [pullback.lift_fst, toR_eq]
  exact hp

def GlueData (R : Subalgebra k Ω) {X : Scheme.{0}} (f : X ⟶ Sp Ω) (U V : X.Opens) : Prop :=
  ∃ (DU DV DW : Scheme.{0}) (qU : DU ⟶ Sp R) (qV : DV ⟶ Sp R) (qW : DW ⟶ Sp R)
    (vU : U.toScheme ⟶ DU) (vV : V.toScheme ⟶ DV) (vW : (U ⊓ V).toScheme ⟶ DW) (φU : DW ⟶ DU) (φV : DW ⟶ DV),
    FP qU ∧ FP qV ∧ FP qW ∧ IsOpenImmersion φU ∧ IsOpenImmersion φV ∧ φU ≫ qU = qW ∧ φV ≫ qV = qW ∧
    IsPullback vU (U.ι ≫ f) qU (toR R) ∧ IsPullback vV (V.ι ≫ f) qV (toR R) ∧
    IsPullback vW ((U ⊓ V).ι ≫ f) qW (toR R) ∧
    vW ≫ φU = X.homOfLE inf_le_left ≫ vU ∧ vW ≫ φV = X.homOfLE inf_le_right ≫ vV

def LeafInclDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens) (R : Subalgebra k Ω), R.FG →
    DescAt R (U.ι ≫ f) → DescAt R (V.ι ≫ f) → DescAt R ((U ⊓ V).ι ≫ f) →
    ∃ R' : Subalgebra k Ω, R ≤ R' ∧ R'.FG ∧ GlueData R' f U V

def LeafGlueTwo : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω) (U V : X.Opens) (R : Subalgebra k Ω), U ⊔ V = ⊤ → GlueData R f U V → DescAt R f

theorem LeafObjGlue_of (hI : LeafInclDescend) (hG : LeafGlueTwo) : LeafObjGlue := by
  intro k _ Ω _ _ X f hf U V hUV ⟨R1, h1, d1⟩ ⟨R2, h2, d2⟩ ⟨R3, h3, d3⟩
  obtain ⟨R', -, hR', g⟩ := hI k Ω f hf U V (R1 ⊔ R2 ⊔ R3) ((h1.sup h2).sup h3)
    (descAt_mono (le_sup_left.trans le_sup_left) d1) (descAt_mono (le_sup_right.trans le_sup_left) d2)
    (descAt_mono le_sup_right d3)
  exact ⟨R', hR', hG k Ω f U V R' hUV g⟩

end LateralTheory.E.LeafObjGluePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTw0LocSplitOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocSplitPf

def LeafTw0LocGen : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec (tw q 0) U),
  Loc U fun V g => ∃ (e : Sec (tw q 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧ (e = 0 ∨ ∃ ζ : Prim q Γ(V, ⊤), e = twGen 0 ζ)

theorem baerU (q : ℕ) [NeZero q] : Module.Baer (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) := by
  intro I g
  let J : Ideal (ZMod q) :=
    { carrier := {y | (ULift.up y : ULift.{1} (ZMod q)) ∈ I}
      add_mem' := fun {a b} ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c {y} hy => by
        have := I.smul_mem (ULift.up c) hy
        exact this }
  let g' : J →ₗ[ZMod q] ZMod q :=
    { toFun := fun y => (g ⟨ULift.up y.1, y.2⟩).down
      map_add' := fun a b => by
        have := g.map_add ⟨ULift.up a.1, a.2⟩ ⟨ULift.up b.1, b.2⟩
        exact congrArg ULift.down this
      map_smul' := fun c a => by
        have := g.map_smul (ULift.up c) ⟨ULift.up a.1, a.2⟩
        exact congrArg ULift.down this }
  obtain ⟨h, hh⟩ := KStar.Selmer.zmod_baer J g'
  refine ⟨{ toFun := fun x => ULift.up (h x.down)
            map_add' := fun a b => congrArg ULift.up (h.map_add a.down b.down)
            map_smul' := fun c a => congrArg ULift.up (h.map_smul c.down a.down) }, ?_⟩
  intro x hx
  exact congrArg ULift.up (hh x.down hx)

theorem retract (q : ℕ) [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (x : M)
    (hx : ∀ c : ULift.{1} (ZMod q), c • x = 0 → c = 0) :
    ∃ r : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r x = 1 := by
  let f : ULift.{1} (ZMod q) →ₗ[ULift.{1} (ZMod q)] M := LinearMap.toSpanSingleton _ _ x
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc; exact hx c hc
  obtain ⟨r, hr⟩ := (baerU q).extension_property f hf LinearMap.id
  refine ⟨r, ?_⟩
  have := LinearMap.congr_fun hr 1
  simpa [f] using this

def LeafTw0GenFree : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)),
  twGen 0 ζ = 0 ∨ ∀ c : ULift.{1} (ZMod q), c • resGen 0 ζ = 0 → c = 0

theorem genSplit_of (hF : LeafTw0GenFree) (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) :
    twGen 0 ζ = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), r (resGen 0 ζ) = 1 := by
  rcases hF q V ζ with h | h
  · exact Or.inl h
  · exact Or.inr (retract q _ h)

section
variable {R : Type} [CommRing R]

theorem map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := by
  simp [Sec.map]

theorem map_res' {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  exact congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)
end

theorem LeafTw0LocSplit_of (h1 : LeafTw0LocGen) (h2 : LeafTw0GenFree) : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := by
  intro q _ U n a
  let I : (sgl (tw q 0)).X 0 ≅ tw q 0 := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q 0)
  obtain ⟨S, hS, hP⟩ := h1 q U n (fun k => Sec.map I.hom (a k))
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨e', c, hc, he'⟩ := hP V g hg
  have back : ∀ y : Sec ((sgl (tw q 0)).X 0) V, Sec.map I.inv (Sec.map I.hom y) = y := by
    intro y; refine (map_comp' I.hom I.inv y).symm.trans ?_; simp [Sec.map]
  refine ⟨Sec.map I.inv e', c, fun k => ?_, ?_⟩
  · rw [← back (Sec.res g (a k)), map_res' I.hom g (a k), hc k]
    exact map_smul (I.inv.hom.app (op V)).hom (c k) e'
  · rcases he' with rfl | ⟨ζ, rfl⟩
    · left; simp [Sec.map]
    · rcases genSplit_of h2 q V ζ with h0 | ⟨r, hr⟩
      · left; simp [h0, Sec.map]
      · right; refine ⟨r, ?_⟩
        convert hr using 2
        exact (map_comp' I.inv ((resAug (tw q 0)).f 0) (twGen 0 ζ)).symm

end LateralTheory.E.LeafTw0LocSplitPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPairRelPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafTripleFPPf

namespace LateralTheory.E.LeafPairRelPf

theorem incl_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' R'' : Subalgebra k Ω} (h : R ≤ R')
    (h' : R' ≤ R'') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]
  rfl

def LeafFactorStage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C E Y : Scheme.{0}} (c : C ⟶ Sp Ω) (p : E ⟶ Sp R) (w : C ⟶ E), FP p → ∀ (hs : IsPullback w c p (toR R))
    (f : Y ⟶ Sp R), LocallyOfFinitePresentation f → ∀ (a : C ⟶ Y), a ≫ f = c ≫ toR R →
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (g : pullback p (incl h) ⟶ Y),
      g ≫ f = pullback.snd p (incl h) ≫ incl h ∧
      pullback.lift w (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ g = a

theorem LeafPairRel_of (hO : LeafObjFP) (hF : LeafFactorStage) : LeafPairRel := by
  intro k _ Ω _ _ R hRfg C0 C1 c0 γ1 h1fp D0 q v0 hq hs
  obtain ⟨R1, hR1, E, p1, w, hp1, hsE⟩ := hO k Ω (γ1 ≫ c0) h1fp
  have h0 : R ≤ R ⊔ R1 := le_sup_left
  have h1 : R1 ≤ R ⊔ R1 := le_sup_right
  have hfg : (R ⊔ R1).FG := hRfg.sup hR1
  have hsE' := pb_lift h1 hsE
  have hlfp : LocallyOfFinitePresentation (pullback.snd q (incl h0)) := (fp_snd q (incl h0) hq).1
  obtain ⟨S, h, hS, g, hg1, hg2⟩ := hF k Ω (R ⊔ R1) hfg (γ1 ≫ c0) (pullback.snd p1 (incl h1)) _
    (fp_snd _ _ hp1) hsE' (pullback.snd q (incl h0)) hlfp
    (γ1 ≫ pullback.lift v0 (c0 ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hs.w))
    (by simp only [Category.assoc, pullback.lift_snd])
  refine ⟨S, h0.trans h, hS, pullback (pullback.snd p1 (incl h1)) (incl h),
    pullback.lift (g ≫ pullback.fst q (incl h0)) (pullback.snd _ _) ?_,
    pullback.lift (pullback.lift w ((γ1 ≫ c0) ≫ toR (R ⊔ R1)) (by rw [Category.assoc, toR_incl]; exact hsE.w))
      ((γ1 ≫ c0) ≫ toR S) (by simp only [Category.assoc, toR_incl, pullback.lift_snd]), ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc, incl_incl]
  · rw [pullback.lift_snd]; exact fp_snd _ _ (fp_snd _ _ hp1)
  · convert pb_lift h hsE' using 2
    simp only [pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hg2,
        Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]

end LateralTheory.E.LeafPairRelPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BridgeYfiPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.Bridge_yfiPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd
  LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling

structure Sys (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) (u : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  mem : ∀ j, u ∈ Set.range (a j).left
  tr : ∀ {j k : J}, (j ⟶ k) → (V k ⟶ V j)
  tr_id : ∀ j, tr (𝟙 j) = 𝟙 (V j)
  tr_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), tr (f ≫ g) = tr g ≫ tr f
  tr_a : ∀ {j k : J} (f : j ⟶ k), tr f ≫ a j = a k
  A : Type
  [ring : CommRing A]
  sh : SH A
  t : Sp A ⟶ U.left
  gY : ∀ j, pullback p (t ≫ U.hom) ⟶ YU p (V j)
  gW : ∀ j, pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι
  sq : ∀ j, prS p ι (t ≫ U.hom) ≫ gY j = gW j ≫ prU p ι (V j)
  gY_a : ∀ j, gY j ≫ resY p (a j) = tY p U t
  gW_a : ∀ j, gW j ≫ resYW p ι (a j) = tW p ι U t
  gY_tr : ∀ {j k : J} (f : j ⟶ k), gY k ≫ resY p (tr f) = gY j
  gW_tr : ∀ {j k : J} (f : j ⟶ k), gW k ≫ resYW p ι (tr f) = gW j
  injY : ∀ j (y : Ht q (sch.obj (YU p (V j))) m i), pull (ZMod q) (sch.map (gY j)) (tw q i) m y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resY p (tr f))) (tw q i) m y = 0
  surY : ∀ y : Ht q (sch.obj (pullback p (t ≫ U.hom))) (m - 1) i,
    ∃ (j : J) (y' : Ht q (sch.obj (YU p (V j))) (m - 1) i), pull (ZMod q) (sch.map (gY j)) (tw q i) (m - 1) y' = y
  injW : ∀ j (w : Ht q (sch.obj (pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι)) (m - 1) i),
    pull (ZMod q) (sch.map (gW j)) (tw q i) (m - 1) w = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resYW p ι (tr f))) (tw q i) (m - 1) w = 0

def Geo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Pack : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
  (u : U.left) (_ : Sys q i p ι U m u) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem Bridge_of_geo_pack (hG : Geo) (hP : Pack) : Bridge := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z u
  obtain ⟨S⟩ := hG hH q k hq i toK ι p hp U m u
  exact hP q i p ι U m u S z

end LateralTheory.E.Bridge_yfiPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSeparatedPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadSeparatedPf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (h' : S ≤ R') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]; rfl

theorem sep_of_stage {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (hS : S ≤ R') (hR : R ≤ R') {D E : Scheme.{0}} (q : D ⟶ Sp R) [IsSeparated (pullback.snd q (incl h))]
    (q' : E ⟶ Sp R') (r : E ⟶ D) (hE : IsPullback r q' q (incl hR)) : IsSeparated q' := by
  have hc : r ≫ q = (q' ≫ incl hS) ≫ incl h := by
    rw [Category.assoc, incl_comp]; exact hE.w
  have outer : IsPullback (pullback.lift r (q' ≫ incl hS) hc ≫ pullback.fst q (incl h)) q' q
      (incl hS ≫ incl h) := by
    rw [pullback.lift_fst, incl_comp]; exact hE
  have sq := IsPullback.of_right outer (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  exact MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance

def BC {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    pullback p t ⟶ pullback g t :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp [w]) (by simp)

def LeafClosedImmSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp R),
    (LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g) →
    (LocallyOfFinitePresentation (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧ QuasiSeparated (f ≫ g)) →
    IsClosedImmersion (BC f g (f ≫ g) rfl (toR R)) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ IsClosedImmersion (BC f g (f ≫ g) rfl (incl h))

def LeafDiagBC : Prop := ∀ {D Z T : Scheme.{0}} (q : D ⟶ Z) (t : T ⟶ Z),
    IsSeparated (pullback.snd q t) ↔ IsClosedImmersion (BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t)

theorem ci_congr {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    IsClosedImmersion (BC f g p w t) ↔ IsClosedImmersion (BC f g (f ≫ g) rfl t) := by
  subst w; rfl

theorem separated_base_change_iff_diagonal_closed_immersion_holds : LeafDiagBC := by
  intro D Z T q t
  have e1 : pullback.snd q t = (pullbackSymmetry q t).hom ≫ pullback.fst t q := by simp
  have e2 : IsSeparated (pullback.snd q t) ↔ IsSeparated (pullback.fst t q) := by
    rw [e1]; exact MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated) _ _
  rw [e2]
  have e3 : IsSeparated (pullback.fst t q) ↔ IsClosedImmersion (pullback.diagonal (pullback.fst t q)) :=
    ⟨fun h => h.isClosedImmersion_diagonal, fun h => ⟨h⟩⟩
  rw [e3, diagonal_pullback_fst, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  have : ((Over.pullback t).map (Over.homMk (pullback.diagonal q) : Over.mk q ⟶ Over.mk (pullback.snd q q ≫ q))).left
      = BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t := by
    apply pullback.hom_ext <;> simp only [BC, pullback.map, Category.comp_id] <;> rfl
  rw [this]

theorem of_two (hC : LeafClosedImmSpread) (hD : LeafDiagBC) :
    LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated := by
  intro k _ Ω _ _ R hR C D c q v hf hc hv
  obtain ⟨h1, h2, h3⟩ := hf
  have s0 : IsSeparated (pullback.snd q (toR R)) := by
    rw [← hv.isoPullback_inv_snd]; infer_instance
  have ci := (ci_congr _ _ _ _ _).1 ((hD q (toR R)).1 s0)
  have hfg : pullback.diagonal q ≫ pullback.snd q q ≫ q = q := by simp
  obtain ⟨S, h, hS, ci'⟩ := hC k Ω R hR (pullback.diagonal q) (pullback.snd q q ≫ q)
    ⟨inferInstance, inferInstance, inferInstance⟩ (by rw [hfg]; exact ⟨h1, h2, h3⟩) ci
  have := (hD q (incl h)).2 ((ci_congr _ _ _ (by simp) _).2 ci')
  exact ⟨S, h, hS, fun R' hS' hRR E q' r hE => sep_of_stage h hS' hRR q q' r hE⟩

end LateralTheory.E.LeafSpreadSeparatedPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafClosedSH0Of
section -- merged from Development.EtaleCohomology.EtaleSheaves.HensQuot
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfQuot
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem hensQuot {A C : Type} [CommRing A] [HenselianLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) : HenselianLocalRing C := by
  have hloc : IsLocalHom g := IsLocalHom.of_surjective g hg
  refine { is_henselian := ?_ }
  intro p hp a0 h0 h1
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.mpr (fun n => hg _)) hp
  obtain ⟨b0, rfl⟩ := hg a0
  have e : ∀ (Q : A[X]) (x : A), g (Q.eval x) = (Q.map g).eval (g x) := fun Q x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  have hb0 : P.eval b0 ∈ maximalIdeal A := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map g
    rw [e, hPmap] at this
    exact (mem_maximalIdeal _).mp h0 this
  have hb1 : IsUnit ((derivative P).eval b0) := by
    apply (isUnit_map_iff g _).mp
    rw [e, ← derivative_map, hPmap]; exact h1
  obtain ⟨b, hb, hbm⟩ := HenselianLocalRing.is_henselian P hPm b0 hb0 hb1
  refine ⟨g b, ?_, ?_⟩
  · change p.eval (g b) = 0
    rw [← hPmap, ← e, hb.eq_zero, map_zero]
  · rw [← map_sub, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp hbm

theorem sepQuot {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C] (g : A →+* C)
    (hg : Function.Surjective g) [IsLocalHom g] [IsSepClosed (ResidueField A)] : IsSepClosed (ResidueField C) := by
  have hbij : Function.Bijective (ResidueField.map g) := by
    refine ⟨(ResidueField.map g).injective, ?_⟩
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨residue A a, by simp⟩
  let e := RingEquiv.ofBijective _ hbij
  refine IsSepClosed.of_exists_root _ (fun p _ hirr hsep => ?_)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_eval₂_eq_zero_of_injective (e.symm : ResidueField C →+* ResidueField A)
    e.symm.injective p (degree_pos_of_irreducible hirr).ne' hsep
  refine ⟨e x, ?_⟩
  have h2 := congrArg e hx
  rw [map_zero] at h2
  rw [show (e : ResidueField A → ResidueField C) = (e : ResidueField A →+* ResidueField C) from rfl,
    Polynomial.hom_eval₂, RingEquiv.comp_symm] at h2
  exact h2

theorem shQuot : LeafSHQuot := by
  intro A _ hA W' ι' _
  obtain ⟨hH, hS⟩ := hA
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g :=
    hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  by_cases hC : Nontrivial Γ(W', ⊤)
  · right
    have hLC : IsLocalRing Γ(W', ⊤) := IsLocalRing.of_surjective' g.hom hg
    have hHC := hensQuot g.hom hg
    have : IsLocalHom g.hom := IsLocalHom.of_surjective g.hom hg
    exact ⟨hHC, sepQuot g.hom hg⟩
  · left
    rw [not_nontrivial_iff_subsingleton] at hC
    refine ⟨fun x => ?_⟩
    have h10 : (1 : Γ(W', ⊤)) = 0 := Subsingleton.elim _ _
    have := congrArg (W'.presheaf.germ ⊤ x trivial).hom h10
    rw [map_one, map_zero] at this
    exact one_ne_zero this

end LateralTheory.E.LeafClosedSH0PfQuot
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EmptySec
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0PfEmpty
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem emptySec : LeafEmptySec := by
  intro R _ F X hX
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := by
    exact Scheme.bot_mem_grothendieckTopology X
  have hT := Sheaf.isTerminalOfBotCover F X hb
  have hZ : IsZero (F.obj.obj (op X)) := hT.isZero
  exact (ModuleCat.isZero_iff_subsingleton.mp hZ)

end LateralTheory.E.LeafClosedSH0PfEmpty
end
end

namespace LateralTheory.E.LeafClosedSH0PfCut
open LateralTheory.E.LeafClosedSH0Pf

theorem LeafClosedSH0_of (hS : LeafSHSieve) : LateralTheory.E.LeafVanBPf.LeafClosedSH0 :=
  LateralTheory.E.LeafClosedSH0Pf.LeafClosedSH0_of hS LateralTheory.E.LeafClosedSH0PfQuot.shQuot
    LateralTheory.E.LeafClosedSH0PfEmpty.emptySec LateralTheory.E.LeafClosedSH0PfPrim.primLift

end LateralTheory.E.LeafClosedSH0PfCut
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoGenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoGenPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩
  · intro U y
    exact loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)
  · intro U x hx
    have hx0 : x = 0 := hx
    subst hx0
    exact loc_top U _ (fun V g => map_zero _)
  · intro U _
    exact h U

theorem LeafTensQIsoGen_of : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := by
  intro R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι
  exact LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι
    (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)

end LateralTheory.E.LeafTensQIsoGenPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSecInjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafSecInjPf

universe u v w

instance evaluationLeftAdjoint_preservesMono {C : Type u} [Category.{0} C] (R' : Type 1) [Ring R'] (c : C) :
    (evaluationLeftAdjoint (ModuleCat.{1} R') c).PreservesMonomorphisms where
  preserves {d₁ d₂} f _ := by
    rw [NatTrans.mono_iff_mono_app']
    intro t
    have e : ((evaluationLeftAdjoint (ModuleCat.{1} R') c).map f).app t =
        Limits.Sigma.map (fun _ : c ⟶ t => f) := by
      apply Limits.Sigma.hom_ext; intro h
      erw [Limits.Sigma.ι_desc]
    rw [e]
    have : HasCoproducts.{0} (ModuleCat.{1} R') := hasCoproducts_shrink.{0, 1}
    have : AB4OfSize.{0} (ModuleCat.{1} R') := AB4OfSize_shrink.{0, 1} _
    have : HasExactColimitsOfShape (Discrete (c ⟶ t)) (ModuleCat.{1} R') := AB4OfSize.ofShape _
    have : (MorphismProperty.monomorphisms (ModuleCat.{1} R')).IsStableUnderCoproductsOfShape (c ⟶ t) :=
      MorphismProperty.isStableUnderColimitsOfShape_monomorphisms _ _
    exact MorphismProperty.colimMap (W := MorphismProperty.monomorphisms (ModuleCat.{1} R'))
      (J := Discrete (c ⟶ t)) _ (fun _ => (inferInstance : Mono f))

theorem secInj (R : Type) [CommRing R] (F : Shv R) (hF : Injective F) (U : Scheme.{0}) :
    Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
      (evaluation _ _).obj (op U)).obj F) :=
  ((evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} R)) (op U)).comp
    (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))).map_injective _ hF

theorem LeafSecInj_of : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := by
  intro R _ F hF U
  have h := secInj R F hF U
  exact (Module.injective_iff_injective_object (ULift.{1} R) (Sec F U)).mpr h

end LateralTheory.E.LeafSecInjPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSHPtOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StrictHenselianPoint
open LateralTheory.E.E4 LateralTheory.E.LeafDegCut LateralTheory.E.LeafSHPtPf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem leafSHTop : LeafSHTop := by
  intro B U x J _ _ D c V a e t ht hcof
  obtain ⟨j0⟩ := (inferInstance : Nonempty J)
  constructor
  · intro O hxO
    have hU : Etale U.hom := U.prop
    let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by
      change Etale (O.ι ≫ U.hom); infer_instance)
    let b : U' ⟶ U := MorphismProperty.Over.homMk (A := U') (B := U) O.ι rfl
    obtain ⟨j, g, hg⟩ := hcof U' b ⟨x, hxO⟩ rfl
    rintro _ ⟨z, rfl⟩
    rw [← ht j, ← hg]
    have : Set.range (O.ι) ⊆ (O : Set U.left) := by rw [Scheme.Opens.range_ι]
    apply this
    exact ⟨(Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g) z, by
      rfl⟩
  · intro S hS
    obtain ⟨𝒰, _, h, hU⟩ := (Scheme.mem_smallGrothendieckTopology _ _).1 hS
    obtain ⟨i, ⟨u, hu⟩⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let fi : (𝒰.X i).asOverProp B (h i) ⟶ U := (𝒰.f i).asOverProp B
    refine ⟨_, fi, hU _ _ ⟨i⟩, ?_⟩
    obtain ⟨j, g, hg⟩ := hcof _ fi u hu
    exact ⟨Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ g, by
      rw [Category.assoc, Category.assoc, hg, ht j]⟩

theorem LeafSHPt_of (hN : LateralTheory.E.LeafSHPtPf.LeafSHNb) : LateralTheory.E.LeafInj0VPf.LeafSHPt :=
  LateralTheory.E.LeafSHPtPf.LeafSHPt_of hN leafSHTop

end LateralTheory.E.StrictHenselianPoint
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IdemLiftOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.IdempotentLifting

abbrev Aq : Type := AdjoinRoot (X ^ 2 - X : ℤ[X])

lemma monic_q : (X ^ 2 - X : ℤ[X]).Monic := by
  apply Polynomial.monic_X_pow_sub
  rw [degree_X]; decide

lemma integral_q : (algebraMap ℤ Aq).IsIntegral := by
  have := monic_q.finite_adjoinRoot
  exact fun x => Algebra.IsIntegral.isIntegral x

def toW {W : Type} [CommRing W] (e : W) (he : IsIdempotentElem e) : Aq →+* W :=
  AdjoinRoot.lift (Int.castRingHom W) e (by simp [sq, he.eq])

theorem IdemLift_of : IdemLift := by
  intro P _ _ W _ w _ e he
  let Z : Scheme.{0} := Spec (CommRingCat.of Aq)
  let t : Z ⟶ Spec (CommRingCat.of ℤ) := Spec.map (CommRingCat.ofHom (algebraMap ℤ Aq))
  have : IsIntegralHom t := IsIntegralHom.SpecMap_iff.2 integral_q
  let g : Spec (CommRingCat.of W) ⟶ Z := Spec.map (CommRingCat.ofHom (toW e he))
  let f₁ : Spec (CommRingCat.of W) ⟶ pullback (specZIsTerminal.from P) t :=
    pullback.lift w g (specZIsTerminal.hom_ext _ _)
  have H : w = f₁ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  let d := w.normalizationDesc f₁ (pullback.fst _ _) H
  let r : Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Aq)).inv (AdjoinRoot.root _)
  refine ⟨d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r), ?_⟩
  have key : w.toNormalization ≫ d ≫ pullback.snd (specZIsTerminal.from P) t = g := by
    rw [← Category.assoc, w.toNormalization_normalizationDesc, pullback.lift_snd]
  have h1 : w.toNormalization.appTop (d.appTop ((pullback.snd (specZIsTerminal.from P) t).appTop r)) =
      g.appTop r := by
    rw [← key]; simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of W)).hom (g.appTop r) = e := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp [r, toW, AdjoinRoot.lift_root]
  unfold phi
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact (congrArg _ h1).trans h2

end LateralTheory.E.IdempotentLifting
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FMrangePfQc
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf LateralTheory.E.FMrangePf

namespace LateralTheory.E.FMrangePfQc

theorem finset_idem {W : Type} [CommRing W] (hW : ProdACF W) (t : Finset W) :
    ∃ e : W, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum W, p ∈ (PrimeSpectrum.zeroLocus (t : Set W))ᶜ ↔ e ∉ p.asIdeal := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, IsIdempotentElem.zero, fun p => by simp⟩
  | insert a t _ ih =>
    obtain ⟨e, he, hpe⟩ := ih
    obtain ⟨f, u, hf, hu, rfl⟩ := hW.2 a
    refine ⟨f + e - f * e, ?_, fun p => ?_⟩
    · unfold IsIdempotentElem at *
      linear_combination (1 - e + (e * e - e)) * hf + (1 - f) * he
    · have hfe : f * (f + e - f * e) = f := by
        have := hf.eq; linear_combination (1 - e) * this
      have hef : e * (f + e - f * e) = e := by
        have := he.eq; linear_combination (1 - f) * this
      have key : f + e - f * e ∈ p.asIdeal ↔ f ∈ p.asIdeal ∧ e ∈ p.asIdeal := by
        constructor
        · intro h
          exact ⟨hfe ▸ p.asIdeal.mul_mem_left f h, hef ▸ p.asIdeal.mul_mem_left e h⟩
        · rintro ⟨h1, h2⟩
          exact p.asIdeal.sub_mem (p.asIdeal.add_mem h1 h2) (p.asIdeal.mul_mem_right e h1)
      have hfu : f * u ∈ p.asIdeal ↔ f ∈ p.asIdeal := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := hu.exists_right_inv
          have := p.asIdeal.mul_mem_right v h
          rwa [mul_assoc, hv, mul_one] at this
        · exact fun h => p.asIdeal.mul_mem_right u h
      have h1 := hpe p
      simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Finset.coe_insert, Set.insert_subset_iff] at h1 ⊢
      rw [key]
      simp only [SetLike.mem_coe, hfu, not_iff_not.mp h1]

theorem QcIdem_pf : QcIdem := by
  intro W _ hW U hU
  obtain ⟨t, ht⟩ := (@PrimeSpectrum.isCompact_isOpen_iff W _ (U : Set (Spec (CommRingCat.of W)))).1 ⟨hU, U.isOpen⟩
  obtain ⟨e, he, hpe⟩ := finset_idem hW t
  refine ⟨e, he, fun p => ?_⟩
  rw [← hpe p, ht]
  rfl

theorem FMrange_of (hI : IdemLift) : FMrange :=
  FMrange_of_leaves hI QcIdem_pf

end LateralTheory.E.FMrangePfQc
end
end
