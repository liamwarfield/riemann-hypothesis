module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC

open ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

variable {L L' : Type} [Field L] [Field L']

def torusExtBC (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) :
    TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    grpB := inferInstance
    isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
    q := (Over.pullback f).map T.q
    q_hom := inferInstance
    q_flat := qB_flat f T.q T.q_flat
    q_surjective := qB_surj f T.q T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) (qB_sq f T.q) T.q_quasiCompact
    i := iB f T.X T.i
    i_hom := iB_hom f T.X T.i
    isKernel := iB_isKernel f T.X T.q T.i T.isKernel }

theorem torusRing_hom_ext {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (g h : torusRing ZU X ⟶ CommRingCat.of A)
    (w : ∀ χ : X, g.hom (AddMonoidAlgebra.single χ 1) = h.hom (AddMonoidAlgebra.single χ 1)) : g = h := by
  apply CommRingCat.hom_ext
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) w
  have hb : b = ((b.down : ℤ) : ULift ℤ) := by ext; simp
  have e : ∀ (n : ℤ) (r : torusRing ZU X ⟶ CommRingCat.of A),
      r.hom (AddMonoidAlgebra.single 0 ((n : ℤ) : ULift ℤ)) = (n : A) := fun n r => by
    have : (AddMonoidAlgebra.single (0 : X) ((n : ℤ) : ULift ℤ) : AddMonoidAlgebra (ULift ℤ) X) = (n : AddMonoidAlgebra (ULift ℤ) X) := by
      rw [AddMonoidAlgebra.intCast_def]
    exact (congrArg r.hom this).trans (map_intCast r.hom n)
  rw [hb, e, e]

def toZTorus (S : Scheme.{0}) (X : Type) [AddCommGroup X] : (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

theorem hT_toZTorus {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    hT f X ≫ toZTorus S X = toZTorus S' X :=
  pullback.lift_fst _ _ _

theorem splitTorus_left_ext {S T : Scheme.{0}} {X : Type} [AddCommGroup X] {a b : T ⟶ (splitTorus S X).left}
    (h₁ : a ≫ toZTorus S X = b ≫ toZTorus S X) (h₂ : a ≫ (splitTorus S X).hom = b ≫ (splitTorus S X).hom) : a = b :=
  pullback.hom_ext h₁ h₂

theorem point_hT {X : Type} [AddCommGroup X] (e : L →+* L') {A : Type} [CommRing A] (a : Sp A ⟶ Sp L')
    (t' : Over.mk a ⟶ splitTorus (Sp L') X) (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X)
    (h : ∀ χ, charVal t χ = charVal t' χ) : t'.left ≫ hT (spMap e) X = t.left := by
  have key : (t'.left ≫ toZTorus (Sp L') X : Sp A ⟶ _) = (t.left ≫ toZTorus (Sp L) X : Sp A ⟶ _) := by
    have p : Spec.preimage (t'.left ≫ toZTorus (Sp L') X : Sp A ⟶ _) =
        Spec.preimage (t.left ≫ toZTorus (Sp L) X : Sp A ⟶ _) :=
      torusRing_hom_ext _ _ fun χ => (h χ).symm
    have := congrArg Spec.map p
    rwa [Spec.map_preimage, Spec.map_preimage] at this
  refine splitTorus_left_ext ?_ ?_
  · rw [Category.assoc, hT_toZTorus]; exact key
  · rw [Category.assoc, hT_snd, ← Category.assoc, Over.w t', Over.w t]; rfl

def eBC (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    (e : T.B ≅ B') : (torusExtBC f T).B ≅ (Over.pullback f).obj B' :=
  (Over.pullback f).mapIso e

theorem eBC_hom (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    [GrpObj B'] (e : T.B ≅ B') (h : letI := T.grpB; IsMonHom e.hom) :
    letI := (torusExtBC f T).grpB; IsMonHom (eBC f T e).hom := by
  letI := T.grpB
  haveI := h
  exact (inferInstance : IsMonHom ((Over.pullback f).map e.hom))

theorem map_left_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

theorem quot_bc (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    (e : T.B ≅ B') : ((torusExtBC f T).q ≫ (eBC f T e).hom).left ≫ pullback.fst B'.hom f =
      pullback.fst G.hom f ≫ (T.q ≫ e.hom).left := by
  change ((Over.pullback f).map T.q ≫ (Over.pullback f).map e.hom).left ≫ _ = _
  rw [← Functor.map_comp]
  exact map_left_fst f _

theorem iB_point (e : L →+* L') {G : Over (Sp L)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp L) X ⟶ G) {A : Type} [CommRing A] (a : Sp A ⟶ Sp L')
    (t' : Over.mk a ⟶ splitTorus (Sp L') X) (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X)
    (h : ∀ χ, charVal t χ = charVal t' χ) :
    (t' ≫ iB (spMap e) X i).left ≫ pullback.fst G.hom (spMap e) = (t ≫ i).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, iB_h, ← Category.assoc, point_hT e a t' t h]

theorem torusOver_torusExtBC (e : L →+* L') {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) :
    TorusOver e T (torusExtBC (spMap e) T) (pullback.fst G.hom (spMap e)) := by
  letI := T.addCommGroup
  exact ⟨AddEquiv.refl _, fun A _ a t' t h => iB_point e T.i a t' t h⟩

theorem lbIso_square {X X' Y Y' : Scheme.{0}} {φ : X' ⟶ X} {β : Y' ⟶ Y} {ψ : X ⟶ Y} {ψ' : X' ⟶ Y'}
    (hc : ψ' ≫ β = φ ≫ ψ) {A : LB X} {A' : LB X'} {B : LB Y} {B' : LB Y'} (hB : B.IsLB) (hA' : A'.IsLB)
    (hB' : B'.IsLB) (hA : A.IsLB) (a : LBIso A' (A.pull φ)) (b : LBIso B' (B.pull β)) (h : LBIso A (B.pull ψ)) :
    LBIso A' (B'.pull ψ') := by
  have a1 : LBIso (A.pull φ) ((B.pull β).pull ψ') :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A φ φ rfl)
      (chartPullLinComb B β (fun _ : PUnit => ψ') (fun _ => ψ) (fun _ => 1) φ (fun _ => hc)) h
  have a2 : LBIso (B'.pull ψ') ((B.pull β).pull ψ') :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ ψ' ψ' rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ ψ' ψ' rfl) b
  have l1 := pull_isLB hA φ
  have l2 := pull_isLB (pull_isLB hB β) ψ'
  have l3 := pull_isLB hB' ψ'
  exact LBIso.trans hA' l1 l3 a (LBIso.trans l1 l2 l3 a1 a2.symm)

theorem exists_abPart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ∧ GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e P.τ P'.τ mK.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨PK, cK, sK, aK, rK, mK, hK⟩ := sabPull Out.CubePf.cubePull (spMap e) P.tK
  obtain ⟨PB, cB, sB, aB, rB, mB, hB⟩ := sabPull Out.CubePf.cubePull (spMap e) P.tB
  obtain ⟨mZ, hZ⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ P.m mK
  let tK' : SAB H (Sp L') := ⟨(Over.pullback (spMap e)).obj P.tK.G, IsSemiAbelian.pullback (spMap e) P.tK.G P.tK.semi,
    OAct.pullback (spMap e) P.tK.G P.tK.act, PK, cK, sK, aK, rK⟩
  let tB' : SAB H (Sp L') := ⟨(Over.pullback (spMap e)).obj P.tB.G, IsSemiAbelian.pullback (spMap e) P.tB.G P.tB.semi,
    OAct.pullback (spMap e) P.tB.G P.tB.act, PB, cB, sB, aB, rB⟩
  let τ' : TorusExtension tK'.G := torusExtBC (spMap e) P.τ
  let e' : τ'.B ≅ tB'.G := eBC (spMap e) P.τ P.e
  have hψ : (τ'.q ≫ e'.hom).left ≫ mB.φ = mK.φ ≫ (P.τ.q ≫ P.e.hom).left := by
    rw [hK, hB]
    exact quot_bc (spMap e) P.τ P.e
  have act' : ∀ a, tK'.act.act a ≫ τ'.q ≫ e'.hom = τ'.q ≫ e'.hom ≫ tB'.act.act a := fun a => by
    change (Over.pullback (spMap e)).map (P.tK.act.act a) ≫ (Over.pullback (spMap e)).map P.τ.q ≫
      (Over.pullback (spMap e)).map P.e.hom = (Over.pullback (spMap e)).map P.τ.q ≫
      (Over.pullback (spMap e)).map P.e.hom ≫ (Over.pullback (spMap e)).map (P.tB.act.act a)
    simp only [← Functor.map_comp]
    rw [P.act a]
  have pp' : LBIso tK'.PP.L (tB'.PP.L.pull (τ'.q ≫ e'.hom).left) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    obtain ⟨wB, gB, -⟩ := mB.lin
    exact lbIso_square hψ P.tB.PP.isLB tK'.PP.isLB tB'.PP.isLB P.tK.PP.isLB ⟨wK, gK⟩ ⟨wB, gB⟩ P.pp
  have hT : TorusOver e P.τ τ' mK.φ := by
    rw [hK]
    exact torusOver_torusExtBC e P.τ
  exact ⟨⟨tK', mZ, τ', tB', e', eBC_hom (spMap e) P.τ P.e P.e_hom, act', pp'⟩, mK, mB, hZ.symm, hψ.symm, hT⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c)
    (h' : genPt ξ ⤳ c') (s : X.presheaf.stalk c) :
    genMap ξ ⟨c', h'⟩ (X.presheaf.stalkSpecializes (specializes_of_eq hc) s) = genMap ξ ⟨c, h⟩ s := by
  subst hc
  simp [TopCat.Presheaf.stalkSpecializes_refl]

theorem closedPoint_specMap_fromSpecStalk {R : CommRingCat.{0}} [IsLocalRing R] (x : X)
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x ((Spec.map φ) (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

private theorem stalkSpecializes_comp_comp_eq_of_eq {x y : X} (h1 : x ⤳ y) (h2 : y ⤳ x) (hxy : x = y)
    {R : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ R) :
    X.presheaf.stalkSpecializes h2 ≫ X.presheaf.stalkSpecializes h1 ≫ g = g := by
  subst hxy
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem stalkSpecializes_stalkClosedPointTo {K : Type} [Field K] (x : X)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom φ.hom]
    (hc : (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint (CommRingCat.of K)) = x) :
    X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = φ := by
  have key := (SpecToEquivOfLocalRing (X := X) (R := CommRingCat.of K)).apply_symm_apply ⟨x, ⟨φ, inferInstance⟩⟩
  obtain ⟨h, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp key
  rw [show Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ from h2,
    TopCat.Presheaf.stalkCongr_hom]
  exact stalkSpecializes_comp_comp_eq_of_eq _ _ hc.symm φ

private theorem isLocalHom_of_field' {K K' : Type} [Field K] [Field K'] (f : K →+* K') : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · simp at ha
    · exact h.isUnit⟩

theorem valAt_of_field_map {K K' : Type} [Field K] [Field K'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (w : Spec (CommRingCat.of K) ⟶ X) (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K')
    (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') {a : Ω} {u : K} (hv : ValAt ξ w a u) :
    ValAt ξ w' a (f u) := by
  obtain ⟨h, s, hs, hr⟩ := hv
  subst e
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X.presheaf.stalk (centre w) ⟶ CommRingCat.of K',
      ψ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := ⟨_, rfl⟩
  haveI : IsLocalHom ψ.hom := by
    haveI := isLocalHom_of_field' f
    have hh : ψ.hom = f.comp (Scheme.stalkClosedPointTo w).hom := by
      subst hψ
      rfl
    rw [hh]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ f (Scheme.stalkClosedPointTo w).hom (isLocalHom_of_field' f)
      (Scheme.isLocalHom_stalkClosedPointTo w)
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk w
  have hw' : Spec.map (CommRingCat.ofHom f) ≫ w = Spec.map ψ ≫ X.fromSpecStalk (centre w) := by
    rw [hψ]
    erw [Spec.map_comp, Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·) hφ.symm
  rw [hw']
  have hc := closedPoint_specMap_fromSpecStalk (centre w) ψ
  have hc' : centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) = centre w := hc
  have h' : genPt ξ ⤳ centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) := by
    rw [hc']
    exact h
  refine ⟨h', X.presheaf.stalkSpecializes (specializes_of_eq hc') s, ?_, ?_⟩
  · exact (genMap_stalkSpecializes ξ hc' h h' s).trans hs
  · have H3 := stalkSpecializes_stalkClosedPointTo (centre w) ψ hc
    have H : (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
        Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk (centre w))).hom s = ψ.hom s :=
      congrArg (fun g => g.hom s) H3
    have hψs : ψ.hom s = f u := by
      rw [← hr]
      subst hψ
      rfl
    exact H.trans hψs

theorem valAt_complex : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  intro X Ω _ ξ L _ _ z σ a u hv
  exact valAt_of_field_map ξ _ _ σ (by rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm) hv

end GlobalTheory.CompanionTheory.Ar.RootHt.PullVal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_at_complex_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex | exact GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_complex <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBound
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {σ : Type} [Fintype σ]

theorem aeval_scale {R : Type} [CommRing R] {F : MvPolynomial σ ℤ} {n : ℕ} (hF : F.IsHomogeneous n) (c : R)
    (x : σ → R) : MvPolynomial.aeval (fun j => c * x j) F = c ^ n * MvPolynomial.aeval x F := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ j, m j = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_map_hom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : σ → A) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun j => f (t j)) F = f (MvPolynomial.aeval t F) :=
  by simpa using (MvPolynomial.comp_aeval_apply (f := t) f.toIntAlgHom F).symm

variable {Ω : Type} [Field Ω]

def IsFormQuot (x : σ → Ω) (i : σ) (b : Ω) : Prop :=
  ∃ (N n : ℕ) (G : MvPolynomial σ ℤ), N ≠ 0 ∧ G.IsHomogeneous n ∧
    MvPolynomial.aeval x G = (N : Ω) * x i ^ n * b

theorem isFormQuot_of_mem [CharZero Ω] {x : σ → Ω} {i : σ} (hi : x i ≠ 0) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x i)) : IsFormQuot x i b := by
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    refine ⟨1, 1, MvPolynomial.X j, one_ne_zero, MvPolynomial.isHomogeneous_X _ _, ?_⟩
    simp only [MvPolynomial.aeval_X, Nat.cast_one, one_mul, pow_one]
    field_simp
  | algebraMap r =>
    refine ⟨r.den, 0, MvPolynomial.C r.num, r.den_nz, MvPolynomial.isHomogeneous_C _ _, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    simp only [MvPolynomial.aeval_C, pow_zero, mul_one, eq_ratCast, eq_intCast, Rat.cast_def, map_intCast]
    field_simp
  | add a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', MvPolynomial.C (N' : ℤ) * MvPolynomial.X i ^ n' * G +
      MvPolynomial.C (N : ℤ) * MvPolynomial.X i ^ n * G', mul_ne_zero hN hN', ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n')).mul hG using 1
        omega
      · convert ((MvPolynomial.isHomogeneous_C _ _).mul
          ((MvPolynomial.isHomogeneous_X _ i).pow n)).mul hG' using 1
        omega
    · simp only [map_add (f := _), map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, he', eq_intCast,
        Int.cast_natCast, Nat.cast_mul, map_natCast]
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨N, n, G, hN, hG, he⟩ := ha
    obtain ⟨N', n', G', hN', hG', he'⟩ := hb
    refine ⟨N * N', n + n', G * G', mul_ne_zero hN hN', hG.mul hG', ?_⟩
    simp only [map_mul, he, he', Nat.cast_mul]
    ring

theorem common_denominator {κ : Type} [Fintype κ] {x : σ → Ω} {i : σ} {b : κ → Ω}
    (h : ∀ j, IsFormQuot x i (b j)) :
    ∃ (N n : ℕ) (F : κ → MvPolynomial σ ℤ), N ≠ 0 ∧ (∀ j, (F j).IsHomogeneous n) ∧
      ∀ j, MvPolynomial.aeval x (F j) = (N : Ω) * x i ^ n * b j := by
  classical
  choose N n G hN hG he using h
  refine ⟨∏ j, N j, ∑ j, n j, fun j => MvPolynomial.C ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : ℤ) *
    MvPolynomial.X i ^ (∑ l, n l - n j) * G j, Finset.prod_ne_zero_iff.2 fun j _ => hN j, fun j => ?_, fun j => ?_⟩
  all_goals have hle : n j ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · convert ((MvPolynomial.isHomogeneous_C _ _).mul
      ((MvPolynomial.isHomogeneous_X _ i).pow (∑ l, n l - n j))).mul (hG j) using 1
    omega
  · have hp : x i ^ (∑ l, n l) = x i ^ (∑ l, n l - n j) * x i ^ n j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hq : ((∏ l, N l : ℕ) : Ω) = (N j : Ω) * ((∏ l ∈ Finset.univ.erase j, N l : ℕ) : Ω) := by
      rw [← Nat.cast_mul, Finset.mul_prod_erase Finset.univ N (Finset.mem_univ j)]
    simp only [map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, he, eq_intCast, Int.cast_natCast,
      map_natCast]
    rw [hp, hq]
    ring

theorem aeval_ne_zero_of_unit {L S : Type} [Field L] [CharZero L] [CommRing S] (g : S →+* Ω)
    (hg : Function.Injective g) (φ : S →+* L) {x : σ → Ω} {w : σ → L} {i : σ} (hx : x i ≠ 0) (hw : w i ≠ 0)
    (t : σ → S) (ht : ∀ j, g (t j) = x j / x i) (ht' : ∀ j, φ (t j) * w i = w j)
    {F : MvPolynomial σ ℤ} {n N : ℕ} (hN : N ≠ 0) (hF : F.IsHomogeneous n) {e : S} (he : IsUnit e)
    (hFe : MvPolynomial.aeval x F = (N : Ω) * x i ^ n * g e) : MvPolynomial.aeval w F ≠ 0 := by
  have h1 : x = fun j => x i * g (t j) := funext fun j => by rw [ht, mul_div_cancel₀ _ hx]
  have h2 : MvPolynomial.aeval x F = x i ^ n * g (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h1]
    rw [aeval_scale hF, aeval_map_hom]
  have h3 : MvPolynomial.aeval t F = (N : S) * e := by
    apply hg
    apply mul_left_cancel₀ (pow_ne_zero n hx)
    rw [← h2, hFe, map_mul, map_natCast]
    ring
  have h4 : w = fun j => w i * φ (t j) := funext fun j => by rw [← ht', mul_comm]
  have h5 : MvPolynomial.aeval w F = w i ^ n * φ (MvPolynomial.aeval t F) := by
    conv_lhs => rw [h4]
    rw [aeval_scale hF, aeval_map_hom]
  rw [h5, h3, map_mul, map_natCast]
  exact mul_ne_zero (pow_ne_zero _ hw) (mul_ne_zero (Nat.cast_ne_zero.2 hN) (he.map φ).ne_zero)

end Forms

section Germs

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_unit_germ {p : Cpt ξ} (hinj : Function.Injective (genMap ξ p)) {s : Ω} (h : unitAt ξ p s) :
    ∃ e : X.presheaf.stalk p.1, IsUnit e ∧ genMap ξ p e = s := by
  obtain ⟨h0, ⟨e, rfl⟩, ⟨e', he'⟩⟩ := h
  refine ⟨e, IsUnit.of_mul_eq_one e' (hinj ?_), rfl⟩
  rw [map_mul, he', mul_inv_cancel₀ h0, map_one]

theorem unitAt_natCast [CharZero Ω] {L : Type} [Field L] [CharZero L] {zz : Spec (CommRingCat.of L) ⟶ X}
    (h : genPt ξ ⤳ centre zz) {r : ℕ} (hr : r ≠ 0) : unitAt ξ ⟨centre zz, h⟩ (r : Ω) := by
  have hu : IsUnit ((r : X.presheaf.stalk (centre zz))) := (inferInstance : IsLocalHom (Scheme.stalkClosedPointTo zz).hom).map_nonunit _ (IsUnit.mk0 _
      ((map_natCast (Scheme.stalkClosedPointTo zz).hom r).trans_ne ((Nat.cast_ne_zero (R := L)).2 hr)))
  obtain ⟨u, hu⟩ := hu
  have hv : genMap ξ ⟨centre zz, h⟩ (u : X.presheaf.stalk (centre zz)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine ⟨Nat.cast_ne_zero.2 hr, ⟨_, hv⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre zz))ˣ) : _), ?_⟩⟩
  rw [← hv]
  exact map_units_inv _ u

end Germs

theorem ratios_quotients_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE L _ _ z hz i k c hzi hzc
  classical
  obtain ⟨hblk, hvan⟩ := hz
  obtain ⟨zz, ⟨hsp, hco⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y hT L).1 z
    (fun k' => (hblk k').imp fun _ h => IsUnit.mk0 _ h) hvan
  let p : Cpt ξ := ⟨centre zz, hsp⟩
  have hinj : Function.Injective (genMap ξ p) := hT.gen.inj p
  have hfib : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := fun r hr hn => hn (unitAt_natCast hsp hr.ne_zero)
  obtain ⟨hyi, hrat⟩ := hco.2 k₀ i (IsUnit.mk0 _ hzi)
  obtain ⟨hyc, hrat'⟩ := hco.2 k c (IsUnit.mk0 _ hzc)
  have hgerm : ∀ i' : J k₀, ∃ t : X.presheaf.stalk (centre zz),
      genMap ξ p t = y ⟨k₀, i'⟩ / y ⟨k₀, i⟩ ∧ (Scheme.stalkClosedPointTo zz).hom t * z ⟨k₀, i⟩ = z ⟨k₀, i'⟩ := by
    intro i'
    obtain ⟨r, ⟨_, t, h1, h2⟩, h3⟩ := hrat i'
    exact ⟨t, h1, by rw [h2, h3]⟩
  choose t ht ht' using hgerm
  have hchart : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p := ⟨hyi, fun i' => ⟨t i', ht i'⟩⟩
  have hreg : ∀ j, y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ p := by
    intro j
    obtain ⟨r, ⟨_, u, h1, _⟩, _⟩ := hrat' j
    exact ⟨u, h1⟩
  choose s hsB hsU hsa using fun j => ((hE p hfib).2 i hchart).1 _ (hreg j)
  have hSU : unitAt ξ p (∏ j, s j) := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => (hsU j).1, Subring.prod_mem _ fun j _ => (hsU j).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact Subring.prod_mem _ fun j _ => (hsU j).2.2
  have hSa : ∀ j, (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩) ∈
      Algebra.adjoin ℚ (Set.range fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩) := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j), mul_right_comm]
    exact Subalgebra.mul_mem _ (hsa j) (Subalgebra.prod_mem _ fun l _ => hsB l)
  obtain ⟨N, n, F, hN, hF, he⟩ := common_denominator (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i)
    (b := fun j => (∏ j, s j) * (y ⟨k, j⟩ / y ⟨k, c⟩)) fun j =>
      isFormQuot_of_mem (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (i := i) hyi (hSa j)
  obtain ⟨e, heu, hee⟩ := exists_unit_germ hinj hSU
  refine ⟨n, F, hF, fun j => ?_, ?_⟩
  · rw [he j, he c, div_self hyc]
    field_simp
  · refine aeval_ne_zero_of_unit (x := fun i' : J k₀ => y ⟨k₀, i'⟩) (w := fun i' : J k₀ => z ⟨k₀, i'⟩) (i := i)
      (genMap ξ p) hinj (Scheme.stalkClosedPointTo zz).hom hyi hzi t ht ht' hN (hF c) heu ?_
    rw [he c, div_self hyc, _root_.mul_one, hee]

end GlobalTheory.CompanionTheory.Ar.BlockRatio
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_points_coord_ratio_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∀ (i : J k₀) (k : K) (c : J k), z ⟨k₀, i⟩ ≠ 0 → z ⟨k, c⟩ ≠ 0 → ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ), (∀ j, (F j).IsHomogeneous n) ∧ (∀ j, MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, c⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F c) * y ⟨k, j⟩) ∧ MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F c) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms | exact GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms | (intros; apply GlobalTheory.CompanionTheory.Ar.BlockRatio.ratios_quotients_of_forms <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructure
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructure
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.TorusAct

theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {T G : C}
    [MonObj T] [MonObj G] (i : T ⟶ G) [IsMonHom i] [Mono i] (f : G ⟶ G) [IsMonHom f] (u : T ⟶ T)
    (h : u ≫ i = i ≫ f) : IsMonHom u := by
  constructor
  · rw [← cancel_mono i, Category.assoc, h, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono i).1
    simp only [Category.assoc, h, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

theorem diagMap_eq_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X) :
    GlobalTheory.Diag.diagMap S u = GlobalTheory.SplitTorus.torusMap S u :=
  (GlobalTheory.SplitTorus.eq_torusMap_iff _ _).2 (GlobalTheory.Diag.diagMap_chi S u)

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]

theorem mono_i (τ : TorusExtension G) : letI := τ.addCommGroup; letI := τ.grpB; Mono τ.i := by
  letI := τ.addCommGroup
  letI := τ.grpB
  exact ⟨fun g h e => τ.isKernel.hom_ext e (toUnit_unique _ _)⟩

theorem exists_restrict (τ : TorusExtension G) (f : G ⟶ G) [IsMonHom f] :
    letI := τ.addCommGroup; letI := τ.grpB; ∀ (b : τ.B ⟶ τ.B), IsMonHom b → f ≫ τ.q = τ.q ≫ b →
      ∃ φ : τ.X →+ τ.X, GlobalTheory.SplitTorus.torusMap (Sp K) φ ≫ τ.i = τ.i ≫ f := by
  letI := τ.addCommGroup
  letI := τ.grpB
  intro b hb hq
  haveI := mono_i τ
  haveI := τ.i_hom
  have w : (τ.i ≫ f) ≫ τ.q = toUnit _ ≫ η := by
    rw [Category.assoc, hq, ← Category.assoc, τ.isKernel.w, Category.assoc, IsMonHom.one_hom]
  let u := τ.isKernel.lift (τ.i ≫ f) (toUnit _) w
  have hu : u ≫ τ.i = τ.i ≫ f := τ.isKernel.lift_fst _ _ _
  haveI : IsMonHom u := isMonHom_of_comp_mono τ.i f u hu
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨φ, hφ ▸ hu⟩

theorem exists_module_diagAct : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G)
    (O : Type) [CommRing O] (act : OAct O G), letI := τ.addCommGroup; letI := τ.grpB;
    (∀ a, ∃ b : τ.B ⟶ τ.B, IsMonHom b ∧ act.act a ≫ τ.q = τ.q ≫ b) →
      ∃ m : Module O τ.X, letI := m;
        ∀ a, (GlobalTheory.Diag.diagAct (Sp K) O τ.X).act a ≫ τ.i = τ.i ≫ act.act a := by
  intro K _ G _ τ O _ act
  letI := τ.addCommGroup
  letI := τ.grpB
  intro hb
  haveI := mono_i τ
  haveI := τ.i_hom
  have ex : ∀ a, ∃ φ : τ.X →+ τ.X, GlobalTheory.SplitTorus.torusMap (Sp K) φ ≫ τ.i = τ.i ≫ act.act a := fun a => by
    obtain ⟨b, h1, h2⟩ := hb a
    haveI := act.hom a
    exact exists_restrict τ _ b h1 h2
  choose φ hφ using ex
  have inj : ∀ {α β : τ.X →+ τ.X}, GlobalTheory.SplitTorus.torusMap (Sp K) α ≫ τ.i =
      GlobalTheory.SplitTorus.torusMap (Sp K) β ≫ τ.i → α = β := fun h =>
    GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 h)
  have h1 : φ 1 = AddMonoidHom.id τ.X := inj (by
    rw [hφ, act.one, GlobalTheory.SplitTorus.torusMap_id, Category.comp_id, Category.id_comp])
  have hm : ∀ a b, φ (a * b) = (φ a).comp (φ b) := fun a b => inj (by
    rw [hφ, act.mul, GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, hφ,
      ← Category.assoc _ τ.i, hφ, Category.assoc])
  have ha : ∀ a b, φ (a + b) = φ a + φ b := fun a b => inj (by
    rw [hφ, act.add, GlobalTheory.SplitTorus.torusMap_add, MonObj.mul_comp, hφ, hφ, MonObj.comp_mul])
  let ρ : O →+* AddMonoid.End τ.X := RingHom.mk' ⟨⟨φ, h1⟩, hm⟩ ha
  letI m : Module O τ.X := Module.compHom τ.X ρ
  refine ⟨m, fun a => ?_⟩
  have e : DistribSMul.toAddMonoidHom τ.X a = φ a := rfl
  rw [GlobalTheory.Diag.diagAct_act, e, diagMap_eq_torusMap, hφ]

end GlobalTheory.CompanionTheory.TorusAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionModuleStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_module_structure : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G) (O : Type) [CommRing O] (act : OAct O G), letI := τ.addCommGroup; letI := τ.grpB; (∀ a, ∃ b : τ.B ⟶ τ.B, IsMonHom b ∧ act.act a ≫ τ.q = τ.q ≫ b) → ∃ m : Module O τ.X, letI := m; ∀ a, (GlobalTheory.Diag.diagAct (Sp K) O τ.X).act a ≫ τ.i = τ.i ≫ act.act a := by
  first | exact @GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct | exact GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct | (intros; apply GlobalTheory.CompanionTheory.TorusAct.exists_module_diagAct <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExact
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExact
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieExact

theorem ker_fst_isNilpotent {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra R (DualNumber A)] (π : DualNumber A →ₐ[R] A)
    (h : ∀ b, π b = TrivSqZeroExt.fst b) : IsNilpotent (RingHom.ker (π : DualNumber A →+* A)) := by
  refine ⟨2, ?_⟩
  rw [pow_two]
  refine le_bot_iff.mp (Ideal.mul_le.mpr fun a ha b hb => ?_)
  have ha' : TrivSqZeroExt.fst a = 0 := by rw [← h]; exact ha
  have hb' : TrivSqZeroExt.fst b = 0 := by rw [← h]; exact hb
  have : a * b = 0 := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha', hb']
  simp [this]

theorem exists_lift_dual {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (A : Type) [Field A]
    (s : Spec (CommRingCat.of (DualNumber A)) ⟶ S) (x₀ : Spec (CommRingCat.of A) ⟶ X)
    (h : x₀ ≫ f = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ s) :
    ∃ x : Spec (CommRingCat.of (DualNumber A)) ⟶ X,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber A) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom
  have hloc : IsLocalHom π.hom := ⟨fun b hb => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hb⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) (O := ⊤) trivial
  refine GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (GlobalTheory.range_subset_opens_of_isLocalRing s ?_) (GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) =
        s (Spec.map π (IsLocalRing.closedPoint (CommRingCat.of A))) :=
      congr($h (IsLocalRing.closedPoint (CommRingCat.of A)))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R B _ _ _ _ _ _ π' hπ' φ
    have hsurj : Function.Surjective π' := fun a => ⟨TrivSqZeroExt.inl a, by rw [hπ']; rfl⟩
    have hnil := ker_fst_isNilpotent π' (fun b => by rw [hπ']; rfl)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ π' hsurj hnil,
      Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩

variable {S : Scheme.{0}}

theorem one_comp_hom {M N T : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : T ⟶ M) ≫ f = 1 := by
  simp [Hom.one_def, IsMonHom.one_hom]

noncomputable def zeroSec {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) : Over.mk x ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) (by
    simp only [Over.mk_left, Over.mk_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; rfl
    rw [this]; simp)

theorem isTanAt_iff {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ zeroSec x ≫ v = 1 :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t : Over.mk x ⟶ G => t.left) h⟩

end GlobalTheory.CompanionTheory.Ar.LieExact


open GlobalTheory.CompanionTheory.Ar.LieExact in
theorem GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  intro K _ G _ τ
  letI := τ.addCommGroup
  letI := τ.grpB
  intro A _ c
  have hq : IsMonHom τ.q := τ.q_hom
  have hi : IsMonHom τ.i := τ.i_hom
  refine ⟨fun v hv => ⟨fun h => ?_, ?_⟩, fun w hw => ?_⟩
  · have sq : v ≫ τ.q = toUnit _ ≫ η := h.trans Hom.one_def
    refine ⟨τ.isKernel.lift v (toUnit _) sq, ?_, τ.isKernel.lift_fst _ _ _⟩
    rw [isTanAt_iff]
    refine τ.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, τ.isKernel.lift_fst, one_comp_hom, (isTanAt_iff _ _ _).mp hv]
  · rintro ⟨w, -, rfl⟩
    rw [Category.assoc, τ.isKernel.w, ← Category.assoc, toUnit_unique (w ≫ toUnit _) (toUnit _),
      Hom.one_def]
  · obtain ⟨hs, -⟩ := GlobalTheory.torusExtension_smooth_geometricallyConnected G τ
    obtain ⟨x, hx1, hx2⟩ := exists_lift_dual τ.q.left A w.left
      (1 : Over.mk (spMap c) ⟶ G).left (by
        have h1 : ((1 : Over.mk (spMap c) ⟶ G) ≫ τ.q).left = (1 : Over.mk (spMap c) ⟶ τ.B).left := by
          rw [one_comp_hom]
        rw [Over.comp_left] at h1
        exact h1.trans hw.symm)
    refine ⟨Over.homMk x ?_, hx1, Over.OverMorphism.ext hx2⟩
    rw [← Over.w τ.q, ← Category.assoc, hx2, Over.w w]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_tangent_exact : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field | exact GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field | (intros; apply GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLift
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.LieTangent

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem centre_field_base {K K' : Type} [Field K] [Field K'] {X : Scheme.{0}} (φ : K →+* K')
    (z : Sp K ⟶ X) : centre (Spec.map (CommRingCat.ofHom φ) ≫ z) = centre z := by
  have : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K') = IsLocalRing.closedPoint K :=
    Subsingleton.elim _ _
  change (Spec.map (CommRingCat.ofHom φ) ≫ z) _ = z _
  rw [Scheme.Hom.comp_apply, this]

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_generise (M : LieModel G ξ E) (p : Cpt ξ) {y : X} (hy : genPt ξ ⤳ y) (c : y ⤳ p.1) {e : E}
    {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G} (h : M.Extends p e v) :
    M.Extends ⟨y, hy⟩ e (epsBase (R := X.presheaf.stalk p.1) (R' := X.presheaf.stalk y)
      (X.presheaf.stalkSpecializes c).hom (Scheme.SpecMap_stalkSpecializes_fromSpecStalk c) ≫ v) := by
  rw [LieModel.extends_iff] at *
  refine ⟨isTanAt_base _ _ h.1, ?_⟩
  rw [h.2, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, ← dualMap_comp]
  congr 3
  exact RingHom.ext fun s => (genMap_specializes p hy c s).symm

theorem valAt_lie_base {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (M : LieModel G ξ E) {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ z = z')
    (hg : genPt ξ ⤳ centre z') {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z' e (epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨hg, _, extends_generise M ⟨centre z, h1⟩ hg (centre_specializes φ z) hv, ?_⟩
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, spec_comp, ← dualMap_comp, ← dualMap_comp]
  congr 3
  exact congrArg (fun g => g.hom) (stalk_base φ z).symm

end

theorem pull_lie_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) := by
  intro X Ω _ ξ G _ Li _ _ M L _ _ z σ Bc _ _ MB x e v hv hl
  have hz : Spec.map (CommRingCat.ofHom σ) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) =
      spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc, spec_comp]
  have hg : genPt ξ ⤳ centre (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) := by
    obtain ⟨h1, -⟩ := hv
    rw [← hz, centre_field_base]
    exact h1
  refine ⟨epsBase σ hz ≫ v, valAt_lie_base σ M hz hg hv, ?_⟩
  unfold LieModel.Lifts at *
  change (Spec.map _ ≫ v.left) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.comp_id] at hl
  rw [hl, ← Category.assoc, spec_comp, ← dualMap_comp]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelValueLiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_value_lift : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.pull_lie_value | exact GlobalTheory.CompanionTheory.Ar.RootHt.pull_lie_value | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.pull_lie_value <;> assumption)
end
end
