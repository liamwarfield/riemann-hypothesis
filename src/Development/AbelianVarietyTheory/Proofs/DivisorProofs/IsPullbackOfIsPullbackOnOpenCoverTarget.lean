module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTarget
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTarget
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isPullback_of_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  intro X G S B β f g π w J Y P ψ e p q hψ hcov he hP hβ hf hr
  let ψ' : ∀ j, P j ⟶ pullback g π := fun j =>
    pullback.lift (p j ≫ ψ j) (q j) (by rw [Category.assoc]; exact (hP j).w)
  have hψ'f : ∀ j, ψ' j ≫ pullback.fst g π = p j ≫ ψ j := fun j => pullback.lift_fst _ _ _
  have hψ's : ∀ j, ψ' j ≫ pullback.snd g π = q j := fun j => pullback.lift_snd _ _ _
  have sq : ∀ j, IsPullback (ψ' j) (p j) (pullback.fst g π) (ψ j) := fun j =>
    (IsPullback.of_bot (v₁₁ := ψ' j) (v₂₁ := pullback.snd g π) (by rw [hψ's]; exact hP j)
      (hψ'f j).symm (IsPullback.of_hasPullback g π)).flip
  haveI : ∀ j, IsOpenImmersion (ψ' j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq j).flip (hψ j)
  have hc : ∀ z : (pullback g π : Scheme), ∃ j y, ψ' j y = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hcov (pullback.fst g π z)
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback (sq j) z y hy.symm
    exact ⟨j, t, ht⟩
  let c : X ⟶ pullback g π := pullback.lift β f w
  have hcf : c ≫ pullback.fst g π = β := pullback.lift_fst _ _ _
  have hce : ∀ j, e j ≫ c = ψ' j := fun j => by
    apply pullback.hom_ext
    · rw [Category.assoc, hcf, hβ, hψ'f]
    · rw [Category.assoc, pullback.lift_snd, hf, hψ's]
  have loc : ∀ j, IsPullback (e j) (𝟙 (P j)) c (ψ' j) := fun j => by
    haveI := he j
    refine (IsOpenImmersion.isPullback (𝟙 (P j)) (e j) (ψ' j) c
      (by rw [hce, Category.id_comp]) ?_).flip
    ext x
    change c x ∈ Set.range (ψ' j) ↔ x ∈ Set.range (e j)
    constructor
    · rintro ⟨y, hy⟩
      apply hr j x
      refine ⟨p j y, ?_⟩
      rw [← hcf, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ'f]
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hce]⟩
  have key : ∀ j : J, (MorphismProperty.isomorphisms Scheme) (pullback.snd c (ψ' j)) := fun j => by
    rw [← (loc j).isoPullback_inv_snd,
      MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)]
    exact MorphismProperty.isomorphisms.infer_property _
  have hiso : (MorphismProperty.isomorphisms Scheme) c :=
    IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers J P ψ' hc) fun j => key j
  haveI : IsIso c := hiso
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTargetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_isPullback_on_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  first | exact @GlobalTheory.Mum.isPullback_of_openCover_target | exact GlobalTheory.Mum.isPullback_of_openCover_target | (intros; apply GlobalTheory.Mum.isPullback_of_openCover_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechKS.isTangent_of_fibre : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a

  have hunit : η[A].left ≫ m = x0 ≫ η[t.G].left := by
    have hw : (η[A].left ≫ m) ≫ t.G.hom = (𝟙_ (Over (Sp K))).hom ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w η[A]]
    let p : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk (η[A].left ≫ m) hw
    have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    have hpp := hm.2 (𝟙_ (Over (Sp K))) 1 1 p p (by rw [h1]; rfl) (by rw [h1]; rfl)
    rw [_root_.mul_one, h1] at hpp
    have hp : p * p = p := Over.OverMorphism.ext hpp
    have hp1 : p = 1 := mul_eq_left.mp hp
    have := congrArg (fun q => q.left) hp1
    simp only [p, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom] at this
    rw [this]
    simp
  show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (u a).left = η[A].left
  apply hm.1.hom_ext
  · rw [Category.assoc, hu a, hunit, ← Category.assoc, ← Spec.map_comp]
    have hr : CommRingCat.ofHom (dualMap (ev x0 U.1 hU)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ CommRingCat.ofHom (ev x0 U.1 hU) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [dualMap, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
    rw [hr, Spec.map_comp, Category.assoc, (hv a).2, Hom.one_def, Over.comp_left, Over.toUnit_left,
      ← Category.assoc]
    congr 1
    exact GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  · rw [Category.assoc, Over.w (u a), Over.w η[A]]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    show _ = 𝟙 (Sp K)
    rw [← Spec.map_id]
    congr 1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a
  exact GlobalTheory.CechKS.isTangent_of_fibre (E := E) t U v hv x0 hU A m u hm hu a
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def IsFinSub {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S)
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)) : Prop :=
  (∀ V : S.Opens, IsAffineOpen V → ∀ a : Γ(S, V), (gp.app V).hom a ∈ F V) ∧
  (∀ (V V' : S.Opens) (hle : V' ≤ V), IsAffineOpen V → IsAffineOpen V' → ∀ x ∈ F V,
    ((Sp K).presheaf.map (homOfLE (gp.preimage_mono hle)).op).hom x ∈ F V') ∧
  (∀ V : S.Opens, IsAffineOpen V → ∀ (f : Γ(S, V)) (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ F (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ V)), y ∈ F V ∧
      ((Sp K).presheaf.map (homOfLE (gp.preimage_mono (S.basicOpen_le f))).op).hom y =
        ((Sp K).presheaf.map (homOfLE (gp.preimage_mono (S.basicOpen_le f))).op).hom ((gp.app V).hom f) ^ k * x) ∧
  (∀ V : S.Opens, IsAffineOpen V → ∃ t : Finset Γ(Sp K, gp ⁻¹ᵁ V), (∀ y ∈ t, y ∈ F V) ∧
    ∀ x ∈ F V, ∃ c : Γ(Sp K, gp ⁻¹ᵁ V) → Γ(S, V), x = ∑ y ∈ t, (gp.app V).hom (c y) * y)

abbrev resK {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V) :
    Γ(Sp K, gp ⁻¹ᵁ V) →+* Γ(Sp K, gp ⁻¹ᵁ W) :=
  ((Sp K).presheaf.map (homOfLE (gp.preimage_mono h)).op).hom

def finFam {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens) : Subring Γ(Sp K, gp ⁻¹ᵁ W) :=
  ⨅ i, (Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
    resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _))).comap (resK gp (inf_le_left : W ⊓ V i ≤ W))

theorem resK_app {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W : S.Opens} (h : W ≤ V) (a : Γ(S, V)) :
    resK gp h ((gp.app V).hom a) = (gp.app W).hom ((S.presheaf.map (homOfLE h).op).hom a) := by
  rw [resK, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, gp.naturality]
  rfl

theorem resK_resK {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {V W X : S.Opens} (h : W ≤ V) (h' : X ≤ W)
    (x : Γ(Sp K, gp ⁻¹ᵁ V)) : resK gp h' (resK gp h x) = resK gp (h'.trans h) x := by
  rw [resK, resK, resK, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem mem_finFam {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens) (x : Γ(Sp K, gp ⁻¹ᵁ W)) :
    x ∈ finFam gp V t W ↔ ∀ i, resK gp (inf_le_left : W ⊓ V i ≤ W) x ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
  simp [finFam, Subring.mem_iInf]

theorem finFam_range {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens) (a : Γ(S, W)) : (gp.app W).hom a ∈ finFam gp V t W := by
  rw [mem_finFam]
  intro i
  rw [resK_app]
  exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

theorem finFam_res {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W W' : S.Opens) (hle : W' ≤ W) (x : Γ(Sp K, gp ⁻¹ᵁ W))
    (hx : x ∈ finFam gp V t W) : resK gp hle x ∈ finFam gp V t W' := by
  rw [mem_finFam] at hx ⊢
  intro i
  have hii : W' ⊓ V i ≤ W ⊓ V i := inf_le_inf_right _ hle
  have e : resK gp (inf_le_left : W' ⊓ V i ≤ W') (resK gp hle x) =
      resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) := by
    rw [resK_resK, resK_resK]
  rw [e]
  have hm : resK gp hii (resK gp (inf_le_left : W ⊓ V i ≤ W) x) ∈ (Subring.closure _).map (resK gp hii) := ⟨_, hx i, rfl⟩
  rw [RingHom.map_closure] at hm
  refine Subring.closure_mono ?_ hm
  rintro _ ⟨y, hy | ⟨z, hz, rfl⟩, rfl⟩
  · obtain ⟨a, rfl⟩ := hy
    exact Or.inl ⟨_, (resK_app gp hii a).symm⟩
  · exact Or.inr ⟨z, hz, by rw [resK_resK]⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamPtsPull
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensPair

theorem lamPts_comp {S : Scheme.{0}} {B T T' : Over S} [GrpObj B] (f : T' ⟶ T) (x y : T ⟶ B) (l : Fin 4) :
    f.left ≫ GlobalTheory.PolDeg.lamPts x y l = GlobalTheory.PolDeg.lamPts (f ≫ x) (f ≫ y) l := by
  fin_cases l <;> simp [GlobalTheory.PolDeg.lamPts, ← Over.comp_left, MonObj.comp_mul]

theorem lamPts_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (l : Fin 4) :
    (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A).left ≫
      GlobalTheory.PolDeg.lamPts (fst D'.P.A D'.P.A ≫ T.pr i) (snd D'.P.A D'.P.A ≫ T.pr j) l =
    GlobalTheory.PolDeg.lamPts (if i = i₀ then fst D.P.A D.P.A else 1) (snd D.P.A D.P.A ^ m j i₀) l := by
  have h1 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      fst D'.P.A D'.P.A ≫ T.pr i = if i = i₀ then fst D.P.A D.P.A else 1 := by
    rw [lift_fst_assoc, Category.assoc, T.inc_pr']
    split_ifs <;> simp
  have h2 : (lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) : G2 D.P.A ⟶ G2 D'.P.A) ≫
      snd D'.P.A D'.P.A ≫ T.pr j = snd D.P.A D.P.A ^ m j i₀ := by
    rw [lift_snd_assoc, Category.assoc, Category.assoc, T.act_pr]
    have e : ∀ k, (snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then snd D.P.A D.P.A else 1 := fun k => by
      rw [Category.assoc, T.inc_pr']; split_ifs <;> simp
    rw [← Category.assoc]
    change preHom (snd D.P.A D.P.A ≫ T.inc i₀) (∏ k, T.pr k ^ m j k) = _
    rw [map_prod]
    simp only [map_zpow]
    change ∏ k, ((snd D.P.A D.P.A ≫ T.inc i₀) ≫ T.pr k) ^ m j k = _
    simp only [e]
    rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
  rw [lamPts_comp, h1, h2]

theorem xe_xi {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ i : Fin r) (a : D.X) : T.xe (T.xi i₀ a) i = if i = i₀ then a else 0 := by
  simp [Tens.xi, Pi.single_apply]

theorem c_zsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (n : ℤ) (b : D.X) : D.c (n • b) = D.c b ^ n := by
  let φ : D.X →+ Additive (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (D.c x)) (fun a b => by
      show Additive.ofMul (D.c (a + b)) = Additive.ofMul (D.c a * D.c b)
      rw [D.c_add]; rfl)
  exact congrArg Additive.toMul (map_zsmul φ n b)

theorem pt_pull {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (i₀ : Fin r) (m : Matrix (Fin r) (Fin r) ℤ) (a b : D.X) (a' b' : D'.X)
    (ha : ∀ i, T.xe a' i = if i = i₀ then a else 0) (hb : ∀ j, T.xe b' j = m j i₀ • b) :
    (lift (toUnit (TK R) ≫ D'.c a') (toUnit (TK R) ≫ D'.c b') : TK R ⟶ G2 D'.P.A) =
      lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) ≫
        lift (fst D.P.A D.P.A ≫ T.inc i₀) (snd D.P.A D.P.A ≫ T.inc i₀ ≫ T.act m) := by
  have c0 : D.c 0 = 1 := by
    have := c_zsmul D 0 a; rwa [zero_smul, zpow_zero] at this
  rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
  congr 1
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, ha, T.inc_pr']
    split_ifs <;> simp [c0]
  · refine T.lim.hom_ext fun ⟨i⟩ => ?_
    simp only [Fan.mk_π_app, Category.assoc]
    rw [T.c_pr, hb, c_zsmul, T.act_pr]
    have e : ∀ k, (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k = if k = i₀ then toUnit (TK R) ≫ D.c b else 1 := fun k => by
      rw [Category.assoc, Category.assoc, T.inc_pr']; split_ifs <;> simp
    calc toUnit (TK R) ≫ D.c b ^ m i i₀ = (toUnit (TK R) ≫ D.c b) ^ m i i₀ := map_zpow (preHom (toUnit (TK R))) _ _
      _ = ∏ k, ((toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ T.pr k) ^ m i k := by
        simp only [e]
        rw [Finset.prod_eq_single i₀ (fun k _ hk => by rw [if_neg hk, one_zpow]) (by simp), if_pos rfl]
      _ = (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) ≫ ∏ k, T.pr k ^ m i k := by
        change _ = preHom (toUnit (TK R) ≫ D.c b ≫ T.inc i₀) (∏ k, T.pr k ^ m i k)
        rw [map_prod]
        simp only [map_zpow]
        rfl
      _ = _ := by simp only [Category.assoc]

end GlobalTheory.TensPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGAGA

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ}

theorem top_le_of_lbPow (u : HolUnif A M g) (k : ℕ) (j : (lbPow M k).ι) {z : Fin g → ℂ}
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M k).U j) : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) :=
  GlobalTheory.top_le_preimage_mono _ (GlobalTheory.Cartier.lbPow_U M k j).le hz

def powFrame (u : HolUnif A M g) (k : ℕ) : HolUnif A (lbPow M k) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j z := u.fr (j PUnit.unit) z ^ k
  fr_hol j := ((u.fr_hol (j PUnit.unit)).mono fun _ hz => top_le_of_lbPow u k j hz).pow k
  fr_ne j z hz := pow_ne_zero _ (u.fr_ne _ z (top_le_of_lbPow u k j hz))
  fr_compat i j z hz := GlobalTheory.ThetaBundleSec.fr_pow_compat u z k i j
    ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).1 ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).2

theorem exists_isFnPow : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  intro g A _ hA M u Hm χ hM hAH k θ hθ
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := GlobalTheory.HolUnifSec.exists_isFn (powFrame u k) hA hp (GlobalTheory.isLB_lbPow hM k) hθ.1 (by
    intro l hl j z hz
    have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) := top_le_of_lbPow u k j hz
    have h1 := hθ.2 ⟨l, hl⟩ z
    have h2 := hAH.2.2.2 ⟨l, hl⟩ _ z hz'
    change θ (z + l) * u.fr (j PUnit.unit) (z + l) ^ k = θ z * u.fr (j PUnit.unit) z ^ k
    simp only [hermForm] at h1
    change θ (z + l) = _ at h1
    change u.fr (j PUnit.unit) z = _ * u.fr (j PUnit.unit) (z + l) at h2
    rw [h1, h2, mul_pow]
    ring)
  exact ⟨s, hs⟩

end GlobalTheory.ThetaGAGA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunctionStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_appellHumbert_thetaFunction : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  first | exact @GlobalTheory.ThetaGAGA.exists_isFnPow | exact GlobalTheory.ThetaGAGA.exists_isFnPow | (intros; apply GlobalTheory.ThetaGAGA.exists_isFnPow <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorBundleRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorBundleRigidification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensRig

theorem oneGen_isGen' {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem eta_eq_one {S : Scheme.{0}} (B : Over S) [GrpObj B] : (η[B] : 𝟙_ (Over S) ⟶ B) = 1 := by
  show _ = toUnit _ ≫ η[B]
  rw [toUnit_unique (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]

theorem eSec_tensφ {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {r : ℕ} (pr : Fin r → (A ⟶ B))
    (hpr : ∀ i, IsMonHom (pr i)) (k : (Fin r × Fin r) × Fin 4) : eSec A ≫ tensφ pr k = eSec B := by
  obtain ⟨⟨i, j⟩, m⟩ := k
  have hi : η[A] ≫ pr i = η[B] := IsMonHom.one_hom _
  have hj : η[A] ≫ pr j = η[B] := IsMonHom.one_hom _
  have key : ∀ x : A ⟶ B, η[A] ≫ x = η[B] → eSec A ≫ x.left = eSec B := fun x hx => by
    rw [eSec, eSec, ← Over.comp_left, hx]
  fin_cases m
  · refine key _ ?_
    rw [MonObj.comp_mul, hi, hj, eta_eq_one, _root_.mul_one]
  · exact key _ hi
  · exact key _ hj
  · refine key _ ?_
    rw [MonObj.comp_one, eta_eq_one]

end GlobalTheory.Mum.TensRig

open GlobalTheory.Mum.TensRig in
theorem GlobalTheory.Mum.TensRig.rig_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)), (∀ i, IsMonHom (pr i)) → ∀ (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' * gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  intro R _ _ D r W A' _ L' hL' pr hpr w hw
  have hform : FormEq (X := D.P.A.left) (Y := (𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (PEmpty.elim : PEmpty → _) PEmpty.elim
      (GlobalTheory.LamBiext.flatφ (tensφ pr) (fun _ : PUnit => eSec A'))
      (GlobalTheory.LamBiext.flatε (tensε W) (fun _ : PUnit => (1 : ℤ))) := by
    intro U _ h
    simp only [GlobalTheory.LamBiext.flatφ, GlobalTheory.LamBiext.flatε, eSec_tensφ pr hpr, _root_.one_mul, Finset.univ_eq_empty,
      Finset.prod_empty, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε]
    simp
  obtain ⟨t, ht, htv⟩ := exists_gen D.P.isLB hform (LB.oneGen D.P.L) (oneGen_isGen' _)
  obtain ⟨a, ha, hmaps⟩ := Transport.exists_transport
    (DVR.linComb_isLB L' hL' (fun _ : PUnit => eSec A') (fun _ => 1))
    (DVR.linComb_isLB _ (DVR.linComb_isLB D.P.L D.P.isLB (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A') (fun _ => 1))
    (LB.linCombIso w (fun _ : PUnit => eSec A') (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _)
    (GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t)
    (GlobalTheory.LamBiext.nest_isGen ht)
  refine ⟨a, ha, fun z J J' hJ hJ' => ?_⟩
  have hPM := (GlobalTheory.GtCubeCompare.maps_iff_pm w (fun _ : PUnit => eSec A') (fun _ => 1) a _).1 hmaps
  have hp : (toUnit (TK R)).left z ∈ LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (ptK η[A'] ≫ tensφ pr k)
  have hq : (toUnit (TK R)).left z ∈ LB.wchart L' (fun _ : PUnit => eSec A') (fun _ => J' (ptK η[A'])) :=
    Set.mem_iInter.2 fun _ => hJ' (ptK η[A'])
  have E := hPM _ (toUnit (TK R)).left z _ _ hp hq
  have L1 : gm (toUnit (TK R)).left z (LB.wchart (LB.LinComb D.P.L (tensφ pr) (tensε W)) (fun _ : PUnit => eSec A')
      (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k)))
      ((GlobalTheory.LamBiext.nest D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') (fun _ => 1) t).s
        (fun _ => fun k => J (ptK η[A'] ≫ tensφ pr k))) = 1 := by
    refine (gm_res _ z (GlobalTheory.LamBiext.nest_le D.P.L (tensφ pr) (tensε W) (fun _ : PUnit => eSec A') _) hp _).trans ?_
    exact (val_of t (toUnit (TK R)).left z J (fun p => J (ptK η[A'] ≫ tensφ pr p.2))
      (fun x => congrArg J (Category.assoc _ _ _).symm)).symm.trans ((htv _ _ z J hJ).trans (val_one _))
  rw [L1, Fintype.prod_unique, zpow_one] at E
  rw [val_pull hJ' a (toUnit (TK R)).left (𝟙 _),
    val_of a _ z J' (fun _ => J' (ptK η[A'])) (fun _ => by rw [Category.id_comp]; rfl), Category.id_comp, mul_comm]
  exact E.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorBundleRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorBundleRigidification : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)), (∀ i, IsMonHom (pr i)) → ∀ (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∃ rig : LB.Gen (L'.pull (eSec A')), rig.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val (LB.pullGen L' _ _ rig (toUnit (TK R)).left) (𝟙 _) z J' * gm (ptK η[A']) z _ (w.s (fun k => J (ptK η[A'] ≫ tensφ pr k), J' (ptK η[A']))) = 1 := by
  first | exact @GlobalTheory.Mum.TensRig.rig_exists | exact GlobalTheory.Mum.TensRig.rig_exists | (intros; apply GlobalTheory.Mum.TensRig.rig_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorMultCharacterize
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.MultEff

open CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := (unitAt_one z).ord_eq_zero

theorem mult_zero (z : X) : (0 : CartierDiv X).mult z = 0 := by
  rw [(isEqn_zero z).mult_eq, Units.val_one, ord_one]

theorem mult_neg (D : CartierDiv X) (z : X) : (-D).mult z = - D.mult z := by
  have h := mult_add D (-D) z
  rw [add_neg_cancel, mult_zero] at h
  omega

theorem ord_inv (u : X.functionFieldˣ) (z : X) :
    Scheme.ord ((u⁻¹ : X.functionFieldˣ) : X.functionField) z = - Scheme.ord (u : X.functionField) z := by
  have h := Scheme.ord_mul (x := z) u.ne_zero (u⁻¹).ne_zero
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, ord_one] at h
  omega

theorem IsEqn.of_specializes {D : CartierDiv X} {x z : X} {g : X.functionFieldˣ} (h : D.IsEqn x g)
    (hz : z ⤳ x) : D.IsEqn z g := by
  obtain ⟨U, hU, hg⟩ := h.exists_nhds
  exact hg z (hz.mem_open U.isOpen hU)

variable [GlobalTheory.IsNormalScheme X]

theorem regAt_iff_ord (x : X) (u : X.functionFieldˣ) :
    RegAt x (u : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (u : X.functionField) z := by
  rw [← regularAt_zero_iff, GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X (0 : CartierDiv X) x u]
  simp only [mult_zero, add_zero]

theorem unitAt_of_ord (x : X) (u : X.functionFieldˣ)
    (h : ∀ z, z ⤳ x → Scheme.ord (u : X.functionField) z = 0) : UnitAt x (u : X.functionField) := by
  rw [unitAt_iff u.ne_zero, ← Units.val_inv_eq_inv_val, regAt_iff_ord, regAt_iff_ord]
  exact ⟨fun z hz => (h z hz).ge, fun z hz => by rw [ord_inv, h z hz, neg_zero]⟩

theorem eff_supp_eq_of_mult : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X), (D.Eff ↔ ∀ z, 0 ≤ D.mult z) ∧ (∀ x, x ∈ D.supp ↔ ∃ z, z ⤳ x ∧ D.mult z ≠ 0) ∧ (∀ E : CartierDiv X, (∀ z, D.mult z = E.mult z) → D = E) ∧ ∀ (x : X) (g : X.functionFieldˣ), (∀ z, z ⤳ x → Scheme.ord (g : X.functionField) z = D.mult z) → D.IsEqn x g := by
  intro X _ _ _ D
  have hEff : ∀ F : CartierDiv X, F.Eff ↔ ∀ z, 0 ≤ F.mult z := by
    intro F
    refine ⟨fun h z => ?_, fun h x => ?_⟩
    · have := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X F z 1).1 (h z) z (specializes_refl z)
      simpa [Units.val_one, ord_one] using this
    · have := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg X F x 1).2 fun z _ => by simpa [Units.val_one, ord_one] using h z
      simpa using this
  refine ⟨hEff D, fun x => ⟨fun hx => ?_, fun ⟨z, hz, hm⟩ => ?_⟩, fun E h => ?_, fun x g h => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨g, hg⟩ := D.exists_isEqn x
    refine (hg.mem_supp_iff.1 hx) (unitAt_of_ord x g fun z hz => ?_)
    rw [← (IsEqn.of_specializes hg hz).mult_eq]
    exact hne z hz
  · exact hz.mem_closed D.supp.isClosed (mem_supp_of_mult_ne_zero hm)
  · have h1 : (D - E).Eff := (hEff _).2 fun z => by
      rw [sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    have h2 : (-(D - E)).Eff := (hEff _).2 fun z => by
      rw [mult_neg, sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    exact sub_eq_zero.1 (h1.eq_zero h2)
  · obtain ⟨g', hg'⟩ := D.exists_isEqn x
    refine hg'.iff_unitAt.2 ?_
    have e : ((g / g' : X.functionFieldˣ) : X.functionField) = (g : X.functionField) / g' :=
      Units.val_div_eq_div_val g g'
    rw [← e]
    refine unitAt_of_ord x _ fun z hz => ?_
    have hm := (IsEqn.of_specializes hg' hz).mult_eq
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, Scheme.ord_mul g.ne_zero (inv_ne_zero g'.ne_zero),
      ← Units.val_inv_eq_inv_val, ord_inv, h z hz, hm]
    ring

end GlobalTheory.Cartier.MultEff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatMul

variable {T : Scheme.{0}}

theorem whiskerRight_pb {H V : Over T} (q : V ⟶ H) (Y : Over T) :
    IsPullback (pullback.fst V.hom Y.hom) (q ▷ Y).left q.left (pullback.fst H.hom Y.hom) := by
  refine (IsPullback.of_right (h₁₁ := (q ▷ Y).left) (v₁₁ := pullback.fst V.hom Y.hom)
    (h₂₁ := q.left) (v₁₂ := pullback.fst H.hom Y.hom) ?_ (Over.whiskerRight_left_fst q)
    (IsPullback.of_hasPullback H.hom Y.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback V.hom Y.hom).flip

theorem whiskerLeft_pb (X : Over T) {A B : Over T} (q : A ⟶ B) :
    IsPullback (snd X A).left (X ◁ q).left q.left (snd X B).left := by
  have : IsPullback (snd X A) (X ◁ q) q (snd X B) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst X B) s.fst)
      (fun s => by simp) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
    · ext1
      · simp
      · simp [s.condition]
    · ext1
      · simp [← h₂]
      · simp [← h₁]
  exact this.map (Over.forget T)

theorem isIso_shear (H : Over T) [GrpObj H] : IsIso (lift μ[H] (snd H H)) := by
  refine ⟨⟨lift (fst H H * (snd H H)⁻¹) (snd H H), ?_, ?_⟩⟩
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, comp_mul, lift_fst, GrpObj.comp_inv, lift_snd, hμ, mul_inv_cancel_right,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  · have hμ : μ[H] = fst H H * snd H H := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    apply hom_ext
    · rw [Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd, inv_mul_cancel_right, Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]

theorem flat_mu (H : Over T) [GrpObj H] (hH : Flat H.hom) : Flat μ[H].left := by
  have e : μ[H] = lift μ[H] (snd H H) ≫ fst H H := by rw [lift_fst]
  have := isIso_shear H
  have : IsIso (lift μ[H] (snd H H)).left := (Over.forget T).map_isIso (lift μ[H] (snd H H))
  have hfst : Flat (fst H H).left := by
    have h1 : (fst H H).left = pullback.fst H.hom H.hom := by simp
    rw [h1]
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback H.hom H.hom).flip hH
  rw [e, Over.comp_left]
  infer_instance

theorem main : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom →
    Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  intro T H V _ e he hH
  have h1 : Flat (e ▷ V).left := MorphismProperty.of_isPullback (whiskerRight_pb e V)
    (inferInstance : Flat e.left)
  have h2 : Flat (H ◁ e).left := MorphismProperty.of_isPullback (whiskerLeft_pb H e)
    (inferInstance : Flat e.left)
  have h3 := flat_mu H hH
  have k : (fst V V ≫ e) * (snd V V ≫ e) = ((e ▷ V) ≫ (H ◁ e)) ≫ μ[H] := by
    rw [Hom.mul_def]
    congr 1
    apply hom_ext <;> simp
  rw [k, Over.comp_left, Over.comp_left]
  infer_instance

end GlobalTheory.Mum.FlatMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOpenPartGroupSchemeProductMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_openPart_groupScheme_productMap : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Flat H.hom → Flat ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  first | exact @GlobalTheory.Mum.FlatMul.main | exact GlobalTheory.Mum.FlatMul.main | (intros; apply GlobalTheory.Mum.FlatMul.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PullAction

section
open MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_lift_end (h : IsGrpPullback G' G f φ) (u : G ⟶ G) [IsMonHom u] :
    ∃ v : G' ⟶ G', IsMonHom v ∧ v.left ≫ φ = φ ≫ u.left := by
  let v : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w u, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hv : v.left ≫ φ = φ ≫ u.left := h.1.lift_fst _ _ _
  have inj : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w x = pushPt h.1.w y → x = y := fun T x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w x, Over.w y]))
  have pa : ∀ (T : Over S') (x : T ⟶ G'), pushPt h.1.w (x ≫ v) = pushPt h.1.w x ≫ u := fun T x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hv, Category.assoc])
  have pm : ∀ (T : Over S') (x y : T ⟶ G'), pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have p1 : ∀ (T : Over S'), pushPt h.1.w (1 : T ⟶ G') = 1 := fun T => by
    have := pm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have hm : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ v = (x ≫ v) * (y ≫ v) := fun T x y => inj T _ _ (by
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  have h1 : ∀ (T : Over S'), (1 : T ⟶ G') ≫ v = 1 := fun T => inj T _ _ (by
    rw [pa, p1, MonObj.one_comp])
  refine ⟨v, ⟨?_, ?_⟩, hv⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := hm (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

end

theorem exists_action_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  intro E _ _ _ H Dw l Xo c W w G₀ _ β₀ hβ
  have key : ∀ a : 𝓞 E, ∃ v : G₀ ⟶ G₀, IsMonHom v ∧ v.left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left := fun a =>
    haveI := Xo.univ.t.act.hom a
    exists_lift_end hβ _
  choose f₀ hf₀ using key
  refine ⟨f₀, hf₀, fun T x tT mm => ?_⟩
  have hp := hβ.1
  let γ : tT.G.left ⟶ G₀.left := hp.lift mm.φ (tT.G.hom ≫ x)
    (mm.cart.1.w.trans (by simp only [Category.assoc]))
  have hγ : γ ≫ β₀ = mm.φ := hp.lift_fst _ _ _
  have hw : γ ≫ G₀.hom = tT.G.hom ≫ x := hp.lift_snd _ _ _
  have hL : LBIso tT.PP.L (Xo.univ.t.PP.L.pull mm.φ) := mm.lin.imp fun _ h => h.1
  have hU := Xo.univ.t.PP.isLB
  refine ⟨γ, hβ.cancel (by rw [hγ, ← Category.assoc]; exact mm.cart) hw, hγ,
    LBIso.trans tT.PP.isLB (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
      (GlobalTheory.GenSpread.lbIso_pull_pull hU γ hγ.symm), fun a => ?_⟩
  apply hp.hom_ext
  · rw [Category.assoc, hγ, mm.act, Category.assoc γ, (hf₀ a).2, ← Category.assoc γ, hγ]
  · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.PullAction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_action_pullback_universalUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  first | exact @GlobalTheory.PullAction.exists_action_pull | exact GlobalTheory.PullAction.exists_action_pull | (intros; apply GlobalTheory.PullAction.exists_action_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOfMatRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.DiagMat

def act (M : Matrix (Fin 8) (Fin 8) ℤ) (X : Type) [AddCommGroup X] : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun c := fun v => ∑ u, M v u • c u
  map_zero' := by ext v; simp
  map_add' c d := by ext v; simp [smul_add, Finset.sum_add_distrib]

theorem act_apply (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) (v : Fin 8) :
    act M X c v = ∑ u, M v u • c u := rfl

theorem act_act (M N : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) :
    act M X (act N X c) = act (M * N) X c := by
  ext v
  simp only [act_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem act_one {X : Type} [AddCommGroup X] (c : Fin 8 → X) : act 1 X c = c := by
  ext v
  simp [act_apply, Matrix.one_apply]

theorem act_comp {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁] (M : Matrix (Fin 8) (Fin 8) ℤ)
    (π : X₀ →+ X₁) (c : Fin 8 → X₀) : act M X₁ (fun u => π (c u)) = fun u => π (act M X₀ c u) := by
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp [act_apply, map_sum, map_zsmul]

theorem matRel_iff (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) :
    MatRel W a b y y' ↔ act (W + W.transpose) X y' = Pi.single b (act (W + W.transpose) X y a) := by
  constructor
  · intro h; ext v; rw [act_apply, h v, Pi.single_apply]; rfl
  · intro h v; have := congrFun h v; rw [act_apply] at this; rw [this, Pi.single_apply]; rfl

end GlobalTheory.Poinc.Eq8.DiagMat


open GlobalTheory.Poinc.Eq8.DiagMat in
theorem GlobalTheory.Poinc.Eq8.exists_diag_of_matRel : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (Y X₀ X₁ : Type) [AddCommGroup Y] [AddCommGroup X₀] [AddCommGroup X₁] (m : Fin 8 → Fin 8 → (Y →+ Y)) (e₀ : Y ≃+ (Fin 8 → X₀)) (ρ : Y →+ (Fin 8 → X₁)), Function.Surjective ρ → (∀ a b y, MatRel W a b (e₀ y) (e₀ (m a b y))) → (∀ a b y, MatRel W a b (ρ y) (ρ (m a b y))) → ∃ π : X₀ →+ X₁, Function.Surjective π ∧ ∀ y u, ρ y u = π (e₀ y u) := by
  intro W hW Y X₀ X₁ _ _ _ m e₀ ρ hρ h₀ h₁
  set Q := W + W.transpose with hQ
  have hdet : IsUnit Q.det := by rw [hW.2]; exact isUnit_one
  have hQP : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have hPQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet

  let Ψ : (Fin 8 → X₀) →+ (Fin 8 → X₁) :=
    (act Q X₁).comp (ρ.comp ((e₀.symm : (Fin 8 → X₀) →+ Y).comp (act Q⁻¹ X₀)))
  have hΨ : ∀ z, Ψ (act Q X₀ (e₀ z)) = act Q X₁ (ρ z) := by
    intro z
    simp only [Ψ, AddMonoidHom.comp_apply, act_act, hPQ, act_one]
    simp
  have hE : ∀ a b c, Ψ (Pi.single b (c a)) = Pi.single b (Ψ c a) := by
    intro a b c
    set z := e₀.symm (act Q⁻¹ X₀ c) with hz
    have hc : act Q X₀ (e₀ z) = c := by simp [hz, act_act, hQP, act_one]
    have r0 := (matRel_iff W a b _ _).1 (h₀ a b z)
    have r1 := (matRel_iff W a b _ _).1 (h₁ a b z)
    rw [← hQ, hc] at r0
    rw [← hQ] at r1
    rw [← r0, hΨ, r1, ← hΨ, hc]
  let π : X₀ →+ X₁ := (Pi.evalAddMonoidHom (fun _ => X₁) 0).comp (Ψ.comp (AddMonoidHom.single (fun _ => X₀) 0))
  have hπ : ∀ b x, Ψ (Pi.single b x) = Pi.single b (π x) := by
    intro b x
    have := hE 0 b (Pi.single 0 x)
    simpa [π] using this
  have hdiag : ∀ c, Ψ c = fun u => π (c u) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hπ]
    rw [← Finset.univ_sum_single (fun u => π (c u))]
  have key : ∀ y u, ρ y u = π (e₀ y u) := by
    intro y u
    have h1 : act Q X₁ (ρ y) = fun u => π (act Q X₀ (e₀ y) u) := by rw [← hΨ, hdiag]
    have h2 := congrArg (act Q⁻¹ X₁) h1
    rw [act_act, hPQ, act_one, act_comp, act_act, hPQ, act_one] at h2
    exact congrFun h2 u
  refine ⟨π, ?_, key⟩
  intro x
  obtain ⟨y, hy⟩ := hρ (fun _ => x)
  exact ⟨e₀ y 0, by rw [← key, hy]⟩
end
