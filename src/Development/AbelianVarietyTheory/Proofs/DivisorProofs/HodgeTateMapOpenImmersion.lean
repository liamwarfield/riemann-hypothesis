module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFinitePartPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFinitePartPullback
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem spMap_injective_divisor {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem ringHom_ext_Bt {S : Type} [CommRing S] {α β : Bt P' x0 hu →+* S}
    (h1 : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)))
    (h2 : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu)) : α = β := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    have e : (o ⊗ₜ[Localization.Away P'.f] b : Bt P' x0 hu) =
        algebraMap O (Bt P' x0 hu) (show O from o) * inB P' x0 hu b := by
      change _ = (o ⊗ₜ[Localization.Away P'.f] (1 : P'.B)) * ((1 : OL P' x0 hu) ⊗ₜ b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rw [e, map_mul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun h1 (show O from o)) (RingHom.congr_fun h2 b)
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

theorem aH_cancel_aff (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {S : Type} [CommRing S]
    (α β : Bt P' x0 hu →+* S)
    (h : spMap α ≫ (aH P' x0 hu hπ).left = spMap β ≫ (aH P' x0 hu hπ).left) : α = β := by
  have hO : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)) := by
    have e := congrArg (· ≫ G'.hom) h
    simp only [Category.assoc, Over.w (aH P' x0 hu hπ)] at e
    apply spMap_injective_divisor
    exact (GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) α).symm.trans (e.trans (GlobalTheory.HTMap.spc _ β))
  have hB : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu) := by
    have e := congrArg (· ≫ π) h
    simp only [Category.assoc, aH_left_π] at e
    have e2 : spMap (α.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (β.comp (inB P' x0 hu)) ≫ P'.u.left :=
      (GlobalTheory.HTMap.spc_assoc _ _ _).symm.trans (e.trans (GlobalTheory.HTMap.spc_assoc _ _ _))
    refine P'.fin.mono S _ _ (GlobalTheory.HTMap.FP.alg_ext ?_) e2
    change α.comp ((inB P' x0 hu).comp P'.str) = β.comp ((inB P' x0 hu).comp P'.str)
    rw [inB_str, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hO]
  exact ringHom_ext_Bt P' x0 hu hO hB

theorem aH_left_mono (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Mono (aH P' x0 hu hπ).left := by
  constructor
  intro T g h e
  refine Scheme.Cover.hom_ext T.affineCover _ _ fun i => ?_
  have ea := Spec.map_preimage (T.affineCover.f i ≫ g)
  have eb := Spec.map_preimage (T.affineCover.f i ≫ h)
  have key := aH_cancel_aff P' x0 hu hπ (Spec.preimage (T.affineCover.f i ≫ g)).hom
    (Spec.preimage (T.affineCover.f i ≫ h)).hom (by
      change Spec.map (Spec.preimage (T.affineCover.f i ≫ g)) ≫ _ = Spec.map (Spec.preimage (T.affineCover.f i ≫ h)) ≫ _
      rw [ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (T.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))
  exact ea.symm.trans ((congrArg Spec.map (CommRingCat.hom_ext key)).trans eb)

end GlobalTheory.FinPartAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFinitePartPullbackStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mono_finite_part_pullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left} (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)), Mono (aH P' x0 hu hπ).left := by
  first | exact @GlobalTheory.FinPartAt.aH_left_mono | exact GlobalTheory.FinPartAt.aH_left_mono | (intros; apply GlobalTheory.FinPartAt.aH_left_mono <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocal
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem push_pow {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (h : x₀.left = x.left ≫ π) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ π := by
  have h1 : (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ π := by
    let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
      show ((1 : T ⟶ G').left ≫ π) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
    have he : e * e = e := Over.OverMorphism.ext ((hg.2 T 1 1 e e rfl rfl).trans (by rw [_root_.mul_one]; rfl))
    have he1 : e = 1 := mul_eq_left.1 he
    exact (congrArg (fun z => z.left) he1).symm
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ, pow_succ]; exact hg.2 T _ _ _ _ ih h

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := congrArg (fun z => (Spec.preimage z).hom) h
  simpa using this

theorem lift_of_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg h S _ hS y hy
  obtain ⟨s0, hs0⟩ := hy
  let o : O →+* S := (Spec.preimage (y ≫ (torsion G' q).hom)).hom
  have ho : spMap o = y ≫ (torsion G' q).hom := Spec.map_preimage _
  let φ : R →+* S := o.comp x0
  have hu' : IsUnit (φ P'.f) := hu.map o
  have hw : (y ≫ (torsion.ι G' q).left ≫ π) ≫ t.G.hom = spMap φ ≫ ξ := by
    rw [Category.assoc, Category.assoc, hg.1.w, ← Category.assoc (torsion.ι G' q).left, Over.w (torsion.ι G' q),
      ← Category.assoc, ← ho, GlobalTheory.HTMap.spc_assoc]
  let w : Over.mk (spMap φ ≫ ξ) ⟶ t.G := GlobalTheory.HTMap.mkPt _ hw
  let T : Over (Sp O) := Over.mk (y ≫ (torsion G' q).hom)
  let yt : T ⟶ torsion G' q := Over.homMk y rfl
  let x : T ⟶ G' := yt ≫ torsion.ι G' q
  have hx : x ^ q = 1 := by
    show (yt ≫ torsion.ι G' q) ^ q = 1
    rw [← MonObj.comp_pow, GlobalTheory.KernelNoTorsion.torsionι_pow, MonObj.comp_one]
  let x₀ : Over.mk (T.hom ≫ (spMap x0 ≫ ξ)) ⟶ t.G := Over.homMk (x.left ≫ π) (by
    show (x.left ≫ π) ≫ t.G.hom = T.hom ≫ spMap x0 ≫ ξ
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w x])
  have hx₀ : x₀ ^ q = 1 := by
    refine Over.OverMorphism.ext ?_
    rw [push_pow hg x x₀ rfl q, hx]
    have := push_pow hg x x₀ rfl 0
    simp only [pow_zero] at this
    exact this.symm
  have hwq : w ^ q = 1 := GlobalTheory.HTMap.tors_of (g := 𝟙 _) (w := x₀) (by
    rw [Category.id_comp]
    show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
    rw [Category.assoc]) hx₀
  obtain ⟨β0, hβ0⟩ : ∃ β, P'.At φ w.left β := by
    refine GlobalTheory.HTMap.FP.at_open hu' rfl w hwq fun 𝔪 h𝔪 => ?_
    obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
    let gm : Bt P' x0 hu →+* IsLocalRing.ResidueField S := (Spec.preimage s0).hom
    have hgm : spMap gm = s0 := Spec.map_preimage _
    have e1 : spMap (gm.comp (algebraMap O (Bt P' x0 hu))) = spMap ((IsLocalRing.residue S).comp o) := by
      rw [← GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) gm, hgm, ← GlobalTheory.HTMap.spc o (IsLocalRing.residue S), ho]
      show s0 ≫ (Hs P' x0 hu).hom = _
      rw [← Over.w (jH P' x0 hu hg.1 h), ← Category.assoc, hs0, Category.assoc]
    have e2 := spMap_inj e1
    refine ⟨gm.comp (inB P' x0 hu), ?_, ?_⟩
    · show (gm.comp (inB P' x0 hu)).comp P'.str = (IsLocalRing.residue S).comp φ
      rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc, e2]
      rfl
    · show spMap (gm.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (IsLocalRing.residue S) ≫ y ≫ (torsion.ι G' q).left ≫ π
      rw [← GlobalTheory.HTMap.spc_assoc, hgm, ← aH_left_π P' x0 hu hg.1, ← jH_ι P' x0 hu hg.1 h, Over.comp_left,
        ← Category.assoc, ← Category.assoc, hs0, Category.assoc, Category.assoc]
  letI : Algebra O S := o.toAlgebra
  have hβ : β0.comp P'.str = (algebraMap O S).comp x0 := hβ0.1
  refine ⟨(ptOf P' x0 hu β0 hβ).left, ?_⟩
  let b : T ⟶ torsion G' q := Over.homMk ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) (by
    show ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) ≫ (torsion G' q).hom = y ≫ (torsion G' q).hom
    rw [Category.assoc, Over.w (jH P' x0 hu hg.1 h), Over.w (ptOf P' x0 hu β0 hβ)]
    exact ho)
  have hb : b = yt := by
    refine GlobalTheory.KernelNoTorsion.torsion_hom_ext (Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_))
    · have e1 : (b ≫ torsion.ι G' q).left = (ptOf P' x0 hu β0 hβ ≫ aH P' x0 hu hg.1).left := by
        show (ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left ≫ (torsion.ι G' q).left = _
        rw [← Over.comp_left, jH_ι]
        rfl
      rw [e1, ptOf_aH_π, hβ0.2]
      show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
      rw [Category.assoc]
    · rw [Over.w (b ≫ torsion.ι G' q), Over.w (yt ≫ torsion.ι G' q)]
  exact congrArg (fun z => z.left) hb
end GlobalTheory.FinPartAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocalStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_pow_eq_one_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  first | exact @GlobalTheory.FinPartAt.lift_of_residue | exact GlobalTheory.FinPartAt.lift_of_residue | (intros; apply GlobalTheory.FinPartAt.lift_of_residue <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersion
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartOpen

theorem isOpenImmersion_of_stalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f]
    (h : ∀ x : X, ∃ s : Spec (Y.presheaf.stalk (f x)) ⟶ X, s ≫ f = Y.fromSpecStalk (f x)) :
    IsOpenImmersion f := by
  have hbij : ∀ x : X, Function.Bijective (f.stalkMap x).hom := by
    intro x
    refine ⟨?_, f.stalkMap_surjective x⟩
    obtain ⟨s, hs⟩ := h x
    obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (Y.presheaf.stalk (f x))).symm.surjective s
    rw [SpecToEquivOfLocalRing_symm_apply] at hs
    dsimp only at hs
    have h1 : f x' = f x := by
      have := Scheme.Hom.comp_apply (Spec.map φ ≫ X.fromSpecStalk x') f (IsLocalRing.closedPoint _)
      rw [hs, Scheme.fromSpecStalk_closedPoint, GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint] at this
      exact this.symm
    have hx : x' = x := f.isClosedEmbedding.injective h1
    subst hx
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
    have key : f.stalkMap x' ≫ φ = 𝟙 _ := by
      have e := (SpecToEquivOfLocalRing Y (Y.presheaf.stalk (f x'))).symm.injective
        (a₁ := ⟨f x', f.stalkMap x' ≫ φ, inferInstance⟩) (a₂ := ⟨f x', 𝟙 _, inferInstance⟩)
        (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
            dsimp only
            rw [hs, Spec.map_id, Category.id_comp])
      rw [SpecToEquivOfLocalRing_eq_iff] at e
      obtain ⟨_, e⟩ := e
      simpa using e
    intro a b hab
    have := congrArg φ.hom hab
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key] at this
  have : Flat f := (Flat.iff_flat_stalkMap f).2 fun x => RingHom.Flat.of_bijective (hbij x)
  exact IsOpenImmersion.of_flat_of_mono f

theorem residue_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    ∃ s : Spec (Y.residueField (f x)) ⟶ X, s ≫ f = Y.fromSpecResidueField (f x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    exact ⟨IsLocalRing.residue _ c, rfl⟩
  have : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(f.residueFieldMap x).hom.injective, hs⟩
  refine ⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem finite_Bt : Module.Finite O (Bt P' x0 hu) := by
  haveI := P'.fin.finite
  exact inferInstanceAs (Module.Finite (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

theorem free_Bt : Module.Free O (Bt P' x0 hu) := by
  haveI := P'.fin.free
  exact inferInstanceAs (Module.Free (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

end

theorem isOpenImmersion_jH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg h
  set j := jH P' x0 hu hg.1 h
  haveI := P.semi.separated
  haveI := P.semi.smooth
  have hm : Mono j.left := by
    haveI := GlobalTheory.T.mono_finite_part_pullback P' x0 hu hg.1
    have e : j.left ≫ (torsion.ι P.G (p ^ n)).left = (aH P' x0 hu hg.1).left := by
      rw [← Over.comp_left, jH_ι]
    exact mono_of_mono_fac e
  have H0 : IsPullback (torsion.ι P.G (p ^ n)).left (torsion P.G (p ^ n)).hom (mulN P.G (p ^ n)).left η[P.G].left := by
    have h := (IsPullback.of_hasPullback (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).map (Over.forget _)
    have h' : (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).left = (torsion P.G (p ^ n)).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)))
    exact h' ▸ h
  have : LocallyOfFinitePresentation ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h3 := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp (mulN P.G (p ^ n)).left P.G.hom
  have : IsSeparated ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h4 := IsSeparated.of_comp (mulN P.G (p ^ n)).left P.G.hom
  have hZlfp : LocallyOfFinitePresentation (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H0 h3
  have hZsep : IsSeparated (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) H0 h4
  haveI := finite_Bt P' x0 hu
  haveI := free_Bt P' x0 hu
  have hHfin : IsFinite (Hs P' x0 hu).hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hHlfp : LocallyOfFinitePresentation (Hs P' x0 hu).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    haveI : Module.FinitePresentation 𝓞_ℂ_[p] (Bt P' x0 hu) := Module.finitePresentation_of_projective _ _
    exact RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation _ _)
  have hc : j.left ≫ (torsion P.G (p ^ n)).hom = (Hs P' x0 hu).hom := Over.w j
  have : IsFinite (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHfin
  have : LocallyOfFinitePresentation (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHlfp
  have : IsFinite j.left := IsFinite.of_comp j.left (torsion P.G (p ^ n)).hom
  have : IsClosedImmersion j.left := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, hm⟩
  have : LocallyOfFinitePresentation j.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j.left (torsion P.G (p ^ n)).hom
  refine isOpenImmersion_of_stalk j.left fun x => ?_
  obtain ⟨s, hs⟩ := residue_lift j.left x
  haveI : IsLocalRing ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) :=
    LocallyRingedSpace.isLocalRing _ _
  exact GlobalTheory.T.finite_part_pow_eq_one_local P' x0 hu hg h ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) (hS := this)
    ((torsion P.G (p ^ n)).left.fromSpecStalk (j.left x)) ⟨s, hs⟩

end GlobalTheory.FinPartOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersionStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_map_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  first | exact @GlobalTheory.FinPartOpen.isOpenImmersion_jH | exact GlobalTheory.FinPartOpen.isOpenImmersion_jH | (intros; apply GlobalTheory.FinPartOpen.isOpenImmersion_jH <;> assumption)
end
end
