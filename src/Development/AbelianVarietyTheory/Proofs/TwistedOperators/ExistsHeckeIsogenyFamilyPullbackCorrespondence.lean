module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_of_isGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : RigLB A) (Y : Scheme.{0})
    (x x' : Y ⟶ S) (Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left) (k : ℤ)
    (β : LB.Gen (isoLB A L Ψ k)), IsPointed A Ψ → β.IsGen → ∃ β', IsRigIso A L Ψ k β' := by
  intro S A _ L Y x x' Ψ k β hΨ hβ
  exact GlobalTheory.RigIsoDescent.exists_isRigIso_of_gen hΨ β hβ

end GlobalTheory.HeckeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

section Map

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] (h : Sp T ⟶ Z.Hk)

def hkLift {x : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) : Gx x ⟶ Z.o₁.t.G.left :=
  Z.m₁.cart.1.lift (snd (Over.mk x) Xo.univ.t.G).left ((fst (Over.mk x) Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx])

def hkLift₂ {x' : Sp T ⟶ Xo.X} (hx' : x' = h ≫ Z.π₂) : Gx x' ⟶ Z.o₂.t.G.left :=
  Z.m₂.cart.1.lift (snd (Over.mk x') Xo.univ.t.G).left ((fst (Over.mk x') Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx'])

variable {h} {x x' : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)

@[reassoc] theorem hkLift_φ : hkLift Z h hx ≫ Z.m₁.cm.F = (snd (Over.mk x) Xo.univ.t.G).left :=
  Z.m₁.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift_hom : hkLift Z h hx ≫ Z.o₁.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ h :=
  Z.m₁.cart.1.lift_snd _ _ _

def hkMap : Gx x ⟶ Gx x' :=
  pullback.lift (f := (Over.mk x').hom) (g := Xo.univ.t.G.hom) (fst (Over.mk x) Xo.univ.t.G).left
    (hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F) (by
      simp only [Category.assoc]
      rw [Z.m₂.cart.1.w, Over.w_assoc Z.ψ, hkLift_hom_assoc, ← hx']; rfl)

@[reassoc] theorem hkMap_fst :
    hkMap Z hx hx' ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

@[reassoc] theorem hkMap_snd :
    hkMap Z hx hx' ≫ (snd (Over.mk x') Xo.univ.t.G).left = hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F :=
  pullback.lift_snd _ _ _

end Map

section Square

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

theorem hkLift_isPullback (hx : x = h ≫ Z.π₁) :
    IsPullback (hkLift Z h hx) (fst (Over.mk x) Xo.univ.t.G).left Z.o₁.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₁.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₁) ?_ (hkLift_hom Z hx)
    Z.m₁.cart.1
  rw [hkLift_φ, ← hx]
  exact (IsPullback.of_hasPullback (Over.mk x).hom Xo.univ.t.G.hom).flip

theorem hkLift₂_isPullback (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift₂ Z h hx') (fst (Over.mk x') Xo.univ.t.G).left Z.o₂.t.G.hom h := by
  have hφ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
    Z.m₂.cart.1.lift_fst _ _ _
  have hhom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
    Z.m₂.cart.1.lift_snd _ _ _
  refine IsPullback.of_right (h₁₂ := Z.m₂.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₂) ?_ hhom
    Z.m₂.cart.1
  rw [hφ, ← hx']
  exact (IsPullback.of_hasPullback (Over.mk x').hom Xo.univ.t.G.hom).flip

theorem hkMap_isPullback (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift Z h hx) (hkMap Z hx hx') Z.ψ.left (hkLift₂ Z h hx') := by
  have hφ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
    Z.m₂.cart.1.lift_fst _ _ _
  have hhom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
    Z.m₂.cart.1.lift_snd _ _ _
  have heq : hkMap Z hx hx' ≫ hkLift₂ Z h hx' = hkLift Z h hx ≫ Z.ψ.left :=
    Z.m₂.cart.1.hom_ext (by rw [Category.assoc, hφ, hkMap_snd, Category.assoc])
      (by rw [Category.assoc, hhom, hkMap_fst_assoc, Category.assoc, Over.w Z.ψ, hkLift_hom])
  refine IsPullback.of_bot ?_ heq.symm (hkLift₂_isPullback Z hx')
  rw [hkMap_fst, Over.w Z.ψ]
  exact hkLift_isPullback Z hx

theorem hkMap_etale (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Etale (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Etale) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.1

theorem hkMap_surjective (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Surjective (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Surjective) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.2.1

end Square

section Fibre

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem isCan_hkLift {Ω : Type} [CommRing Ω] {χ : T →+* Ω} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x}
    (hx : x = h ≫ Z.π₁) (hp : IsCan χ pm) (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) :
    pm ≫ hkLift Z h hx = hkLift Z (spMap χ ≫ h) h₁ :=
  Z.m₁.cart.1.hom_ext (by rw [Category.assoc, hkLift_φ, hkLift_φ, hp.2.1])
    (by rw [Category.assoc, hkLift_hom, hkLift_hom, reassoc_of% hp.2.2])

theorem isFib_hkMap {Ω : Type} [CommRing Ω] (χ : T →+* Ω) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)
    {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} (hΨ : IsFib χ (hkMap Z hx hx') Ψ₁) :
    ∃ (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) (h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂), Ψ₁ = hkMap Z h₁ h₂ := by
  obtain ⟨pm, pm', hp, hp', e, f⟩ := hΨ
  have h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁ := by rw [hp.1, hx, Category.assoc]
  have h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂ := by rw [hp'.1, hx', Category.assoc]
  refine ⟨h₁, h₂, GlobalTheory.HeckeFrCompare.gx_ext (f.trans (hkMap_fst Z h₁ h₂).symm) ?_⟩
  rw [hkMap_snd Z h₁ h₂, ← isCan_hkLift_assoc Z hx hp h₁, ← hkMap_snd Z hx hx', ← reassoc_of% e, hp'.2.1]

end Fibre

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGeneratorHeckeIsogenyLineBundleQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGeneratorHeckeIsogenyLineBundleQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_gen_isoLB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  have hL₁ : Z.o₁.t.PP.L.IsLB := Z.o₁.t.PP.isLB
  have hL₂ : Z.o₂.t.PP.L.IsLB := Z.o₂.t.PP.isLB
  obtain ⟨w₁, hw₁, -⟩ := Z.m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := Z.m₂.lin
  have i₁ : LBIso Z.o₁.t.PP.L (Xo.univ.t.PP.L.pull Z.m₁.cm.F) := ⟨w₁, hw₁⟩
  have i₂ : LBIso Z.o₂.t.PP.L (Xo.univ.t.PP.L.pull Z.m₂.cm.F) := ⟨w₂, hw₂⟩
  have i₃ : LBIso (lbPow Z.o₁.t.PP.L (p ^ 2)) (Xo.univ.t.PP.L.pull (Z.ψ.left ≫ Z.m₂.cm.F)) :=
    GlobalTheory.ThetaAffineGlue.lbIso_comp (isLB_lbPow hL₁ _) hL₂ hL Z.isog.1.2.2.2.2.2 i₂
  have i₄ := GlobalTheory.ThetaAffineGlue.lbIso_pull i₃ (hkLift Z h hx)
  have i₅ := GlobalTheory.Spread.lbIso_pow_pull_comp hL hL₁ i₁ (hkLift Z h hx) (hkLift_φ Z hx).symm (p ^ 2)
  have i₆ := lbIso_lbPow_pull hL₁ (hkLift Z h hx) (p ^ 2)
  have i₇ := GlobalTheory.EmbVA.lbIso_pow hL (snd (Over.mk x) Xo.univ.t.G).left (p ^ 2) ((p : ℤ) ^ 2) (by push_cast; rfl)
  have i₈ := ((i₇.trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL _) _)
    (isLB_lbPow (pull_isLB hL₁ _) _) i₅.symm).trans (LB.isLB_linComb hL _ _) (isLB_lbPow (pull_isLB hL₁ _) _)
    (pull_isLB (isLB_lbPow hL₁ _) _) i₆).trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL₁ _) _)
    (pull_isLB hL _) i₄
  have e := (GlobalTheory.PrimNorm.lbIso_iff hL _ _ _ _).1 i₈
  rw [Fin.prod_univ_one, Fintype.prod_unique, zpow_one] at e
  refine (GlobalTheory.PrimNorm.hasGen_iff hL (isoφ Xo.univ.t.G (hkMap Z hx hx')) ![(p : ℤ) ^ 2, -1]).2 ?_
  rw [prod_iso', hkMap_snd, e, mul_inv_cancel]

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGeneratorHeckeIsogenyLineBundleQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_heckeIsogeny_lineBundle_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  first | exact @GlobalTheory.HeckeEx.exists_gen_isoLB | exact GlobalTheory.HeckeEx.exists_gen_isoLB | (intros; apply GlobalTheory.HeckeEx.exists_gen_isoLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

private theorem one_left_eq_eSec {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (y : Y ⟶ S) :
    (1 : Over.mk y ⟶ G).left = y ≫ eSec G := by
  rw [eSec]
  show (toUnit _ ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

private theorem eSec_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  rw [eSec]
  have := Over.w η[G]
  simpa using this

theorem hkMap_ptSec_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G := by
    apply Z.m₁.cart.1.hom_ext
    · rw [Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc,
        Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]
    · rw [Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]
      simp
  haveI := Z.isog.1.1
  have hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply GlobalTheory.HeckeFrCompare.gx_ext
  · rw [Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]
    rfl
  · rw [Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec,
      Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresPreservesOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUniversalIsogenyOnFibres_preserves_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  first | exact @GlobalTheory.HeckeEx.hkMap_ptSec_one | exact GlobalTheory.HeckeEx.hkMap_ptSec_one | (intros; apply GlobalTheory.HeckeEx.hkMap_ptSec_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresLinearAtRingPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresLinearAtRingPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open GlobalTheory.HeckeFrCompare (gx_ext toFib_fst toFib_fst_assoc toFib_snd)
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (push toFib)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

def overCast {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (Over.mk u : Over X) ⟶ Over.mk v :=
  Over.homMk (𝟙 _) (by simp [e])

@[simp] theorem overCast_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) : (overCast e).left = 𝟙 _ := rfl

theorem overCast_comp_left {T' X : Scheme.{0}} {u v : T' ⟶ X} (e : u = v) {G : Over X} (a : Over.mk v ⟶ G) :
    (overCast e ≫ a).left = a.left := by
  rw [Over.comp_left, overCast_left, Category.id_comp]

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem hkLift_act (hx : x = h ≫ Z.π₁) (r : 𝓞 E) :
    (Over.mk x ◁ Xo.univ.t.act.act r).left ≫ hkLift Z h hx = hkLift Z h hx ≫ (Z.o₁.t.act.act r).left := by
  refine Z.m₁.cart.1.hom_ext ?_ ?_
  · rw [Category.assoc, hkLift_φ, Category.assoc, Z.m₁.act, hkLift_φ_assoc, ← Over.comp_left, whiskerLeft_snd,
      Over.comp_left]
  · rw [Category.assoc, hkLift_hom, Category.assoc, Over.w, hkLift_hom, ← Category.assoc, ← Over.comp_left,
      whiskerLeft_fst]

def hkLiftPt (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (Over.mk (t ≫ h) : Over Z.Hk) ⟶ Z.o₁.t.G :=
  Over.homMk (toFib x t a ≫ hkLift Z h hx) (by
    rw [Category.assoc, hkLift_hom, toFib_fst_assoc]; rfl)

theorem hkLiftPt_left (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left = toFib x t a ≫ hkLift Z h hx := rfl

theorem hkLiftPt_φ (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    (hkLiftPt Z hx t a).left ≫ Z.m₁.cm.F = a.left := by
  rw [hkLiftPt_left, Category.assoc, hkLift_φ, toFib_snd]

theorem hkLiftPt_mul (hx : x = h ≫ Z.π₁) {T' : Scheme.{0}} (t : T' ⟶ Sp T) (a₁ a₂ : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    hkLiftPt Z hx t (a₁ * a₂) = hkLiftPt Z hx t a₁ * hkLiftPt Z hx t a₂ := by
  have e : (t ≫ h) ≫ Z.π₁ = t ≫ x := by rw [hx, Category.assoc]
  have key := Z.m₁.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁) (hkLiftPt Z hx t a₂) (overCast e ≫ a₁)
    (overCast e ≫ a₂) (by rw [overCast_comp_left, hkLiftPt_φ]) (by rw [overCast_comp_left, hkLiftPt_φ])
  refine Over.OverMorphism.ext (Z.m₁.cart.1.hom_ext ?_ ?_)
  · rw [hkLiftPt_φ, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · rw [Over.w, Over.w]

theorem push_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) {T' : Scheme.{0}} (t : T' ⟶ Sp T)
    (a : Over.mk (t ≫ x) ⟶ Xo.univ.t.G) :
    push (hkMap Z hx hx') t a = (hkLiftPt Z hx t a ≫ Z.ψ).left ≫ Z.m₂.cm.F := by
  rw [push, hkMap_snd, Over.comp_left, hkLiftPt_left]
  simp only [Category.assoc]

theorem isLinHom_hkMap (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : IsLinHom (hkMap Z hx hx') := by
  haveI : IsMonHom Z.ψ := Z.isog.1.1
  refine ⟨hkMap_fst Z hx hx', fun T' t a₁ a₂ b₁ b₂ h₁ h₂ => ?_, fun r => ?_⟩
  · have e : (t ≫ h) ≫ Z.π₂ = t ≫ x' := by rw [hx', Category.assoc]
    have key := Z.m₂.cart.2 (Over.mk (t ≫ h)) (hkLiftPt Z hx t a₁ ≫ Z.ψ) (hkLiftPt Z hx t a₂ ≫ Z.ψ) (overCast e ≫ b₁)
      (overCast e ≫ b₂) (by rw [overCast_comp_left, h₁, push_hkMap]) (by rw [overCast_comp_left, h₂, push_hkMap])
    rw [push_hkMap, hkLiftPt_mul, MonObj.mul_comp, ← key, ← MonObj.comp_mul, overCast_comp_left]
  · have w : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (snd (Over.mk z) Xo.univ.t.G).left =
        (snd (Over.mk z) Xo.univ.t.G).left ≫ (Xo.univ.t.act.act r).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
    have w₀ : ∀ z : Sp T ⟶ Xo.X, (Over.mk z ◁ Xo.univ.t.act.act r).left ≫ (fst (Over.mk z) Xo.univ.t.G).left =
        (fst (Over.mk z) Xo.univ.t.G).left := fun z => by
      rw [← Over.comp_left, whiskerLeft_fst]
    have hψ : (Z.o₁.t.act.act r).left ≫ Z.ψ.left = Z.ψ.left ≫ (Z.o₂.t.act.act r).left := by
      rw [← Over.comp_left, Z.isog.1.2.2.2.2.1 r, Over.comp_left]
    refine gx_ext ?_ ?_
    · rw [Category.assoc, hkMap_fst, w₀, Category.assoc, w₀, hkMap_fst]
    · rw [Category.assoc, hkMap_snd, hkLift_act_assoc, reassoc_of% hψ, Z.m₂.act, Category.assoc, w,
        hkMap_snd_assoc]

end GlobalTheory.HeckeEx

end

theorem GlobalTheory.HeckeEx.isLinHom_hkMap_target : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), IsLinHom (hkMap Z hx hx') :=
  fun _ _ _ _ _ _ _ _ _ _ _ Z _ _ _ _ _ hx hx' => GlobalTheory.HeckeEx.isLinHom_hkMap Z hx hx'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeUniversalIsogenyOnFibresLinearAtRingPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUniversalIsogenyOnFibres_linear_at_ringPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), IsLinHom (hkMap Z hx hx') := by
  first | exact @GlobalTheory.HeckeEx.isLinHom_hkMap_target | exact GlobalTheory.HeckeEx.isLinHom_hkMap_target | (intros; apply GlobalTheory.HeckeEx.isLinHom_hkMap_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.HeckePoint GlobalTheory.HeckeFrCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem isHkIsog_hkMap (Z : Corr Xo P p i) (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z.Hk) (C : Subgroup (Over.mk (z ≫ Z.π₁) ⟶ Xo.univ.t.G))
    (hC : Z.toKerScheme.Carries z (z ≫ Z.π₁) C) :
    ∃ ψp, IsHkIsog p (z ≫ Z.π₁) (z ≫ Z.π₂) C ((conj _ _).symm (hkMap Z (h := z) rfl rfl)) ψp := by
  obtain ⟨-, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left := (swap _).inv ≫ hkLift Z z rfl
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := by
    simp only [α, Category.assoc, hkLift_φ, swap_inv_snd]
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := by
    simp only [α, Category.assoc, hkLift_hom, swap_inv_fst_assoc]
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  have q₁ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.fst _ _ = α ≫ Z.ψ.left ≫ Z.m₂.cm.F := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.fst _ _ = _
    simp only [α, Category.assoc, swap_hom_fst, hkMap_snd, hkMap_snd_assoc]
  have q₂ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.snd _ _ = _
    simp only [Category.assoc, swap_hom_snd, hkMap_fst, hkMap_fst_assoc, swap_inv_fst]
  refine ⟨ψp, by rw [Category.assoc, Category.assoc, Z.base₂], q₂,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, q₁, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, q₂, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P₁ := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P₂ := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P₁ hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P₂ n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P₁.isAb P₂.isAb P₁.isLB P₂.isLB hom
      hiso hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

theorem exists_isHeckeFam_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X), x = h ≫ Z.π₁ → x' = h ≫ Z.π₂ → ∃ Ψ : Gx x ⟶ Gx x', IsHeckeFam P p i Ψ ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
  intro E _ _ _ H Dw l Xo P p i Z hA T _ h x x' hx hx'
  have hcop : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd hA.2.2.1).2 hA.2.2.2.2
  have hfib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X)
      (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ (hkMap Z hx hx') Ψ₁ →
        Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
          IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁ ∧
            Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
    intro Ω _ _ χ x₁ x₁' Ψ₁ hΨ
    obtain ⟨h₁, h₂, rfl⟩ := isFib_hkMap Z χ hx hx' hΨ
    subst h₁ h₂
    obtain ⟨C, hCk, hCc⟩ := exists_carried Z.toKerScheme (spMap χ ≫ h) _ rfl
    obtain ⟨ψp, hψ⟩ := isHkIsog_hkMap Z hA (spMap χ ≫ h) C ((hCc C).2 rfl)
    have hK := GlobalTheory.ThetaTrace.transKer_of_isHkIsog hψ
    have hH := (isog_iff hcop _ _ C _).1 ⟨ψp, hψ⟩
    rw [Equiv.apply_symm_apply] at hK hH
    rw [hK]
    exact ⟨hCk, hH, (hCc C).2 rfl⟩
  refine ⟨hkMap Z hx hx', ⟨GlobalTheory.T.heckeUniversalIsogenyOnFibres_linear_at_ringPoint E H Dw l Xo P p i Z T h x x' hx hx', hkMap_etale Z hx hx',
    hkMap_surjective Z hx hx', ?_, fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ =>
      ⟨(hfib Ω χ x₁ x₁' Ψ₁ hΨ).1, (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.1⟩⟩,
    fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ => (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.2⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_generator_heckeIsogeny_lineBundle_quotient E H Dw l Xo P p i Z T h x x' hx hx'
  exact exists_isRigIso_of_isGen _ _ _ _ _ _ _ _ β ⟨hkMap_fst Z hx hx', GlobalTheory.T.heckeUniversalIsogenyOnFibres_preserves_origin E H Dw l Xo P p i Z T h x x' hx hx'⟩ hβ

end GlobalTheory.HeckeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeIsogenyFamily_pullback_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X), x = h ≫ Z.π₁ → x' = h ≫ Z.π₂ → ∃ Ψ : Gx x ⟶ Gx x', IsHeckeFam P p i Ψ ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
  first | exact @GlobalTheory.HeckeEx.exists_isHeckeFam_carries | exact GlobalTheory.HeckeEx.exists_isHeckeFam_carries | (intros; apply GlobalTheory.HeckeEx.exists_isHeckeFam_carries <;> assumption)
end
