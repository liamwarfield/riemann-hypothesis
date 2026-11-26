module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTransferIsPullDegId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedUniformisationBundleEvenClosedFibreTor
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionEvenTranslateSamePolarisedD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionTranslateRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorusLift

open GlobalTheory.UU GlobalTheory.FormalPoint

section Lift

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

theorem exists_coords (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (e : ℕ) :
    ∃ y : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
      RedOnto.Coords U e g (thick R I e) y :=
  RedOnto.exists_coords U e g (thick R I e) (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)

variable [IsLocalRing R]


variable {U} in
theorem red_unique [IsHausdorff I R] {g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  choose y hy using exists_coords U g
  refine Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => ?_)
  exact (RedOnto.comp_fstG_eq h (hy e)).symm.trans (RedOnto.comp_fstG_eq h' (hy e))

theorem exists_red [IsAdicComplete I R] (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G, U.Red x g := by
  choose y hy using exists_coords U g
  have hf : IsAdicFamily I fun e => y e ≫ (fstG I e G).left := fun e => by
    have h₁ := (hy (e + 1)).comp (adicLevelMap I (Nat.le_succ (e + 1)))
    have h₂ : adicLevelMap I (Nat.le_succ (e + 1)) ≫ thick R I (e + 1) = thick R I e := adicLevelMap_ι _ _
    have h₃ : RedOnto.Coords U (e + 1) g (thick R I e) (adicLevelMap I (Nat.le_succ (e + 1)) ≫ y (e + 1)) :=
      h₂ ▸ h₁
    have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) G).left)
      (h₃.unique (hy e).succ)).trans ((Category.assoc _ _ _).trans (congrArg _ h₄)))
  obtain ⟨x, ⟨hx₁, hx₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) G.hom hf fun e => by
    have h₁ : (fstG I e G).left ≫ G.hom = (U.gt e).pG.left ≫ D.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.P.A.hom) (hy e).1).trans ((Category.assoc _ _ _).trans (congrArg _ (Over.w g.b))))))
  refine ⟨Over.homMk x hx₁, fun e Z r xe hxe => ?_⟩
  have hr : r = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    have := congrArg (· ≫ G.hom) hxe
    simp only [Category.assoc, Over.homMk_left, hx₁] at this
    rw [← Category.comp_id r]
    refine this.symm.trans ?_
    rw [Over.w (fstG I e G)]
    rfl
  have hxe' : xe = (xe ≫ (thickObj R I e G).hom) ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, ← hx₂ e, hxe]
    simp only [Over.homMk_left]
    rw [hr, Category.assoc]
  have := (hy e).comp (xe ≫ (thickObj R I e G).hom)
  rw [← hr, ← hxe'] at this
  exact this

end Lift

theorem exists_sec_sq_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  intro R _ _ _ hR D A G _ _ hS U g hg
  obtain ⟨z, hz, hgz⟩ := hg
  have : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre GlobalTheory.globalFns_holds hS w hw
  obtain ⟨a, ha⟩ := exists_red U' g
  refine ⟨a, ?_, fun e ae _ hae => ?_⟩
  · rw [pow_two]
    exact red_unique (RedAdd.red_mul GlobalTheory.globalFns_holds ha ha hgz) (RedAdd.red_one U' hz)
  · obtain ⟨h₁, h₂⟩ := ha e _ (thick R (maximalIdeal R) e) ae hae
    refine ⟨h₁, fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
    rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
    exact h₂ χ y J hJ

end GlobalTheory.TorusLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionSectionLiftTorusExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twoTorsion_section_lift_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  first | exact @GlobalTheory.TorusLift.exists_sec_sq_eq_one | exact GlobalTheory.TorusLift.exists_sec_sq_eq_one | (intros; apply GlobalTheory.TorusLift.exists_sec_sq_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionTranslateRefinement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwistSec

theorem exists_sec_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨g, h2, hc⟩ := GlobalTheory.T.exists_orderTwo_point_refinements_compare_unif R hR D₀ D A G hG U hS
  obtain ⟨a, ha, hl⟩ := GlobalTheory.T.exists_twoTorsion_section_lift_torusExtension R hR D A G hG U g h2
  refine ⟨a, ha, fun A₂ D₂ U₂ hL => ?_⟩
  obtain ⟨R', i1, i2, i3, ρ, D₁, D₂', hf, hloc, h0, h2', hid⟩ := hc a ha hl A₂ D₂ U₂ hL
  refine ⟨R', i1, i2, i3, ρ, D₁, hf, hloc, h0, fun D' hD' => ?_⟩
  have h3 := isPullDeg_unique_any R R' ρ D₂.toPre D₂'.toPre D'.toPre h2' hD'
  have h4 := nonempty_isPullDeg_comp_of_injective R' R' R' (RingHom.id R') (RingHom.id R') D₁.toPre D₂'.toPre
    D'.toPre Function.injective_id hid h3
  simpa using h4

end GlobalTheory.TwistSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionTranslateRefinementStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderTwo_section_translate_refinement : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  first | exact @GlobalTheory.TwistSec.exists_sec_compare | exact GlobalTheory.TwistSec.exists_sec_compare | (intros; apply GlobalTheory.TwistSec.exists_sec_compare <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalSymmetricBundleTranslateOrderTw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.LocalPullGen

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (L : LB X), L.IsLB →
    ∀ p : (𝟙_ (Over (Sp R))).left ⟶ X, ∃ ρ : LB.Gen (L.pull p), ρ.IsGen := by
  intro R _ _ X L hL p
  exact ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := R) L hL (K := PUnit) (fun _ => p) (fun _ => 1)

end GlobalTheory.LocalPullGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLineBundlePullbackSpecLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_lineBundle_pullback_spec_localRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (L : LB X), L.IsLB →
    ∀ p : (𝟙_ (Over (Sp R))).left ⟶ X, ∃ ρ : LB.Gen (L.pull p), ρ.IsGen := by
  first | exact @GlobalTheory.LocalPullGen.main | exact GlobalTheory.LocalPullGen.main | (intros; apply GlobalTheory.LocalPullGen.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslCP

open GlobalTheory.CubTransport GlobalTheory.UU

section Gen
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_transl_gen (hL : L.IsLB) (τ : X ⟶ X) {K : Type} [Fintype K] {φ' φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (hc : ∀ k, φ' k ≫ τ = φ k) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb (L.pull τ) φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good L z J → Good (L.pull τ) z J' →
        val t r z J = (∏ k, gw (pullIso L τ) (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ τ)) (J' (r ≫ φ' k)) ^ ε k) *
          val t' r z J' := by
  have hc' : ∀ k, φ' k ≫ τ = 𝟙 Y ≫ φ k := fun k => (hc k).trans (Category.id_comp _).symm
  obtain ⟨a, ha, H⟩ := exists_pmaps ((isGen_iff _).1 (pullIso_isGen hL τ)) hL (pull_isLB hL τ) (𝟙 Y) hc' t ht
  refine ⟨a, ha, fun Z r z J J' hJ hJ' => ?_⟩
  have e := val_pmaps hc' H r hJ hJ'
  rwa [Category.comp_id] at e

theorem gw_pullIso_self (hL : L.IsLB) (τ : X ⟶ X) (f : Y ⟶ X) (y : Y) {j : L.ι} (hj : τ (f y) ∈ L.U j) :
    gw (pullIso L τ) f y j (fun _ => j) = 1 :=
  gm_self (pull_isLB hL τ) f y (mem_pull.2 hj)

theorem gw_pullIso_good (hL : L.IsLB) (τ : X ⟶ X) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (f : Z ⟶ X) : gw (pullIso L τ) f z (J (f ≫ τ)) (fun _ => J (f ≫ τ)) = 1 :=
  gw_pullIso_self hL τ f z (hJ (f ≫ τ))

theorem good_pull {Z : Scheme.{0}} (τ : X ⟶ X) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (L.pull τ) z (fun r _ => J (r ≫ τ)) := fun r => mem_pull.2 (hJ (r ≫ τ))

end Gen

section Grp
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem comp_transl (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (x : T ⟶ G) :
    x.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (toUnit T), Category.comp_id]

theorem toUnit_comp_inv (a : 𝟙_ (Over S) ⟶ G) (ha : a ^ 2 = 1) (T : Over S) : (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := by
  have : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ha])
  rw [← GrpObj.comp_inv, this]

theorem eSec_eq_one_left : eSec G = (1 : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]; rfl

theorem toUnit_left' (T : Over S) (a : 𝟙_ (Over S) ⟶ G) : (toUnit T ≫ a).left = T.hom ≫ a.left := by
  rw [Over.comp_left, Rosenlicht.toUnit_left]

end Grp

section Main
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem transl_comp_inv (a : 𝟙_ (Over S) ⟶ G) (ha : a ^ 2 = 1) :
    ((toUnit G ≫ a) * 𝟙 G).left ≫ (ι[G]).left = (ι[G]).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have i1 : ι[G] = (𝟙 G)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have e : ((toUnit G ≫ a) * 𝟙 G) ≫ ι[G] = ι[G] ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, toUnit_unique (ι[G] ≫ toUnit G) (toUnit G),
      Category.comp_id, mul_inv, toUnit_comp_inv a ha, i1]
  rw [← Over.comp_left, ← Over.comp_left, e]

theorem exists_symL (P : CP G) (a : 𝟙_ (Over S) ⟶ G) (ha : a ^ 2 = 1) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) (fun k => ![(ι[G]).left, 𝟙 G.left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left) ![1, -1]),
      t.IsGen ∧ ∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
        val t x.left z J = val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹ := by
  have hm := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen ((toUnit G ≫ a) * 𝟙 G).left)
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ P.sym_gen (G.hom ≫ a.left)))
  have hi : (G.hom ≫ a.left) ≫ (ι[G]).left = G.hom ≫ a.left := by
    have : a ≫ ι[G] = a := by rw [← Hom.inv_def]; exact inv_eq_of_mul_eq_one_left (by rw [← pow_two, ha])
    rw [Category.assoc, ← Over.comp_left, this]
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := fun k => ![(ι[G]).left, 𝟙 G.left] k ≫ ((toUnit G ≫ a) * 𝟙 G).left)
    (ε' := ![1, -1]) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hi, Category.comp_id, Category.id_comp, transl_comp_inv a ha]
      simp only [zpow_one, zpow_neg, inv_inv, mul_inv_cancel, inv_mul_cancel, _root_.mul_one]) _ hm
  refine ⟨t, ht, fun T x z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, comp_transl, ← Category.assoc, Over.w x,
    toUnit_left']
end Main

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem lift_tripleCoordinates_eq_id : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
  ext <;> simp [x3]

theorem exists_cubL (P : CP G) (a : 𝟙_ (Over S) ⟶ G) :
    ∃ t : LB.Gen (LB.LinComb P.L.L (fun I => thφ G (x3 G) I ≫ ((toUnit G ≫ a) * 𝟙 G).left) thε), t.IsGen ∧
      ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
        val t (lift x (lift y u)).left z J =
          cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹ := by
  have hm := DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.pullGen_isGen P.L.L (thφ G (x3 G)) thε P.c.t P.c.isGen
      (lift (x3 G 0) (lift (x3 G 1) ((toUnit (G3 G) ≫ a) * x3 G 2))).left)
    (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen P.L.L (thφ G (x3 G)) thε P.c.t P.c.isGen (lift (x3 G 0) (lift (x3 G 1) (toUnit (G3 G) ≫ a))).left))
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ' := fun I => thφ G (x3 G) I ≫ ((toUnit G ≫ a) * 𝟙 G).left) (ε' := thε) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      refine (congrArg₂ (· * ·) (prod_cub _ _ _ h) (congrArg (·⁻¹) (prod_cub _ _ _ h))).trans ?_
      have e := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) (fun q => h (q ≫ ((toUnit G ≫ a) * 𝟙 G).left))
      simp only [lift_tripleCoordinates_eq_id, Over.id_left, Category.id_comp, comp_transl] at e
      refine Eq.trans ?_ e.symm
      have c₁ : x3 G 0 * x3 G 1 * ((toUnit (G3 G) ≫ a) * x3 G 2) =
          (toUnit (G3 G) ≫ a) * (x3 G 0 * x3 G 1 * x3 G 2) := by ac_rfl
      have c₂ : x3 G 0 * ((toUnit (G3 G) ≫ a) * x3 G 2) = (toUnit (G3 G) ≫ a) * (x3 G 0 * x3 G 2) := by ac_rfl
      have c₃ : x3 G 1 * ((toUnit (G3 G) ≫ a) * x3 G 2) = (toUnit (G3 G) ≫ a) * (x3 G 1 * x3 G 2) := by ac_rfl
      have c₄ : x3 G 0 * x3 G 1 * (toUnit (G3 G) ≫ a) = (toUnit (G3 G) ≫ a) * (x3 G 0 * x3 G 1) := by ac_rfl
      have c₅ : x3 G 0 * (toUnit (G3 G) ≫ a) = (toUnit (G3 G) ≫ a) * x3 G 0 := mul_comm _ _
      have c₆ : x3 G 1 * (toUnit (G3 G) ≫ a) = (toUnit (G3 G) ≫ a) * x3 G 1 := mul_comm _ _
      rw [c₁, c₂, c₃, c₄, c₅, c₆, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) _ hm
  refine ⟨t, ht, fun T x y u z J hJ => ?_⟩
  have r₀ : lift x (lift y u) ≫ x3 G 0 = x := by simp [x3]
  have r₁ : lift x (lift y u) ≫ x3 G 1 = y := by simp [x3]
  have r₂ : lift x (lift y u) ≫ x3 G 2 = u := by simp [x3]
  have r₃ : lift x (lift y u) ≫ (toUnit (G3 G) ≫ a) = toUnit T ≫ a := by
    rw [← Category.assoc, toUnit_unique (lift x (lift y u) ≫ toUnit (G3 G)) (toUnit T)]
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)
  refine (congrArg₂ (· * ·) (val_cub P.c _ hJ _ _ _) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub P.c _ hJ _ _ _)))).trans ?_
  rw [r₀, r₁, MonObj.comp_mul, r₂, r₃]
end Cube

section Alg
variable {A U : Type} [CommGroup A] [CommGroup U]

theorem isCub_transl {C : A → A → A → U} (hC : IsCub C) (α : A) :
    IsCub (fun x y u => C x y (α * u) * (C x y α)⁻¹) := by
  constructor
  case face =>
    intro x y
    simp only [hC.face, mul_inv_cancel]
  case s01 =>
    intro x y u
    rw [hC.s01 x y, hC.s01 x y]
  case s12 =>
    intro x y u
    have t : ∀ p q, C x p q = C p q x := fun p q => (hC.s01 x p q).trans (hC.s12 p x q)
    have e := hC.coc u α y x
    rw [← t, ← t, ← t, ← t, hC.s12 x (u * α) y, mul_comm u α, hC.s12 x α y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  case coc =>
    intro x x' x'' y
    have e₁ := hC.coc x x' x'' (α * y)
    have e₂ := hC.coc x x' x'' α
    apply Additive.ofMul.injective
    have e₁' := congrArg Additive.ofMul e₁
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at e₁' e₂' ⊢
    linear_combination (norm := abel) e₁' - e₂'

theorem sym_cub_transl (C : A → A → A → U) (σ : A → U) (α : A) (hα : α⁻¹ = α)
    (h : ∀ x y u, C x⁻¹ y⁻¹ u⁻¹ * σ (x * y) * σ (x * u) * σ (y * u) =
      C x y u * σ (x * y * u) * σ x * σ y * σ u) (x y u : A) :
    C x⁻¹ y⁻¹ (α * u⁻¹) * (C x⁻¹ y⁻¹ α)⁻¹ * (σ (α * (x * y)) * (σ α)⁻¹) * (σ (α * (x * u)) * (σ α)⁻¹) *
        (σ (α * (y * u)) * (σ α)⁻¹) =
      C x y (α * u) * (C x y α)⁻¹ * (σ (α * (x * y * u)) * (σ α)⁻¹) * (σ (α * x) * (σ α)⁻¹) *
        (σ (α * y) * (σ α)⁻¹) * (σ (α * u) * (σ α)⁻¹) := by
  have e₁ := h x y (α * u)
  have e₂ := h x y α
  have c₁ : x * (α * u) = α * (x * u) := by ac_rfl
  have c₂ : y * (α * u) = α * (y * u) := by ac_rfl
  have c₃ : x * y * (α * u) = α * (x * y * u) := by ac_rfl
  have c₄ : x * y * α = α * (x * y) := mul_comm _ _
  have c₅ : x * α = α * x := mul_comm _ _
  have c₆ : y * α = α * y := mul_comm _ _
  rw [mul_inv, hα, c₁, c₂, c₃] at e₁
  rw [hα, c₄, c₅, c₆] at e₂
  apply Additive.ofMul.injective
  have e₁' := congrArg Additive.ofMul e₁
  have e₂' := congrArg Additive.ofMul e₂
  simp only [ofMul_mul, ofMul_inv] at e₁' e₂' ⊢
  linear_combination (norm := abel) e₁' - e₂'

end Alg

theorem exists_transl : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (a : 𝟙_ (Over S) ⟶ G),
    a ^ 2 = 1 → ∀ ρ : LB.Gen (P.L.L.pull a.left), ρ.IsGen →
    ∃ P' : GlobalTheory.UU.CP G, P'.L.L = P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left ∧
      (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P'.sym x.left z J' =
          val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹) ∧
      (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P'.c z J' x y u = cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹) := by
  intro S G _ _ P a ha ρ hρ
  have hL := P.L.isLB
  have hL' := pull_isLB hL ((toUnit G ≫ a) * 𝟙 G).left
  have hα : ∀ T : Over S, (toUnit T ≫ a)⁻¹ = toUnit T ≫ a := toUnit_comp_inv a ha

  have hc : ∀ _ : PUnit, eSec G ≫ ((toUnit G ≫ a) * 𝟙 G).left = a.left := fun _ => by
    rw [eSec_eq_one_left, comp_transl, _root_.mul_one, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨rig, hrig, -⟩ := exists_transl_gen hL ((toUnit G ≫ a) * 𝟙 G).left (φ' := fun _ : PUnit => eSec G) (φ := fun _ => a.left)
    (ε := fun _ => 1) hc ρ hρ
  let L' : RigLB G := ⟨P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left, rig, hL', hrig⟩

  obtain ⟨s, hs, vs⟩ := exists_symL P a ha
  obtain ⟨s', hs', Vs⟩ := exists_transl_gen hL ((toUnit G ≫ a) * 𝟙 G).left (φ' := ![(ι[G]).left, 𝟙 G.left]) (fun _ => rfl) s hs
  obtain ⟨k, hk, vk⟩ := exists_cubL P a
  obtain ⟨k', hk', Vk⟩ := exists_transl_gen hL ((toUnit G ≫ a) * 𝟙 G).left (φ' := thφ G (x3 G)) (fun _ => rfl) k hk
  have cubRel : ∀ (T : Over S) (z : T.left) (J) (J'), Good P.L.L z J → Good L'.L z J' → ∀ x y u : T ⟶ G,
      cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹ =
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (x * y * u) *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (x * y))⁻¹ *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (x * u))⁻¹ *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) (y * u))⁻¹ *
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) x *
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) y *
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) u *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) 1)⁻¹ *
        CubTransport.thV (L := L') k' z J' x y u := fun T z J J' hJ hJ' x y u =>
    (vk T x y u z J hJ).symm.trans ((Vk _ _ z J J' hJ hJ').trans
      (congrArg₂ (· * ·) (prod_cub x y u (fun q => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) q z (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' q))) rfl))
  have symRel : ∀ (T : Over S) (z : T.left) (J) (J'), Good P.L.L z J → Good L'.L z J' → ∀ x : T ⟶ G,
      val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹ =
        (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) x⁻¹ *
        ((fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left)) x)⁻¹ *
        val s' x.left z J' := fun T z J J' hJ hJ' x =>
    (vs T x z J hJ).symm.trans ((Vs _ _ z J J' hJ hJ').trans
      (congrArg₂ (· * ·) (prod_sym x (fun q => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) q z (J (q ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' q))) rfl))
  let c' : CubicalStr G L' := cubicalOfVal k' hk' fun T z J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    exact isCub_of_twist (isCub_transl (isCub_cubV P.c hJ) (toUnit T ≫ a)) (MonoidHom.id (T ⟶ G))
      (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left))
      (θ' := CubTransport.thV (L := L') k' z J') (cubRel T z J J' hJ hJ')
  refine ⟨⟨L', c', s', hs', corr_of_val hL' fun y J' hJ' => ?_, fun T x y u z J' hJ' => ?_⟩, rfl,
    fun T x z J J' hJ hJ' => ?_, fun T x y u z J J' hJ hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good_pt hL y
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    have e := symRel (𝟙_ (Over S)) y J J' hJ hJ' 1
    simp only [_root_.mul_one, mul_inv_cancel, inv_one, _root_.one_mul] at e
    rw [Category.id_comp, eSec_eq_one_left]
    exact e.symm
  · obtain ⟨J, hJ⟩ := exists_good_pt hL z
    exact sym_cub_alg (MonoidHom.id (T ⟶ G))
      (fun p : T ⟶ G => gw (pullIso P.L.L ((toUnit G ≫ a) * 𝟙 G).left) p.left z (J (p.left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (J' p.left))
      (θ := fun x y u => cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹)
      (θ' := cubV c' z J') (σ := fun p => val P.sym ((toUnit T ≫ a) * p).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹)
      (σ' := fun p => val s' p.left z J') (cubRel T z J J' hJ hJ') (symRel T z J J' hJ hJ')
      (sym_cub_transl (cubV P.c z J) (fun p => val P.sym p.left z J) _ (hα T) (fun x y u => P.sym_cub T x y u z J hJ) x y u)
  · have eJ : J' = fun r _ => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) := funext fun r => eq_of_heq (hJ' r)
    subst eJ
    have e := symRel T z J _ hJ (good_pull ((toUnit G ≫ a) * 𝟙 G).left hJ) x
    simp only [gw_pullIso_good hL _ hJ, inv_one, _root_.one_mul] at e
    exact e.symm
  · have eJ : J' = fun r _ => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) := funext fun r => eq_of_heq (hJ' r)
    subst eJ
    have e := cubRel T z J _ hJ (good_pull ((toUnit G ≫ a) * 𝟙 G).left hJ) x y u
    simp only [gw_pullIso_good hL _ hJ, inv_one, _root_.one_mul, _root_.mul_one] at e
    exact e.symm

end GlobalTheory.TranslCP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalSymmetricLineBundleTwoTorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_cubicalSymmetricLineBundle_twoTorsion : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G) (a : 𝟙_ (Over S) ⟶ G),
    a ^ 2 = 1 → ∀ ρ : LB.Gen (P.L.L.pull a.left), ρ.IsGen →
    ∃ P' : GlobalTheory.UU.CP G, P'.L.L = P.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left ∧
      (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P'.sym x.left z J' =
          val P.sym ((toUnit T ≫ a) * x).left z J * (val P.sym (toUnit T ≫ a).left z J)⁻¹) ∧
      (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P.L.L.ι)
        (J' : (T.left ⟶ G.left) → P'.L.L.ι), Good P.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P'.c z J' x y u = cubV P.c z J x y ((toUnit T ≫ a) * u) * (cubV P.c z J x y (toUnit T ≫ a))⁻¹) := by
  first | exact @GlobalTheory.TranslCP.exists_transl | exact GlobalTheory.TranslCP.exists_transl | (intros; apply GlobalTheory.TranslCP.exists_transl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalSymmetricBundleTranslateOrderTw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwistCP

theorem exists_cp_transl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  intro R _ _ _ hR D A G _ _ hG U a ha
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_generator_lineBundle_pullback_spec_localRing R G.left M.L.L M.L.isLB a.left
  obtain ⟨P, hPL, h2, h3⟩ := GlobalTheory.T.exists_translate_cubicalSymmetricLineBundle_twoTorsion (Sp R) G M a ha ρ hρ
  refine ⟨P, ?_, GlobalTheory.T.translatedUniformisationBundle_even_closedFibreTorus R hR D A G hG U a ha P hPL h2 h3⟩
  rw [hPL]
  exact GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U.LG.isLB _)

end GlobalTheory.MumTwistCP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalSymmetricBundleTranslateOrderTwStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∃ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P := by
  first | exact @GlobalTheory.MumTwistCP.exists_cp_transl | exact GlobalTheory.MumTwistCP.exists_cp_transl | (intros; apply GlobalTheory.MumTwistCP.exists_cp_transl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwistAV

open GlobalTheory.CechPic (cls pull)

section

variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G]

def genSec (a : 𝟙_ (Over (Sp R)) ⟶ G) : 𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by
    rw [Category.assoc, Over.w a]; simp)) (pullback.lift_snd _ _ _)

theorem genSec_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (genSec a).left ≫ pullback.fst G.hom (jK R) = jK R ≫ a.left :=
  pullback.lift_fst _ _ _

theorem const_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (toUnit ((Over.pullback (jK R)).obj G) ≫ genSec a).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ G.hom ≫ a.left := by
  rw [Over.comp_left, Category.assoc, genSec_fst, ← Category.assoc (pullback.fst G.hom (jK R)), pullback.condition]
  rfl

theorem hom_ext_gen {T : Over (Sp (FractionRing R))} {x y : T ⟶ (Over.pullback (jK R)).obj G}
    (h : x.left ≫ pullback.fst G.hom (jK R) = y.left ≫ pullback.fst G.hom (jK R)) : x = y :=
  Over.OverMorphism.ext ((isGrpPullback_pullback G (jK R)).1.hom_ext h (by
    show x.left ≫ ((Over.pullback (jK R)).obj G).hom = y.left ≫ ((Over.pullback (jK R)).obj G).hom
    rw [Over.w, Over.w]))

set_option synthInstance.maxHeartbeats 200000 in
theorem genSec_sq (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) : genSec a * genSec a = 1 := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let T : Over (Sp (FractionRing R)) := 𝟙_ _
  let x₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ a
  have hx : x₀.left = (genSec a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genSec_fst]; rfl
  have e := hp T (genSec a) (genSec a) x₀ x₀ hx hx
  have haa : x₀ * x₀ = toUnit _ ≫ η[G] := by
    rw [← MonObj.comp_mul, ← sq, ha, Hom.one_def, ← Category.assoc, comp_toUnit]
  set c := genSec a * genSec a with hc
  let y₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ η[G]
  have hy : y₀.left = c.left ≫ pullback.fst G.hom (jK R) := by rw [show y₀ = x₀ * x₀ from haa.symm, e]
  have e₂ := hp T c c y₀ y₀ hy hy
  have hyy : y₀ * y₀ = y₀ := by
    rw [show y₀ = 1 from Hom.one_def.symm, _root_.one_mul]
  have hcc : c * c = c := hom_ext_gen (by rw [← e₂, hyy, hy])
  exact mul_eq_left.1 hcc

theorem transl_fst [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (GlobalTheory.PolTranslate.transl (genSec a)).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let GK := (Over.pullback (jK R)).obj G
  let p : Over.mk (GK.hom ≫ jK R) ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
  have e := hp GK (𝟙 GK) (toUnit GK ≫ genSec a) p (p ≫ toUnit G ≫ a) (by simp [p])
    (by rw [const_fst]; rfl)
  have e' : p * (p ≫ toUnit G ≫ a) = p ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [MonObj.comp_mul, Category.comp_id, _root_.mul_comm]
  rw [e', Over.comp_left] at e
  exact e.symm

end

theorem exists_translate_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D A G _ _ _ U a ha P hP
  haveI := U.gen_hom
  haveI := A.isAb.comm
  haveI : IsProper A.A.hom := A.isAb.proper
  let b := genSec a
  let a' : 𝟙_ (Over (Sp (FractionRing R))) ⟶ A.A := b ≫ U.gen.hom
  have ha' : a' * a' = 1 := by
    show (b ≫ U.gen.hom) * (b ≫ U.gen.hom) = 1
    rw [← MonObj.mul_comp, genSec_sq a ha, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  let A₂ : PolAV (Sp (FractionRing R)) :=
    { A := A.A
      isAb := A.isAb
      g := A.g
      smoothDim := A.smoothDim
      L := GlobalTheory.RigidTranslate.rigTransl A.L a'
      isLB := LB.isLB_linComb A.isLB _ _
      rigid := GlobalTheory.RigidTranslate.rigidified_rigTransl A.isLB
      sym := GlobalTheory.RigidTranslate.sym_rigTransl ha' A.isLB A.sym
      ample := GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section a' A.isLB A.ample
      ktriv := GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ _ _ A.isLB a' A.ktriv }
  refine ⟨A₂, U.gen, U.gen_hom, ?_⟩
  let f := pullback.fst G.hom (jK R)
  let τ := ((toUnit G ≫ a) * 𝟙 G).left
  have hLG := U.LG.isLB
  have hext : pull U.gen.hom.left (cls A.L A.isLB) = pull f (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hLG _)).2 U.ext
  have hP' : cls P.L.L P.L.isLB = pull τ (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff P.L.isLB (pull_isLB hLG _)).2 hP
  have hrig : pull (eSec G) (cls P.L.L P.L.isLB) = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB P.L.isLB _)).2 ⟨P.L.rig, P.L.rigGen⟩
  have ea : a.left = eSec G ≫ τ := by
    show a.left = (η[G] ≫ ((toUnit G ≫ a) * 𝟙 G)).left
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id,
      h1, _root_.mul_one]
  have hgt : U.gen.hom.left ≫ (GlobalTheory.PolTranslate.transl a').left =
      (GlobalTheory.PolTranslate.transl b).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PolTranslate.comp_transl, GlobalTheory.PolTranslate.transl, MonObj.mul_comp,
      Category.id_comp]
    rfl
  have hgc : U.gen.hom.left ≫ (toUnit A.A ≫ a').left = (toUnit _ ≫ b).left ≫ U.gen.hom.left := by
    rw [GlobalTheory.RigidTranslate.comp_const, ← Over.comp_left]
    rfl
  have h₁ := pull_isLB (LB.isLB_linComb A.isLB (K := Fin 2)
    ![(GlobalTheory.PolTranslate.transl a').left, (toUnit A.A ≫ a').left] ![1, -1]) U.gen.hom.left
  refine (GlobalTheory.CechPic.cls_eq_iff h₁ (pull_isLB P.L.isLB _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull _ _ h₁, GlobalTheory.CechPic.cls_linComb A.isLB, GlobalTheory.CechPic.cls_pull P.L.isLB]
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg, map_sub]
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, hgt, hgc, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp, hext,
      ← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, transl_fst a, const_fst a, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp f, GlobalTheory.CechPic.pull_comp, ea, GlobalTheory.CechPic.pull_comp, ← hP', hrig, map_zero, map_zero, sub_zero]
  · exact LB.isLB_linComb A.isLB _ _

end GlobalTheory.TwistAV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  first | exact @GlobalTheory.TwistAV.exists_translate_pol | exact GlobalTheory.TwistAV.exists_translate_pol | (intros; apply GlobalTheory.TwistAV.exists_translate_pol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionEvenTranslateSamePolarisedD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumTwist

theorem exists_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (a : 𝟙_ (Over (Sp R)) ⟶ G) (P : GlobalTheory.UU.CP G) (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), a ^ 2 = 1 ∧ LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P ∧ IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) ∧ ∀ (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), U₂.LG = P.L → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  obtain ⟨a, ha, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_translate_refinement R hR D₀ D A G hG U hS
  obtain ⟨P, hP, hE⟩ := GlobalTheory.T.exists_evenCubicalSymmetricBundle_translate_orderTwo R hR D A G hG U a ha
  obtain ⟨A₂, gen₂, hm, hl⟩ := GlobalTheory.T.exists_principal_polarisation_genericFibre_twoTorsion_translate R hR D A G hG U a ha P hP
  refine ⟨a, P, A₂, gen₂, ha, hP, hE, hm, hl, fun D₂ U₂ hU => ?_⟩
  exact hcmp A₂ D₂ U₂ (by rw [hU]; exact hP)

end GlobalTheory.MumTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionEvenTranslateSamePolarisedDStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderTwo_section_evenTranslate_samePolarisedData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (a : 𝟙_ (Over (Sp R)) ⟶ G) (P : GlobalTheory.UU.CP G) (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), a ^ 2 = 1 ∧ LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) ∧ EvenOn P ∧ IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) ∧ ∀ (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), U₂.LG = P.L → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D₂.toPre D'.toPre) → Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D'.toPre) := by
  first | exact @GlobalTheory.MumTwist.exists_twist | exact GlobalTheory.MumTwist.exists_twist | (intros; apply GlobalTheory.MumTwist.exists_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.LamTransl
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem foldr_eq {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (l : List (Fin n)) :
    l.foldr (fun k acc => padd G (x k) acc) (pzero G T) = (l.map x).prod := by
  induction l with
  | nil => simp [pzero, Hom.one_def]
  | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, padd, Hom.mul_def]

def split3 (I : Finset (Fin 3)) : Finset (Fin 2) ⊕ Finset (Fin 2) :=
  if (2 : Fin 3) ∈ I then Sum.inl (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)
  else Sum.inr (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)

theorem split3_bij : Function.Bijective split3 := by decide

def splitEquiv : thK ≃ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.ofBijective _ split3_bij).trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

theorem mem8 : ∀ I : Finset (Fin 3),
    I ∈ ({∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))) := by decide

variable (a : 𝟙_ (Over S) ⟶ G)

def tr : G ⟶ G := (toUnit G ≫ a) * 𝟙 G

def pt3 : G2 G ⟶ G3 G := lift (fst G G) (lift (snd G G) (toUnit (G2 G) ≫ a))
def φA : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down ≫ tr G a).left
def φB : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left
def ε2 : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem splitEquiv_apply (I : Finset (Fin 3)) : splitEquiv ⟨I⟩ = Sum.map ULift.up ULift.up (split3 I) := by
  rfl

theorem split_eq (k : thK) : Sum.elim (φA G a) (φB G) (splitEquiv k) = (pt3 G a).left ≫ thφ G (x3 G) k ∧
    Sum.elim ε2 (fun k => -ε2 k) (splitEquiv k) = thε k := by
  rcases k with ⟨I⟩
  rw [splitEquiv_apply]
  have h := mem8 I
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [split3, if_true, if_false, Finset.mem_insert, Finset.mem_singleton,
      Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  all_goals
    refine ⟨?_, trivial⟩
    simp only [φA, φB, thφ]
    rw [← Over.comp_left]
    congr 1
    rw [psum, foldr_eq, psum, foldr_eq]
    simp [List.finRange_succ, x2, x3, pt3, tr, MonObj.comp_mul]
  all_goals ac_rfl

theorem sameSum : LB.SameSum (fun k => (pt3 G a).left ≫ thφ G (x3 G) k) thε (Sum.elim (φA G a) (φB G))
    (Sum.elim ε2 fun k => -ε2 k) := by
  classical
  intro ψ
  rw [← Equiv.sum_comp splitEquiv]
  exact Finset.sum_congr rfl fun k _ => by rw [(split_eq G a k).1, (split_eq G a k).2]

end GlobalTheory.Mum.LamTransl

namespace GlobalTheory.Mum


open LamTransl in
theorem lam_transl_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L →
    ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) →
      LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  intro S G _ _ L c a N hN hNL
  have hT : (L.L.pull (tr G a).left).IsLB := pull_isLB L.isLB _
  have hA : (LB.LinComb L.L (φA G a) ε2).IsLB := DVR.linComb_isLB _ L.isLB _ _
  have hLam := GlobalTheory.SabBaseChange.cube_isLB (x2 G) L.isLB
  have h1 : LBIso (abelian₂ G N) (abelian₂ G (L.L.pull (tr G a).left)) := GlobalTheory.SabBaseChange.lbIso_cube (x2 G) hNL
  have h2 : LBIso (abelian₂ G (L.L.pull (tr G a).left)) (LB.LinComb L.L (φA G a) ε2) :=
    LBIso.chartPull (chartPullLinComb L.L (tr G a).left _ (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (chartPullSame L.L (φA G a) (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (GlobalTheory.PolBaseChange.lbIso_refl hA)
  have h3 : LBIso (abelian₂ G L.L) (LB.LinComb L.L (φA G a) ε2) := by
    refine (GlobalTheory.TripleCompare.lbIso_iff_gen (L := L.L) (φB G) ε2 (φA G a) ε2).2 ?_
    obtain ⟨t', ht', -⟩ := DVR.gen_transport L.isLB (sameSum G a)
      _ (DVR.pullGen_isGen L.L _ _ c.t c.isGen (pt3 G a).left)
    exact ⟨t', ht'⟩
  exact LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hN) (GlobalTheory.SabBaseChange.cube_isLB _ hT) hLam h1
    (LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hT) hA hLam h2 (LBIso.symm h3))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_translate_iso_cubical : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L → ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  first | exact @GlobalTheory.Mum.lam_transl_iso | exact GlobalTheory.Mum.lam_transl_iso | (intros; apply GlobalTheory.Mum.lam_transl_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataUniformiseFiniteExtension
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem samePol_unif_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ : DegData R (maximalIdeal R)), ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G U.LG.L).pull β₂) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  have := hR.2
  obtain ⟨a, P, A₂, gen₂, -, hPa, hEv, hgen, hgenL, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_evenTranslate_samePolarisedData R hR D₀ D A G hG U hS
  obtain ⟨D₂, U₂, hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R hR G P hG hEv A₂ gen₂ hgen hgenL
  obtain ⟨R', _, _, _, ρ, D₁, hfin, hloc, ⟨hD₀⟩, hmove⟩ := hcmp D₂ U₂ hLG
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD', A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hfin.1 ρ hfin.2.1 (map_maximalIdeal_le ρ) hG U₂
  obtain ⟨hiso⟩ := hmove D' ⟨hD'⟩
  have hG₁ : IsSemiAbelian ((Over.pullback (specOf ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨U₁, hU₁, -⟩ := (GlobalTheory.T.uniformisation_transfer_isPullDeg_id R' (maximalIdeal R') hfin.1 D₁ D' ⟨hiso⟩ A' _ hG₁).1 U'
  have hb : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (specOf ρ) := Category.id_comp _
  have hpb : IsGrpPullback ((Over.pullback (specOf ρ)).obj G) G (spMap ρ)
      ((Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    refine (isGrpPullback_pullback G (spMap ρ)).congr ?_ hb.symm
    rfl
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback (Sp R) (Sp R') (spMap ρ) G _ _ hpb
  have hLU : (abelian₂ G U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have h2 : LBIso (abelian₂ G U₂.LG.L) (abelian₂ G U.LG.L) := by
    rw [hLG]
    exact GlobalTheory.T.mumfordBundle_translate_iso_cubical (Sp R) G U.LG U.cubG a P.L.L P.L.isLB hPa
  have h3 : LBIso (abelian₂ G U₂.LG.L) ((abelian₂ G U.LG.L).pull (𝟙 _)) :=
    LBIso.trans (DVR.linComb_isLB _ U₂.LG.isLB _ _) hLU (pull_isLB hLU _) h2
      ⟨GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen hLU⟩
  have h4' := hlam U₂.LG.L U'.LG.L _ (abelian₂ G U.LG.L) (𝟙 _) U₂.LG.isLB U'.LG.isLB hLU
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩ h3
  rw [Category.comp_id] at h4'
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, D₁, _, inferInstance, inferInstance, _, β₂, A', U₁, hfin,
    ⟨hD₀⟩, hpb, hsq, ?_⟩
  rw [hU₁]
  exact h4'

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataUniformiseFiniteExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.samePolarisedData_uniformise_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ : DegData R (maximalIdeal R)), ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G U.LG.L).pull β₂) := by
  first | exact @GlobalTheory.Mum.samePol_unif_finExt | exact GlobalTheory.Mum.samePol_unif_finExt | (intros; apply GlobalTheory.Mum.samePol_unif_finExt <;> assumption)
end
