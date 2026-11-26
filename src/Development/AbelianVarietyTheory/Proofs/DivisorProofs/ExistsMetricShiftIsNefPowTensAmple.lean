module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefRationalFibreOfNefFiniteFieldFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbe
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
open GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

theorem ratDeg_pull_eq_interNumRed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∀ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ p) 1 → z ≫ w = redι Z ≫ ratFibre.fst p → IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) → ∀ M : LB X, M.IsLB → ratDeg (w ≫ p) (M.pull w) = interNumRed ℚ Z ![M.pull (ratFibre.fst p)] := by
  intro k _ X p Z hZ W w z hW hzw H M hM
  letI iQ : Algebra ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
    algebraΓOfHom (redι Z ≫ ratFibre.snd p)
  have hi : ∀ r : ℚ, (redι Z).appTop (algebraMap ℚ Γ(ratFibre p, ⊤) r) =
      algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun _ ↦ rfl
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  have hC : VB.IsProjCurve ℚ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have hs : strHom ℚ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = redι Z ≫ strHom ℚ (ratFibre p) := by
      rw [ratFibre.strHom_eq]; exact strHom_eq fun _ ↦ rfl
    have hP : IsProper (strHom ℚ (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [hs]; exact hZ.isProper
    exact VB.IsProperCurve.isProjCurve ℚ _
      ⟨inferInstance, (topologicalKrullDim_red Z).trans hZ.dim_eq, hP⟩
  set R := ratFibre (w ≫ p)
  set e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ R :=
    H.isoIsPullback _ _ (ratFibre.isPullback (w ≫ p)) with he
  have efst : e.hom ≫ ratFibre.fst (w ≫ p) = z :=
    IsPullback.isoIsPullback_hom_fst _ _ H (ratFibre.isPullback _)
  have hf : ∀ r : ℚ, e.hom.appTop (algebraMap ℚ Γ(R, ⊤) r) =
      algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦
    RingHom.congr_fun (RingHom.ext_rat (e.hom.appTop.hom.comp (algebraMap ℚ _)) (algebraMap ℚ _)) r
  set L := (M.pull w).pull (ratFibre.fst (w ≫ p)) with hLdef
  set N := (M.pull (ratFibre.fst p)).pull (redι Z) with hNdef
  have hL : L.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hN : N.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hLe : (L.pull e.hom).IsLB := Semi.LB.isLB_pull hL _
  have hcls : cls (L.pull e.hom) hLe = cls N hN := by
    rw [cls_pull hL, cls_pull (Semi.LB.isLB_pull hM _), cls_pull hM, cls_pull (Semi.LB.isLB_pull hM _),
      cls_pull hM]
    simp only [← pull_comp, ← Category.assoc, efst, hzw]
  have h₁ : chi ℚ (structureModule R) =
      chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    (chi_congr ℚ (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi ℚ (toMod L) =
      chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) := by
    refine (chi_congr ℚ (Twist.unitTwistIso L)).symm.trans ?_
    refine (chi_congr ℚ ((twistFunctor L).mapIso (asIso (unitToPush e.hom)))).trans ?_
    refine (chi_twist_pushforward_of_isClosedImmersion hf _ L).trans ?_
    exact (nonempty_twist_iso_of_cls_eq _ hLe hN hcls).elim (chi_congr ℚ)
  have h₃ : interNumRed ℚ Z ![M.pull (ratFibre.fst p)] =
      chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) -
        chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    have e₁ := interNumOn_eq_interNum_pull (k := ℚ) (L := ![M.pull (ratFibre.fst p)]) hi
      (fun i ↦ by fin_cases i; exact Semi.LB.isLB_pull hM _)
    have e₂ := hC.degLB_eq_interNum hN
    rw [VB.degLB_eq hN, ← chi_congr ℚ (Twist.unitTwistIso N)] at e₂
    rw [interNumRed_def, interNumSub_def]
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    congr 1
    funext i
    fin_cases i
    rfl
  rw [ratDeg, degOfRank, h₁, h₂, h₃]
  push_cast
  ring

end GlobalTheory.RatFibreClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∀ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ p) 1 → z ≫ w = redι Z ≫ ratFibre.fst p → IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) → ∀ M : LB X, M.IsLB → ratDeg (w ≫ p) (M.pull w) = interNumRed ℚ Z ![M.pull (ratFibre.fst p)] := by
  first | exact @GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | exact GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | (intros; apply GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurface
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurface
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveClosure

theorem exists_closure_arith_surface_rat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  intro k _ X p D hX Z hZ
  have := hX.isIntegral
  have := hX.finite
  let S : Closeds X := ⟨closure (ratFibre.fst p '' (Z : Set (ratFibre p))), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set X) :=
    (hZ.isIrreducible.image _ (ratFibre.fst p).continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  haveI : IsPreimmersion (ratFibre.fst p) :=
    MorphismProperty.of_isPullback (ratFibre.isPullback p).flip inferInstance
  have hpb0 := (IsPullback.of_hasPullback w (ratFibre.fst p)).paste_vert (ratFibre.isPullback p)
  rw [← Category.assoc] at hpb0
  have hpb1 : IsPullback (pullback.fst w (ratFibre.fst p)) (pullback.snd w (ratFibre.fst p) ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := hpb0
  haveI : IsReduced (pullback ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isReduced_pullback_localization ℤ ℚ (nonZeroDivisors ℤ) _ _
  haveI : IsReduced (pullback w (ratFibre.fst p)) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w (ratFibre.fst p)) = (Z : Set (ratFibre p)) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change ratFibre.fst p ⁻¹' closure (ratFibre.fst p '' (Z : Set (ratFibre p))) = _
    rw [← (ratFibre.fst p).isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w (ratFibre.fst p)) Z hrange
  have hzw : (e.hom ≫ pullback.fst w (ratFibre.fst p)) ≫ w = redι Z ≫ ratFibre.fst p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w (ratFibre.fst p)) (redι Z ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : ℚ →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ ratFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w (ratFibre.fst p)).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  haveI : IsProper (w ≫ p) := by
    obtain ⟨N, i, _, hi⟩ := hproj
    have := isProper_str k N
    exact hi ▸ inferInstance
  haveI : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  haveI : Flat ((w ≫ p) ≫ spMap (Int.castRingHom k)) := (flat_int_iff_charZero _).2 hcW
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal S).subscheme = (1 + 1 : ℕ) :=
    IntModel.topologicalKrullDim_eq_succ (O := ℤ) (K := ℚ) Int.not_isField hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w (ratFibre.fst p), inferInstance, hX.of_isClosedImmersion w hcW hdim,
    hzw, hpb⟩

end GlobalTheory.CurveClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurfaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closure_curve_rationalFibre_arithmeticSurface : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  first | exact @GlobalTheory.CurveClosure.exists_closure_arith_surface_rat | exact GlobalTheory.CurveClosure.exists_closure_arith_surface_rat | (intros; apply GlobalTheory.CurveClosure.exists_closure_arith_surface_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefRationalFibreOfNefFiniteFieldFibres
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem GlobalTheory.GenNef.isNef_ratFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  intro k _ X _ p D hX L hL
  haveI := hX.finite
  letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  refine ⟨LB.isLB_pull L.isLB _, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hzw, hpb⟩ := GlobalTheory.T.exists_closure_curve_rationalFibre_arithmeticSurface k X p D hX Z hZ
  have e := GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber k X p Z hZ W w z hW hzw hpb L.B L.isLB
  have h0 := NefGeneric.ratDeg_nonneg k W (w ≫ p) (L.pull w rfl) hW
    (ArInt.nefFib_pull k X W p (w ≫ p) hX.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ p) (L.B.pull w) at h0
  rw [e] at h0
  exact h0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefRationalFibreOfNefFiniteFieldFibresStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_rationalFibre_of_nef_finiteFieldFibres : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  first | exact @GlobalTheory.GenNef.isNef_ratFibre | exact GlobalTheory.GenNef.isNef_ratFibre | (intros; apply GlobalTheory.GenNef.isNef_ratFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtendingRationalGenericFibreMulInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtendingRationalGenericFibreMulInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenSecInt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {X XK : Scheme.{0}} [IsIntegral X] {f : X ⟶ Sp ℤ} {j : XK ⟶ X} {fK : XK ⟶ Sp ℚ}
  (H : IsPullback j fK f (spMap (algebraMap ℤ ℚ)))
include H

theorem app_injective_of_affine (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (j.app U).hom := by
  by_cases hne : Nonempty U
  · letI := (j.app U).hom.toAlgebra
    haveI := isLocalization_app H hU
    haveI : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc
    refine IsLocalization.injective (M := (nonZeroDivisors ℤ).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) ?_
    rintro _ ⟨π, hπ, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have e : AbLaw.cst f U π = (π : Γ(X, U)) := map_intCast _ π
    rw [e, Ne, Int.cast_eq_zero]
    exact nonZeroDivisors.ne_zero hπ
  · haveI : Subsingleton Γ(X, U) := by
      have : U = ⊥ := by
        rw [eq_bot_iff]
        exact fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      subst this
      infer_instance
    exact fun a b _ => Subsingleton.elim a b

theorem app_injective (hc : CharZero Γ(X, ⊤)) (U : X.Opens) : Function.Injective (j.app U).hom := by
  intro a b h
  refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ a b fun V => ?_
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · apply app_injective_of_affine H hc V.1.2
    exact (app_rs j V.2 a).trans ((congrArg _ h).trans (app_rs j V.2 b).symm)

theorem exists_extension (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (t : Γ(XK, j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = rs XK (pre_le j hV) t) :
    ∃ b : Γ(X, U), (j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hcov : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hcov (fun x => b x.1 x.2) (fun x y => by
      apply app_injective H hc
      refine (app_rs j inf_le_left _).trans (Eq.trans ?_ (app_rs j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, XK.sheaf.eq_of_locally_eq' (fun x : U => j ⁻¹ᵁ V x.1 x.2) (j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j y, hy⟩, hx _ hy⟩
  · exact (app_rs j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

theorem exists_sec [CompactSpace X] (hc0 : CharZero Γ(X, ⊤)) (B : LB X) (hB : B.IsLB)
    (t : (B.pull j).Sec) : ∃ s : B.Sec, ∀ y : XK,
      j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  have hx : ∀ x : X, ∃ (i : B.ι) (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator H (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : ℤ := ∏ x ∈ S, π x
  have hc : algebraMap ℤ ℚ c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(X, Wx x), (j.app (Wx x)).hom b' =
      AbLaw.cst fK (j ⁻¹ᵁ Wx x) (algebraMap ℤ ℚ c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨AbLaw.cst f (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst H.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(X, B.U i), (j.app (B.U i)).hom s =
      AbLaw.cst fK (j ⁻¹ᵁ B.U i) (algebraMap ℤ ℚ c) * loc t i le_rfl := by
    intro i
    refine exists_extension H hc0 _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs X (le_inf hV hk) (B.g i (ci z)).val * rs X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst,
      rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : XK.Opens, IsUnit (AbLaw.cst fK W (algebraMap ℤ ℚ c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective H hc0
    change (j.app _).hom (rs X inf_le_left (s i)) = (j.app _).hom (_ * rs X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ j ⁻¹ᵁ B.U i →
        (j y ∈ X.basicOpen (s i) ↔ y ∈ XK.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ j ⁻¹ᵁ X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ XK.basicOpen ((j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U i := X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (XK.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩

end GlobalTheory.GenSecInt

theorem GlobalTheory.GenSecInt.main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro k _ X _ p D h B hB t
  haveI := h.isNoetherian
  have H : IsPullback (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) := IsPullback.of_hasPullback _ _
  exact GlobalTheory.GenSecInt.exists_sec H h.charZero B hB t
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionExtendingRationalGenericFibreMulIntStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_rationalGenericFibre_mul_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  first | exact @GlobalTheory.GenSecInt.main | exact GlobalTheory.GenSecInt.main | (intros; apply GlobalTheory.GenSecInt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.GenFibreGen

theorem nefFib_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), NefFib L → NefFib (L.pow n) := by
  intro k _ X _ p D hX L n hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have htriv : NefFib (HermLB.triv p) := by
      intro Z i _ _ κ _ _ _ _
      exact (interNum_eq_zero_of_cls_eq_zero κ _
        (fun _ => LB.isLB_pull (LB.isLB_triv X) i) 0
        (by rw [CechPic.cls_pull (LB.isLB_triv X)]; exact map_zero _)).ge
    refine AmpleTwistNef.nefFib_of_cls_eq ?_ htriv
    erw [CechPic.cls_lbPow L.isLB 0, zero_smul]
    rfl
  · have := hX.finite
    exact (nefFib_pow_iff k X p hX.isProjOver L n hn).2 hL

theorem exists_fst_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → ∃ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) y = x :=
  fun k _ X p x hx => RatDegZeros.mem_range_fst k X p x hx

theorem isProjOver_snd {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsProjOver (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) := by
  have := h.finite
  have := h.isIntegral
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  exact ProjSpace.isProjOver_pullback_snd (Int.castRingHom ℚ) hP

theorem exists_secs_generic : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  intro hNN k _ X _ p D hX L A n hL hA
  have hN := GlobalTheory.T.isNef_rationalFibre_of_nef_finiteFieldFibres k X p D hX (L.pow n) (nefFib_pow k X p D hX L n hL)
  have : IsAffineHom (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hA' : IsAmpleLB (A.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))) :=
    hA.pull_of_isAffineHom _
  have hK := IsAmpleLB.tens_of_isNef hNN ℚ _ _ (isProjOver_snd hX) _ _ hA' hN
  obtain ⟨m, hm, N, t, ht⟩ := hK.exists_isGenerated_pow
  have hM := pull_isLB (((L.pow n).tens A).pow m).isLB (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq _ _ _ (isLB_lbPow hK.isLB m) hM (by
      rw [CechPic.cls_lbPow hK.isLB m, CechPic.cls_pull (((L.pow n).tens A).pow m).isLB _ hM]
      erw [CechPic.cls_lbPow ((L.pow n).tens A).isLB m]
      rw [map_nsmul]
      congr 1
      erw [CechPic.cls_tens (pull_isLB A.isLB _) (pull_isLB (L.pow n).isLB _), CechPic.cls_tens (L.pow n).isLB A.isLB]
      rw [map_add (f := _), CechPic.cls_pull A.isLB, CechPic.cls_pull (L.pow n).isLB, add_comm]) (Fin N) t ht
  choose s hs using fun i => GlobalTheory.T.exists_section_extending_rationalGenericFibre_mul_int k X p D hX _ (((L.pow n).tens A).pow m).isLB (v i)
  refine ⟨m, N, s, hm, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := exists_fst_eq k X p x hx
  have hy : y ∈ ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (v i) := hv ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨i, (hs i y).2 hi⟩

end GlobalTheory.GenFibreGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  first | exact @GlobalTheory.GenFibreGen.exists_secs_generic | exact GlobalTheory.GenFibreGen.exists_secs_generic | (intros; apply GlobalTheory.GenFibreGen.exists_secs_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmple
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_isNef_shift_pow_tens : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hC hN k _ X _ p D hX L A n hL hLf hA hAn
  obtain ⟨m, N, s, hm, hs⟩ := GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre hN k X p D hX L A n hLf hA
  obtain ⟨t, -, ht⟩ := GlobalTheory.NefOfGen.nef_of_gen hC k X p D hX ((L.pow n).tens A) m N s hm hs
    ((hL.pow n).tens hAn.semiPos) (GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens k X p D hX L A n hLf (nefFib_of_isNef hAn))
  exact ⟨t, ht⟩

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.VolBr.exists_isNef_shift_pow_tens | exact GlobalTheory.VolBr.exists_isNef_shift_pow_tens | (intros; apply GlobalTheory.VolBr.exists_isNef_shift_pow_tens <;> assumption)
end
