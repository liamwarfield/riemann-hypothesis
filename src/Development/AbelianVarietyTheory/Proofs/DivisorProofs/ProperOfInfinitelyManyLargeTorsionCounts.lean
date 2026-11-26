module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurve

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPoint
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffineLineExt

open Polynomial

theorem isPrincipalIdealRing_away {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := ⟨fun J => by
  rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J]
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
  rw [ha]
  exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩

theorem extend : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  intro k _ B _ _ P c hP u hu
  have hQ0 : P * (X - C c) ≠ 0 := mul_ne_zero hP (X_sub_C_ne_zero c)
  haveI : IsDomain (Localization.Away P) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  haveI : IsDomain (Localization.Away (P * (X - C c))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)
  haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P
  have hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) =
      algebraMap k[X] (Localization.Away (P * (X - C c))) a :=
    IsLocalization.Away.awayToAwayRight_eq P (X - C c)
  have hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) =
      spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) :=
    IsOpenImmersion.of_isLocalization P
  haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P))) := by
    rw [← hcomp]
    exact IsOpenImmersion.of_isLocalization (P * (X - C c))
  haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)))
    (spMap (algebraMap k[X] (Localization.Away P)))
  haveI : B.left.IsSeparated := ⟨by
    rw [show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]
    infer_instance⟩
  have hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, h1, h2⟩ := TorusConst.exists_extension (Z := Sp (Localization.Away P))
    (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _
    (spMap (algebraMap k (Localization.Away P))) B.hom u hu'
  exact ⟨g, h2, h1⟩

end GlobalTheory.AffineLineExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendAffineLineMorphismToProperAcrossPointStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  first | exact @GlobalTheory.AffineLineExt.extend | exact GlobalTheory.AffineLineExt.extend | (intros; apply GlobalTheory.AffineLineExt.extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversionCoordinateLocalizationPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversionCoordinateLocalizationPolynomial
open Polynomial

namespace GlobalTheory

noncomputable def awayLiftAlgHom {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) : Localization.Away P →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers P) (f := f)
    (by rintro ⟨_, n, rfl⟩; simpa using h.pow n)

theorem awayLiftAlgHom_algebraMap {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) (q : k[X]) :
    awayLiftAlgHom P f h (algebraMap k[X] (Localization.Away P) q) = f q := by
  simp [awayLiftAlgHom, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]

theorem aeval_reverse_mul_pow_of_mul_eq_one {k : Type} [Field k] {B : Type} [CommRing B]
    [Algebra k B] (x y : B) (h : x * y = 1) (P : k[X]) :
    aeval y P.reverse * x ^ P.natDegree = aeval x P := by
  letI : Invertible x := invertibleOfRightInverse x y h
  have hinv : (⅟x : B) = y := invOf_eq_right_inv h
  have := eval₂_reverse_mul_pow (algebraMap k B) x P
  rw [hinv] at this
  simpa [aeval_def] using this

theorem algebraMap_eq_aeval_X {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    [Algebra k[X] B] [IsScalarTower k k[X] B] (p : k[X]) :
    algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by
  have : (IsScalarTower.toAlgHom k k[X] B) = aeval (algebraMap k[X] B X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun this p

theorem localizationAway_inv_coordinate (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    ∃ Q : Polynomial k, Q ≠ 0 ∧
      ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q)
        (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)),
        (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) =
            algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧
          τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) =
            (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
              IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  classical
  have hrev : P.reverse ≠ 0 := fun h => hP (reverse_eq_zero.mp h)
  refine ⟨X * P.reverse, mul_ne_zero X_ne_zero hrev, ?_⟩

  set C := Localization.Away (X * P)
  set u : C := IsLocalization.Away.invSelf (X * P)
  have hu : algebraMap k[X] C (X * P) * u = 1 := IsLocalization.Away.mul_invSelf _
  set xC : C := algebraMap k[X] C X
  set xi : C := algebraMap k[X] C P * u
  have hxC : xC * xi = 1 := by rw [← hu, map_mul]; ring
  have hPC : IsUnit (algebraMap k[X] C P) :=
    isUnit_iff_exists_inv.mpr ⟨xC * u, by rw [← hu, map_mul]; ring⟩
  have hxi : IsUnit xi := isUnit_iff_exists_inv'.mpr ⟨xC, hxC⟩
  have hτ : IsUnit (aeval xi (X * P.reverse)) := by
    rw [map_mul, aeval_X]
    refine hxi.mul ?_
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) xC xi hxC P
    rw [← algebraMap_eq_aeval_X] at key
    exact isUnit_of_mul_isUnit_left (key ▸ hPC)
  let τ := awayLiftAlgHom (X * P.reverse) (aeval xi) hτ

  set B := Localization.Away (X * P.reverse)
  set v : B := IsLocalization.Away.invSelf (X * P.reverse)
  have hv : algebraMap k[X] B (X * P.reverse) * v = 1 := IsLocalization.Away.mul_invSelf _
  set yB : B := algebraMap k[X] B X
  set yi : B := algebraMap k[X] B P.reverse * v
  have hyB : yB * yi = 1 := by rw [← hv, map_mul]; ring
  have hrevB : IsUnit (algebraMap k[X] B P.reverse) :=
    isUnit_iff_exists_inv.mpr ⟨yB * v, by rw [← hv, map_mul]; ring⟩
  have hyi : IsUnit yi := isUnit_iff_exists_inv'.mpr ⟨yB, hyB⟩
  have hσ : IsUnit (aeval yi P) := by
    have key := aeval_reverse_mul_pow_of_mul_eq_one (k := k) yi yB (by rw [mul_comm]; exact hyB) P
    rw [← algebraMap_eq_aeval_X] at key
    rw [← key]
    exact hrevB.mul (hyi.pow _)
  let σ := awayLiftAlgHom P (aeval yi) hσ
  have hτalg : ∀ q : k[X], τ (algebraMap k[X] B q) = aeval xi q :=
    awayLiftAlgHom_algebraMap _ _ _
  have hσalg : ∀ q : k[X], σ (algebraMap k[X] (Localization.Away P) q) = aeval yi q :=
    awayLiftAlgHom_algebraMap _ _ _
  refine ⟨σ, τ, ?_, ?_⟩
  · have hτyi : τ yi = xC := by
      have h1 : τ yB * τ yi = 1 := by rw [← map_mul, hyB, map_one]
      have h2 : τ yB = xi := by rw [hτalg, aeval_X]
      rw [h2] at h1
      calc τ yi = τ yi * (xC * xi) := by rw [hxC, mul_one]
        _ = xC * (xi * τ yi) := by ring
        _ = xC := by rw [h1, mul_one]
    have hext : ((τ.comp σ).comp (IsScalarTower.toAlgHom k k[X] (Localization.Away P))) =
        IsScalarTower.toAlgHom k k[X] C := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
      rw [hσalg, aeval_X, hτyi]
    exact RingHom.ext fun p => DFunLike.congr_fun hext p
  · exact RingHom.ext fun p => hτalg p

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInversionCoordinateLocalizationPolynomialStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inversion_coordinate_localization_polynomial : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∃ Q : Polynomial k, Q ≠ 0 ∧ ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q) (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)), (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) = algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧ τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) = (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P * IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  first | exact @GlobalTheory.localizationAway_inv_coordinate | exact GlobalTheory.localizationAway_inv_coordinate | (intros; apply GlobalTheory.localizationAway_inv_coordinate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConst
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NoRatCurve

section
variable (k : Type) [Field k] (P : Polynomial k)

def rhoMap : Localization.Away (Polynomial.X : Polynomial k) →+* Localization.Away (Polynomial.X * P) :=
  IsLocalization.Away.awayToAwayRight (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) (Polynomial.X : Polynomial k) P

theorem rhoMap_algebraMap (x : Polynomial k) :
    rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) x) =
      algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) x :=
  IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away (Polynomial.X : Polynomial k))
    (P := Localization.Away (Polynomial.X * P)) _ _ x

theorem rhoMap_invSelf : rhoMap k P (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P) := by
  have hu1 : IsUnit (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X) :=
    isUnit_of_mul_isUnit_left (x := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) Polynomial.X)
      (y := algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P)
      (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _)
  apply hu1.mul_left_cancel
  calc _ = rhoMap k P (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) Polynomial.X *
        IsLocalization.Away.invSelf (Polynomial.X : Polynomial k)) := by rw [map_mul, rhoMap_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := by rw [← _root_.mul_assoc, ← map_mul, IsLocalization.Away.mul_invSelf]

theorem rhoMap_comp_algebraMap : (rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) =
    algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) :=
  RingHom.ext (rhoMap_algebraMap k P)

theorem rhoMap_comp_aeval : (rhoMap k P).comp (Polynomial.aeval (R := k) (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
      Localization.Away (Polynomial.X : Polynomial k))).toRingHom =
    (Polynomial.aeval (R := k) (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
      IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    have e2 : (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P *
        IsLocalization.Away.invSelf (Polynomial.X * P))) (Polynomial.C a) =
        algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) (Polynomial.C a) := by
      rw [Polynomial.aeval_C]; rfl
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e1, e2,
      rhoMap_algebraMap]
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_X, Polynomial.aeval_X]
    exact rhoMap_invSelf k P

end

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem awayToAwayRight_injective (k : Type) [Field k] (P : Polynomial k) (hP : P ≠ 0) :
    Function.Injective (rhoMap k P) := by
  have hXP : (Polynomial.X * P : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hP
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P))) :=
    IsLocalization.injective (Localization.Away (Polynomial.X * P)) (powers_le_nonZeroDivisors_of_noZeroDivisors hXP)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (Polynomial.X : Polynomial k)) z
  have e := rhoMap_algebraMap k P a
  have h1 : IsLocalization.mk' (Localization.Away (Polynomial.X : Polynomial k)) a s *
      algebraMap _ _ (s : Polynomial k) = algebraMap _ _ a := IsLocalization.mk'_spec _ _ _
  have h2 := congrArg (rhoMap k P) h1
  rw [map_mul, hz, zero_mul, e] at h2
  have ha : a = 0 := hinj (by rw [← h2, map_zero])
  subst ha
  simp

theorem extend_to_line : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k), P ≠ 0 → ∀ u : Sp (Localization.Away P) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → ∃ v : Sp (Polynomial k) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Polynomial k)) ∧ spMap (algebraMap (Polynomial k) (Localization.Away P)) ≫ v = u := by
  intro k _ _ B _ _ P hP
  induction hn : P.natDegree generalizing P with
  | zero =>
    intro u hu
    obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.1 hn
    have ha : IsUnit (Polynomial.C a) := Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 (by rintro rfl; simp at hP))
    let φ : Localization.Away (Polynomial.C a) →+* Polynomial k := IsLocalization.Away.lift (g := RingHom.id (Polynomial k)) (Polynomial.C a) ha
    have hφ : (algebraMap (Polynomial k) (Localization.Away (Polynomial.C a))).comp φ = RingHom.id _ :=
      IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C a)) (RingHom.ext fun x => by
        simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq])
    refine ⟨spMap φ ≫ u, ?_, ?_⟩
    · rw [Category.assoc, hu, ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.C a))]
      simp [φ, IsLocalization.Away.lift, IsLocalization.lift_eq]
    · rw [← Category.assoc, ← spMap_comp', hφ]
      show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ u = u
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  | succ n ih =>
    intro u hu
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root P (by rw [Polynomial.degree_eq_natDegree hP, hn]; exact_mod_cast Nat.succ_ne_zero n)
    obtain ⟨P', rfl⟩ : ∃ P', P = P' * (Polynomial.X - Polynomial.C c) :=
      ⟨P /ₘ (Polynomial.X - Polynomial.C c), by rw [mul_comm, Polynomial.mul_divByMonic_eq_iff_isRoot.2 hc]⟩
    have hP' : P' ≠ 0 := left_ne_zero_of_mul hP
    have hn' : P'.natDegree = n := by
      rw [Polynomial.natDegree_mul hP' (Polynomial.X_sub_C_ne_zero c), Polynomial.natDegree_X_sub_C] at hn
      omega
    obtain ⟨v', hv', ev'⟩ := GlobalTheory.T.extend_affineLine_morphism_to_proper_across_point k B P' c hP' u hu
    obtain ⟨v, hv, ev⟩ := ih P' hP' hn' v' hv'
    refine ⟨v, hv, ?_⟩
    rw [← ev', ← ev, ← Category.assoc, ← spMap_comp']
    congr 2
    exact RingHom.ext fun x => (IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away P')
      (P := Localization.Away (P' * (Polynomial.X - Polynomial.C c))) P' (Polynomial.X - Polynomial.C c) x).symm

theorem maps_from_open_line_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ B.left) (a b : Localization.Away P →ₐ[k] k), u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u = spMap b.toRingHom ≫ u := by
  intro k _ _ B _ hB P hP u a b hu
  haveI := hB.smooth
  haveI := hB.proper
  obtain ⟨Q, hQ, σ, τ, h1, h2⟩ := GlobalTheory.T.exists_inversion_coordinate_localization_polynomial k P hP
  obtain ⟨f₀, hf₀, e₀⟩ := extend_to_line k B P hP u hu
  have hu' : (spMap σ.toRingHom ≫ u) ≫ B.hom = spMap (algebraMap k (Localization.Away Q)) := by
    rw [Category.assoc, hu, ← spMap_comp']
    congr 1
    ext x
    exact σ.commutes x
  obtain ⟨f₁, hf₁, e₁⟩ := extend_to_line k B Q hQ _ hu'
  haveI : IsDominant (spMap (rhoMap k P)) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (rhoMap k P))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (awayToAwayRight_injective k P hP)]
    exact bot_le
  have hc : spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial k) :
        Localization.Away (Polynomial.X : Polynomial k))).toRingHom ≫ f₁ := by
    refine ext_of_isDominant_of_isSeparated B.hom ?_ (spMap (rhoMap k P)) ?_
    · rw [Category.assoc, Category.assoc, hf₀, hf₁, ← spMap_comp', ← spMap_comp']
      congr 1
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    · calc spMap (rhoMap k P) ≫ spMap (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) ≫ f₀
          = spMap ((rhoMap k P).comp (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))) ≫ f₀ := by
            rw [spMap_comp' (algebraMap (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k))) (rhoMap k P),
              Category.assoc]
        _ = spMap τ.toRingHom ≫ spMap σ.toRingHom ≫ u := by
            rw [rhoMap_comp_algebraMap, ← h1, spMap_comp', Category.assoc, e₀]
            show spMap (τ.toRingHom.comp σ.toRingHom) ≫ u = _
            rw [spMap_comp', Category.assoc]
        _ = spMap (τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q))) ≫ f₁ := by
            rw [spMap_comp', Category.assoc, e₁]
        _ = _ := by
            rw [h2, ← rhoMap_comp_aeval, spMap_comp', Category.assoc]
  have key := GlobalTheory.T.projectiveLine_to_abelianVariety_const k B hB f₀ f₁ hf₀ hf₁ hc
    (a.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
    (b.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away P)))
  rw [← e₀, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp']
  exact key

end GlobalTheory.NoRatCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismOpenAffineLineAbelianSchemeConstStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_open_affine_line_abelianScheme_const : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ B.left) (a b : Localization.Away P →ₐ[k] k), u ≫ B.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u = spMap b.toRingHom ≫ u := by
  first | exact @GlobalTheory.NoRatCurve.maps_from_open_line_const | exact GlobalTheory.NoRatCurve.maps_from_open_line_const | (intros; apply GlobalTheory.NoRatCurve.maps_from_open_line_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroup
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS.ArcInf
variable {k : Type} [Field k] [IsAlgClosed k]

theorem exists_eval_ne_zero_of_ne_zero {p : Polynomial k} (hp : p ≠ 0) : ∃ t, p.eval t ≠ 0 := by
  by_contra h
  push_neg at h
  exact hp (Polynomial.funext fun t => by rw [h t, Polynomial.eval_zero])

theorem comp_linear_ne_zero {p : Polynomial k} (hp : p ≠ 0) {c e : k} (hc : c ≠ 0) :
    p.comp (Polynomial.C c * Polynomial.X + Polynomial.C e) ≠ 0 := by
  intro h
  rw [Polynomial.comp_eq_zero_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact hp h
  · have := congrArg (fun p : Polynomial k => p.coeff 1) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, Polynomial.coeff_C,
      one_ne_zero, if_false, mul_one, add_zero] at this
    exact hc (by simpa using this)

theorem exists_rational_family {G : Over (Sp k)} [GrpObj G] (hG : SmConn G)
    (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (hna : ¬ ∃ b : algOver k (PowerSeries k) ⟶ G, algOverHom (toK k) ≫ b = a) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ)
      (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)) (t₁ t₂ : k),
      IsChart G j ε f ∧ Pd ≠ 0 ∧ (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) ∧
      Pd.eval t₁ ≠ 0 ∧ Pd.eval t₂ ≠ 0 ∧ ψ t₁ ≠ ψ t₂ := by
  obtain ⟨A, _, _, j, ε, r, f, hc⟩ := GlobalTheory.T.exists_affineUnitChart_smoothGroupScheme k G hG
  obtain ⟨h, d, hd1, hh1, ht⟩ := GlobalTheory.T.exists_arcQuotient_twoVariable_coords k G A j ε r f hc a
  have hsep := hG.2.2.1
  have hXd := mt ((GlobalTheory.T.subst_two_variables_identities_alt k).1 d).1.1 hd1
  have hXh := fun i => ((GlobalTheory.T.subst_two_variables_identities_alt k).1 (h i)).1.2 (hh1 i)
  have hd' : (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) ≠ 0 := fun e => hXd (e ▸ dvd_zero _)
  have hd : d ≠ 0 := by
    rintro rfl
    apply hd1
    rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero
      fun i => by fin_cases i <;> exact PowerSeries.constantCoeff_X), map_zero]
  by_cases hQ : ∀ i, MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) d) < MvPowerSeries.weightedOrder (![1, 1] : Fin 2 → ℕ) (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))
  · exfalso
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' le_rfl le_rfl (fun i => (hQ i).le)
    obtain ⟨ch1, ch2⟩ := GlobalTheory.T.relation_of_gen_of_order_eq k (fun z w => Rel a z w 1)
      (fun m n => ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
        ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → Rel a z (PowerSeries.C t * PowerSeries.X ^ n) 1)
      (fun z w h => by simpa using h.symm) (fun x y z h h' => by simpa using h.trans h') (fun _ _ h => h)
    have g11 := ch1 1 1 (fun z hz => by
      have hz0 := coeff_ne_of_order hz
      refine ⟨insert 0 ((fun t => (t + 1) * PowerSeries.coeff 1 z) '' {t | Pd.IsRoot t}),
        ((Polynomial.finite_setOfPred_isRoot hPd).image _).insert _, fun t hS => ?_⟩
      have e : t / PowerSeries.coeff 1 z * PowerSeries.coeff 1 z = t := div_mul_cancel₀ _ hz0
      have ht0 : t ≠ 0 := fun e => hS (Or.inl e)
      have hp : Pd.eval (t / PowerSeries.coeff 1 z - 1) ≠ 0 := fun e' =>
        hS (Or.inr ⟨_, e', by simp only [sub_add_cancel, e]⟩)
      obtain ⟨h1, h2⟩ := mul_step le_rfl hg z hz _ (div_ne_zero ht0 hz0) hp
      have : ψ (t / PowerSeries.coeff 1 z - 1) = ε := hc.hom_ext fun i => by
        have := h1 i
        rw [(hP i).2 (hQ i), Polynomial.eval_zero, mul_eq_zero] at this
        rw [hc.2.2.2, this.resolve_right hp]
      rwa [this, hc.2.1, e] at h2)
    obtain ⟨-, s2, s3, s4⟩ := GlobalTheory.T.weightedOrder_slope_comparison_alt k r h d hd _ (fun _ _ => Iff.rfl)
    obtain ⟨m₀, hm₀⟩ := s2 (ht.lt_of_rel hc hd le_rfl le_rfl g11)
    have all := ch2 (m₀ + 1) fun m hm =>
      ht.gen_of_lt hc hd (m := m) (n := m + 1) (by omega) (by omega) (hm₀ m (by omega))
    refine hna (GlobalTheory.T.arc_extends_of_regular_second_axis k G A j ε r f hc a h d hd ht (s4 fun n hn => ?_))
    refine (s3 1 n (m₀ + 1) (by omega)).1 (ht.lt_of_rel hc hd (by omega) (Nat.mul_pos (by omega) hn) ?_)
    intro z w hz hw
    exact all _ _ z w (by omega) (Nat.le_mul_of_pos_right _ hn) hz hw
  · obtain ⟨m, n, hm, hmn, hle, i, hi⟩ := (GlobalTheory.T.weightedOrder_slope_comparison_alt k r (fun i => (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 0 + MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) k) (h i))) _ hd' _
      (fun _ _ => Iff.rfl)).1 hXh hXd ⟨1, 1, le_rfl, le_rfl, hQ⟩
    obtain ⟨Pd, P, ψ, hPd, hP, hg⟩ := ht.shear hc hd' hm (hm.trans hmn) hle
    have hPi : P i ≠ 0 := fun e => ((hP i).1 e).ne hi
    have triv : ∀ t, Pd.eval t ≠ 0 → (∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
        algOverHom (ψ t) ≫ j = 1 → (P i).eval t = 0 := fun t ht h1 h => by
      have e : ψ t = ε := eq_of_comp_eq hc.1 (h.trans hc.2.1.symm)
      rw [← h1 i, e, hc.2.2.2 i, zero_mul]
    rcases hmn.lt_or_eq with hlt | rfl
    · have hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t :=
        fun t ht => (add_step hlt hg 0 t ht).1
      have hmul : ∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
          (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t + t')) ≫ j := by
        intro t t' h1 h2 h3
        have e1 := (add_step hlt hg 0 t' h2).2
        have e2 := (add_step hlt hg (t' + 0) t h1).2
        have e3 := (add_step hlt hg 0 (t + t') h3).2
        rw [_root_.add_assoc] at e3
        exact Red.unique hsep (e1.trans e2) e3
      obtain ⟨t', ht'⟩ := exists_eval_ne_zero_of_ne_zero hPd
      obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero hPd hPi)
        (comp_linear_ne_zero hPd (one_ne_zero (α := k)) (e := t')))
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨hpt, hpi⟩, hpt2⟩ := ht
      refine ⟨A, _, _, j, ε, r, f, Pd, P, ψ, t + t', t', hc, hPd, hψ, hpt2, ht', fun e => hpi ?_⟩
      have h := hmul t t' hpt ht' hpt2
      rw [e] at h
      exact triv t hpt (hψ t hpt) (mul_eq_right.1 h)
    · have ev : ∀ (q : Polynomial k) (t : k), (q.comp (Polynomial.X - Polynomial.C 1)).eval t = q.eval (t - 1) :=
        fun q t => by simp
      have hψ : ∀ t, t ≠ 0 → Pd.eval (t - 1) ≠ 0 → ∀ i, ψ (t - 1) (f i) * Pd.eval (t - 1) = (P i).eval (t - 1) :=
        fun t h0 h1 => (mul_step hm hg _ (order_mon one_ne_zero m) t h0 h1).1
      have hmul : ∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval (t - 1) ≠ 0 → Pd.eval (t' - 1) ≠ 0 → Pd.eval (t * t' - 1) ≠ 0 →
          (algOverHom (ψ (t - 1)) ≫ j) * (algOverHom (ψ (t' - 1)) ≫ j) = algOverHom (ψ (t * t' - 1)) ≫ j := by
        intro t t' h0 h0' h1 h2 h3
        have e1 := (mul_step hm hg _ (order_mon one_ne_zero m) t' h0' h2).2
        have e3 := (mul_step hm hg _ (order_mon one_ne_zero m) _ (mul_ne_zero h0 h0') h3).2
        rw [coeff_mon, _root_.mul_one] at e1 e3
        have e2 := (mul_step hm hg _ (order_mon h0' m) t h0 h1).2
        rw [coeff_mon] at e2
        exact Red.unique hsep (e1.trans e2) e3
      have hQ1 : Pd.comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0 :=
        comp_linear_ne_zero hPd one_ne_zero
      have hQ2 : (P i).comp (Polynomial.C 1 * Polynomial.X + Polynomial.C (-1)) ≠ 0 :=
        comp_linear_ne_zero hPi one_ne_zero
      obtain ⟨t', ht'⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero Polynomial.X_ne_zero hQ1)
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht'
      obtain ⟨h0', hpt'⟩ := ht'
      obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        Polynomial.X_ne_zero hQ1) hQ2) (comp_linear_ne_zero hPd h0' (e := -1)))
      simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X, _root_.one_mul, ne_eq, mul_eq_zero, not_or, ← sub_eq_add_neg] at ht
      obtain ⟨⟨⟨h0, hpt⟩, hpi⟩, hpt2⟩ := ht
      rw [mul_comm t' t] at hpt2
      refine ⟨A, _, _, j, ε, r, f, Polynomial.X * Pd.comp (Polynomial.X - Polynomial.C 1),
        fun i => Polynomial.X * (P i).comp (Polynomial.X - Polynomial.C 1), fun t => ψ (t - 1), t * t', t', hc,
        mul_ne_zero Polynomial.X_ne_zero (mt comp_sub_one_eq_zero.1 hPd), fun s hs i => ?_, ?_, ?_, fun e => hpi ?_⟩
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev] at hs
        rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, ev, ev,
          ← hψ s (left_ne_zero_of_mul hs) (right_ne_zero_of_mul hs) i]
        ring
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev]
        exact mul_ne_zero (mul_ne_zero h0 h0') hpt2
      · rw [Polynomial.eval_mul, Polynomial.eval_X, ev]
        exact mul_ne_zero h0' hpt'
      · have h := hmul t t' h0 h0' hpt hpt' hpt2
        have e' : ψ (t * t' - 1) = ψ (t' - 1) := e
        rw [e'] at h
        exact triv (t - 1) hpt (hψ t h0 hpt) (mul_eq_right.1 h)

end GlobalTheory.SS.ArcInf

noncomputable section
namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

section Curve
variable {k : Type} [Field k]

def evAway (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) : Localization.Away Pd →ₐ[k] k :=
  { IsLocalization.Away.lift Pd (g := Polynomial.evalRingHom t) (IsUnit.mk0 _ ht) with
    commutes' := fun c => by
      show IsLocalization.Away.lift Pd _ (algebraMap k (Localization.Away Pd) c) = c
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away Pd)]
      simp [IsLocalization.Away.lift] }

theorem evAway_alg (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) (q : Polynomial k) :
    evAway Pd t ht (algebraMap _ _ q) = q.eval t := by
  simp [evAway, IsLocalization.Away.lift]

theorem evAway_invSelf (Pd : Polynomial k) (t : k) (ht : Pd.eval t ≠ 0) :
    evAway Pd t ht (IsLocalization.Away.invSelf Pd) = (Pd.eval t)⁻¹ := by
  have h := congrArg (evAway Pd t ht) (IsLocalization.Away.mul_invSelf (S := Localization.Away Pd) Pd)
  rw [map_mul, evAway_alg, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem eq_zero_of_evAway [Infinite k] {Pd : Polynomial k} (hPd : Pd ≠ 0) (x : Localization.Away Pd)
    (hx : ∀ t (ht : Pd.eval t ≠ 0), evAway Pd t ht x = 0) : x = 0 := by
  obtain ⟨⟨Q, ⟨_, n, rfl⟩⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers Pd) x
  have hQ0 : Q * Pd = 0 := by
    refine Polynomial.funext fun t => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_zero]
    by_cases ht : Pd.eval t = 0
    · rw [ht, mul_zero]
    · have := congrArg (evAway Pd t ht) hQ
      simp only [map_mul, evAway_alg, hx t ht, zero_mul] at this
      rw [← this, zero_mul]
  have hQ' : Q = 0 := (mul_eq_zero.1 hQ0).resolve_right hPd
  simp only [hQ', map_zero] at hQ
  exact (IsLocalization.map_units (Localization.Away Pd) (⟨Pd ^ n, n, rfl⟩ : Submonoid.powers Pd)).mul_left_eq_zero.1 hQ

variable [Infinite k] {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A]
  {j : algOver k A ⟶ G} {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A}

theorem exists_algHom_of_family (hc : IsChart G j ε f) {Pd : Polynomial k} (hPd : Pd ≠ 0)
    (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k))
    (hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) :
    ∃ Ψ : A →ₐ[k] Localization.Away Pd, ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Ψ = ψ t := by
  let g : Fin r → Localization.Away Pd := fun i =>
    algebraMap (Polynomial k) _ (P i) * IsLocalization.Away.invSelf Pd
  have hg : ∀ t (ht : Pd.eval t ≠ 0) i, evAway Pd t ht (g i) = ψ t (f i) := fun t ht i => by
    simp only [g, map_mul, evAway_alg, evAway_invSelf]
    rw [← hψ t ht i, mul_inv_cancel_right₀ ht]
  let φ : MvPolynomial (Fin r) k →ₐ[k] A := MvPolynomial.aeval f
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hc.2.2.1
  let Φ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away Pd := MvPolynomial.aeval g
  have hev : ∀ t (ht : Pd.eval t ≠ 0), (evAway Pd t ht).comp Φ = (ψ t).comp φ := fun t ht => by
    rw [MvPolynomial.comp_aeval, MvPolynomial.comp_aeval]
    exact congrArg _ (funext (hg t ht))
  have hker : RingHom.ker φ ≤ RingHom.ker Φ := fun p hp => by
    rw [RingHom.mem_ker] at hp ⊢
    refine eq_zero_of_evAway hPd _ fun t ht => ?_
    have := AlgHom.congr_fun (hev t ht) p
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at this
    rw [this, show φ p = 0 from hp, map_zero]
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let Ψ : A →ₐ[k] Localization.Away Pd :=
    (Ideal.Quotient.liftₐ (RingHom.ker φ) Φ fun p hp => hker hp).comp e.symm.toAlgHom
  have hΨ : Ψ.comp φ = Φ := by
    ext p
    simp only [Ψ, AlgHom.comp_apply]
    have : e.symm (φ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (MvPolynomial.X p) := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker φ) Φ _) (e.symm (φ (MvPolynomial.X p))) = _
    rw [this]
    rfl
  refine ⟨Ψ, fun t ht => ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨p, rfl⟩ := hsurj x
  have := AlgHom.congr_fun (hev t ht) p
  rw [← hΨ] at this
  simpa only [AlgHom.comp_apply] using this

theorem curve_of_family (hc : IsChart G j ε f) {Pd : Polynomial k} (hPd : Pd ≠ 0)
    (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k))
    (hψ : ∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) {t₁ t₂ : k}
    (h₁ : Pd.eval t₁ ≠ 0) (h₂ : Pd.eval t₂ ≠ 0) (hne : ψ t₁ ≠ ψ t₂) :
    ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left)
      (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧
      spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  obtain ⟨Ψ, hΨ⟩ := exists_algHom_of_family hc hPd P ψ hψ
  refine ⟨Pd, hPd, (algOverHom Ψ ≫ j).left, evAway Pd t₁ h₁, evAway Pd t₂ h₂, Over.w _, fun e => hne ?_⟩
  have key : ∀ t (ht : Pd.eval t ≠ 0), spMap (evAway Pd t ht).toRingHom ≫ (algOverHom Ψ ≫ j).left =
      (algOverHom (ψ t) ≫ j).left := fun t ht => by
    rw [← hΨ t ht, algOverHom_comp, Over.comp_left, Over.comp_left, Over.comp_left, algOverHom_left]
    rfl
  rw [key, key] at e
  exact eq_of_comp_eq hc.1 (Over.OverMorphism.ext e)

end Curve
end GlobalTheory.RatCurve

namespace GlobalTheory.RatCurve
open GlobalTheory.SS GlobalTheory.SS.ArcInf

theorem exists_rational_curve : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G],
    GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left)
      (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧
      spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  intro k _ _ G _ hG hnp
  have : Smooth G.hom := hG.2.1
  have : GeometricallyConnected G.hom := hG.2.2.2.2
  have : IsIntegral G.left := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected G.hom
  have harc : ∃ a : Sp (FractionRing (PowerSeries k)) ⟶ G.left,
      a ≫ G.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) ∧
      ¬ ∃ b : Sp (PowerSeries k) ⟶ G.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a := by
    by_contra hno
    refine hnp (GlobalTheory.ArcProper.isProper_of_arcs k G hG.2.2.1 inferInstance hG.2.2.2.1 fun a ha => ?_)
    by_contra hb
    exact hno ⟨a, ha, hb⟩
  obtain ⟨a, ha, hna⟩ := harc
  obtain ⟨A, _, _, j, ε, r, f, Pd, P, ψ, t₁, t₂, hc, hPd, hψ, h₁, h₂, hne⟩ :=
    exists_rational_family hG (Over.homMk a ha) (by
      rintro ⟨b, hb⟩
      exact hna ⟨b.left, congrArg (fun x => x.left) hb⟩)
  exact curve_of_family hc hPd P ψ hψ h₁ h₂ hne

end GlobalTheory.RatCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonconstantRationalCurveNonproperGroupStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ¬ IsProper G.hom → ∃ (P : Polynomial k) (_ : P ≠ 0) (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u := by
  first | exact @GlobalTheory.RatCurve.exists_rational_curve | exact GlobalTheory.RatCurve.exists_rational_curve | (intros; apply GlobalTheory.RatCurve.exists_rational_curve <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ManyTorsionProper

theorem isProper_of_many_torsion_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ _ G _ hG g hg m s hs hcard
  by_contra hnp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hcard
    · exact h
  obtain ⟨P, hP, u, a, b, hu, hab⟩ := GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group k G hG hnp
  obtain ⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩ :=
    GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve k G hG g hg m hm s hs P hP u a b hu hab
  have hpr : IsProper G'.hom :=
    GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)
  exact hab' (GlobalTheory.T.morphism_open_affine_line_abelianScheme_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')

end GlobalTheory.ManyTorsionProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_many_torsion_points_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  first | exact @GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero | exact GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero | (intros; apply GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperOfInfinitelyManyLargeTorsionCounts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.properOfInfinitelyManyLargeTorsionCounts :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G →
      ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ,
      {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧
        m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  intro k _ _ G _ hG g hsm C hinf
  obtain ⟨m, ⟨hm0, s, hs, hle⟩, hCm⟩ := hinf.exists_gt C
  have hm1 : 1 ≤ m := by omega
  have hcard : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h | h
    · rw [h, Nat.mul_zero] at hle
      have : 0 < m ^ (2 * g) := Nat.pow_pos hm1
      omega
    · exact h
  have hlt : m ^ (2 * g) < m * s.card :=
    lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right hCm hcard)
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    exact GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k p G hG g hsm m hm0 s hs hlt
  · subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    exact GlobalTheory.T.isProper_of_many_torsion_points_charZero k G hG g hsm m s hs hlt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperOfInfinitelyManyLargeTorsionCountsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_infinitely_many_large_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ C : ℕ, {m : ℕ | (m : k) ≠ 0 ∧ ∃ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) ∧ m ^ (2 * g) ≤ C * s.card}.Infinite → IsProper G.hom := by
  first | exact @GlobalTheory.properOfInfinitelyManyLargeTorsionCounts | exact GlobalTheory.properOfInfinitelyManyLargeTorsionCounts | (intros; apply GlobalTheory.properOfInfinitelyManyLargeTorsionCounts <;> assumption)
end
