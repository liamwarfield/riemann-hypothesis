module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologousNegTorsorCocycleOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProdu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointPreimageTopOfReduction
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem evalSectionAtPointOrZero_specMap_comp (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) (h : ⊤ ≤ x ⁻¹ᵁ U) : evU (spMap φ ≫ x) U a = φ (evU x U a) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ _)
  unfold evU
  rw [dite_eq_left h', dite_eq_left h]
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
  have e := congrArg (fun k => k.hom (x.appLE U ⊤ h a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  exact e

theorem evalSectionAtPointOrZero_restriction (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) : evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hV.trans (fun p hp ↦ h hp)
  unfold evU
  rw [dite_eq_left hV, dite_eq_left hU]
  unfold GlobalTheory.Cris.evalAt
  have e := congrArg (fun k => k.hom a) (Scheme.Hom.map_appLE x hV (homOfLE h).op)
  simp only [RingHom.comp_apply, CommRingCat.comp_apply] at e ⊢
  rw [e]

theorem dualNumberSndMulInverseFst_mul_units (D : Type) [CommRing D] (u u' : DualNumber D) (hu : IsUnit u) (hu' : IsUnit u') : dl (u * u') = dl u + dl u' := by
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  obtain ⟨v', hv'⟩ := hu'.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv hv'
  unfold dl
  rw [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, ← hv, ← hv', ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit, Ring.inverse_unit]
  rw [mul_inv_rev, Units.val_mul]
  have a1 : (v : D) * ↑v⁻¹ = 1 := Units.mul_inv v
  have a2 : (v' : D) * ↑v'⁻¹ = 1 := Units.mul_inv v'
  linear_combination (u'.snd * ↑v'⁻¹) * a1 + (u.snd * ↑v⁻¹) * a2

theorem dualNumberAlgHomMap_fst_snd_logDerivative (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D) : (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u)) := by
  have h1 : (epsHom φ u).fst = φ u.fst := by
    simp [epsHom, DualNumber.lift_apply_apply]
  have h2 : (epsHom φ u).snd = φ u.snd := by
    simp [epsHom, DualNumber.lift_apply_apply]
  refine ⟨h1, h2, fun hu ↦ ?_⟩
  obtain ⟨v, hv⟩ := hu.map (TrivSqZeroExt.fstHom D D D)
  simp only [TrivSqZeroExt.fstHom_apply] at hv
  unfold dl
  rw [h1, h2, ← hv, Ring.inverse_unit, map_mul]
  have : φ (v : D) = ((Units.map (φ : D →* D') v : D'ˣ) : D') := rfl
  rw [this, Ring.inverse_unit]
  rfl
theorem evalSectionAtPointOrZero_schemeHom_app (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) : evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a := by
  unfold evU
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dite_eq_left h, dite_eq_left h']
    unfold GlobalTheory.Cris.evalAt
    simp only [RingHom.comp_apply]
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  · have h' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ U := h
    rw [dite_eq_right h, dite_eq_right h']

theorem dualNumberPoint_preimage_top_of_reduction (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  let f : DualNumber D →+* D := (TrivSqZeroExt.fstHom D D D).toRingHom
  have hf : Function.Surjective f := fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩
  intro p _
  change PrimeSpectrum (DualNumber D) at p
  have hp : p ∈ Set.range (PrimeSpectrum.comap f) := by
    rw [range_comap_of_surjective D f hf, PrimeSpectrum.mem_zeroLocus]
    intro z hz
    change z.fst = 0 at hz
    have hz₂ : z ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext <;> simp [hz]
    exact p.isPrime.mem_of_pow_mem 2 (hz₂ ▸ p.asIdeal.zero_mem)
  obtain ⟨q, hq⟩ := hp
  exact hq ▸ h (Set.mem_univ q)

theorem evU_dl_rules : (∀ (Y : Scheme.{0}) (D D' : Type) [CommRing D] [CommRing D'] (φ : D →+* D') (x : Sp D ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ U → evU (spMap φ ≫ x) U a = φ (evU x U a)) ∧ (∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y, U)), ⊤ ≤ x ⁻¹ᵁ V → evU x V ((Y.presheaf.map (homOfLE h).op).hom a) = evU x U a) ∧ (∀ (Y Z : Scheme.{0}) (D : Type) [CommRing D] (x : Sp D ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)), evU x (q ⁻¹ᵁ U) ((q.app U).hom a) = evU (x ≫ q) U a) ∧ (∀ (D : Type) [CommRing D] (u u' : DualNumber D), IsUnit u → IsUnit u' → dl (u * u') = dl u + dl u') ∧ (∀ (R D D' : Type) [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (u : DualNumber D), (epsHom φ u).fst = φ u.fst ∧ (epsHom φ u).snd = φ u.snd ∧ (IsUnit u → dl (epsHom φ u) = φ (dl u))) ∧ ∀ (Y : Scheme.{0}) (D : Type) [CommRing D] (y : Sp (DualNumber D) ⟶ Y) (U : Y.Opens), ⊤ ≤ (spMap (TrivSqZeroExt.fstHom D D D).toRingHom ≫ y) ⁻¹ᵁ U → ⊤ ≤ y ⁻¹ᵁ U :=
  ⟨evalSectionAtPointOrZero_specMap_comp, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_schemeHom_app, dualNumberSndMulInverseFst_mul_units, dualNumberAlgHomMap_fst_snd_logDerivative, dualNumberPoint_preimage_top_of_reduction⟩

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunction
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatSec

theorem nat_of_comp (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
      (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
    (x : Pt Y D) (x' : Pt Y D') (hx : ⊤ ≤ x.left ⁻¹ᵁ U) (h : spMap φ ≫ x.left = x'.left) :
    t D' x' = φ (t D x) := by
  have h1 : x.left ≫ Y.hom = spMap (algebraMap R D) := Over.w x
  have h2 : x'.left ≫ Y.hom = spMap (algebraMap R D') := Over.w x'
  have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ ≫ spMap _ = spMap _
    rw [← h1, ← h2, ← h, Category.assoc]
  let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
  have h4 := ht D D' ψ x hx
  have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
  rw [h5] at h4
  exact h4

theorem fromSpecStalk_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem ext_of_evU (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (a a' : Γ(Y.left, U))
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U a = evU z.left U a') : a = a' := by
  refine TopCat.Presheaf.section_ext Y.left.sheaf U a a' fun y hy ↦ ?_
  let S : CommRingCat.{0} := Y.left.presheaf.stalk y
  letI al : Algebra R S := (Spec.preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).hom.toAlgebra
  let z : Pt Y S := Over.homMk (Y.left.fromSpecStalk y)
    (Spec.map_preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).symm
  have hz : ⊤ ≤ z.left ⁻¹ᵁ U := fromSpecStalk_top y U hy
  have e := h S z hz
  unfold evU at e
  rw [dite_eq_left hz, dite_eq_left hz] at e
  unfold evalAt at e
  change (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a) =
    (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a') at e
  rw [fromSpecStalk_appLE y U hy] at e
  simp only [CommRingCat.comp_apply] at e
  change (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ = (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ at e
  simp only [Iso.inv_hom_id_apply] at e
  exact e

theorem exists_unique_section : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) → ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → evU z.left U a = t E z := by
  intro R _ Y U t ht
  let Z : Scheme.{0} := U.toScheme
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), @Pt R _ Y D _ (al D x) := fun D x ↦
    Over.homMk (x ≫ U.ι) (by rw [Category.assoc]; exact (Spec.map_preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).symm)
  have hin : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), ⊤ ≤ (x ≫ U.ι) ⁻¹ᵁ U := by
    intro D x p _
    exact (x p).2
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Z) → D := fun D x ↦ @t D _ (al D x) (pt D x)
  obtain ⟨s, hs⟩ := NatConst.exists_section Z (fun _ : Unit ↦ (⊤ : Z.Opens)) (by simp) κ
    fun D D' φ x _ ↦ @NatSec.nat_of_comp R _ Y U t ht D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom
      (pt D x) (pt D' _) (hin D x) (by change Spec.map φ ≫ x ≫ U.ι = (Spec.map φ ≫ x) ≫ U.ι; rw [Category.assoc])
  have hex : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U (U.topIso.hom s) = t E z := by
    intro E _ inst z hz
    have hr : Set.range z.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact hz (Set.mem_univ q)
    let w : Spec (CommRingCat.of E) ⟶ Z := IsOpenImmersion.lift U.ι z.left hr
    have hw : w ≫ U.ι = z.left := IsOpenImmersion.lift_fac U.ι z.left hr
    have h1 : κ (CommRingCat.of E) w = t E z := by
      refine (@NatSec.nat_of_comp R _ Y U t ht E _ inst E _ (al (CommRingCat.of E) w) (RingHom.id E) z
        (pt (CommRingCat.of E) w) hz ?_)
      change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫ z.left = w ≫ U.ι
      rw [hw, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [← h1, hs (CommRingCat.of E) w ⟨(), le_top⟩]
    unfold evU
    rw [dite_eq_left hz]
    unfold evalAt
    simp only [RingHom.comp_apply]
    congr 1
    have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
      rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    have key : ∀ (g : Spec (CommRingCat.of E) ⟶ Y.left) (_ : w ≫ U.ι = g) (h : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ h = U.topIso.inv ≫ w.appLE ⊤ ⊤ le_top := by
      rintro _ rfl h
      rw [← hι]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [key _ hw hz, CommRingCat.comp_apply, Iso.hom_inv_id_apply]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨U.topIso.hom s, hex, fun a ha ↦ ?_⟩
  exact NatSec.ext_of_evU R Y U a _ fun E _ _ z hz ↦ (ha E z hz).trans (hex E z hz).symm

end GlobalTheory.PtExt.NatSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunctionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_unique_section_of_natural_pointwise_function
    (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) :
    ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E),
      ⊤ ≤ z.left ⁻¹ᵁ U → evU (D := E) z.left U a = t E z :=
  GlobalTheory.PtExt.NatSec.exists_unique_section R Y U t ht
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGenerator
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem triv_pull_of_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t →
    GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  intro R _ X Y L _ q t ht
  unfold IsPtGen at ht
  obtain ⟨hu, hn, hg⟩ := ht
  have hmul : ∀ {D : Type} [CommRing D] (x : Sp D ⟶ Y.left) (U : Y.left.Opens), ⊤ ≤ x ⁻¹ᵁ U →
      ∀ a b : Γ(Y.left, U), evU x U (a * b) = evU x U a * evU x U b := by
    intro D _ x U h a b; unfold evU; rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, map_mul]
  have hone : ∀ {D : Type} [CommRing D] (x : Sp D ⟶ Y.left) (U : Y.left.Opens), ⊤ ≤ x ⁻¹ᵁ U →
      evU x U (1 : Γ(Y.left, U)) = 1 := by
    intro D _ x U h; unfold evU; rw [dite_eq_left h, map_one]
  have hch : ∀ (j : PUnit → L.ι) {E : Type} [CommRing E] [Algebra R E] (z : Pt Y E),
      ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j → ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U (j PUnit.unit) :=
    fun j E _ _ z h p hp ↦ LB.wchart_le L (K := PUnit) (fun _ ↦ q.left) j PUnit.unit (h hp)
  have huniq : ∀ (U : Y.left.Opens) (f : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → f E' (spOver ψ ≫ z) = ψ (f E z)) →
      ∀ c c' : Γ(Y.left, U), (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
        evU z.left U c = f E z) → (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
        evU z.left U c' = f E z) → c = c' :=
    fun U f hf c c' hc hc' ↦ (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y U f hf).unique hc hc'
  have hnat : ∀ j : PUnit → L.ι, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j →
      t E' (spOver ψ ≫ z) (j PUnit.unit) = ψ (t E z (j PUnit.unit)) :=
    fun j E _ _ E' _ _ ψ z h ↦ hn E E' ψ z _ (hch j z h)
  have hnatI : ∀ j : PUnit → L.ι, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j →
      Ring.inverse (t E' (spOver ψ ≫ z) (j PUnit.unit)) = ψ (Ring.inverse (t E z (j PUnit.unit))) := by
    intro j E _ _ E' _ _ ψ z h
    rw [hnat j E E' ψ z h]
    obtain ⟨u, hu'⟩ := hu E z _ (hch j z h)
    rw [← hu', Ring.inverse_unit]
    have e : ψ (u : E) = ((Units.map (ψ : E →* E') u : E'ˣ) : E') := rfl
    rw [e, Ring.inverse_unit]
    rfl
  have ex := fun j : PUnit → L.ι ↦
    (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y ((L.pull q.left).U j) (fun E _ _ z ↦ t E z (j PUnit.unit)) (hnat j)).exists
  have exI := fun j : PUnit → L.ι ↦
    (GlobalTheory.T.exists_unique_section_of_natural_pointwise_function R Y ((L.pull q.left).U j) (fun E _ _ z ↦ Ring.inverse (t E z (j PUnit.unit))) (hnatI j)).exists
  choose a ha using ex
  choose b hb using exI
  have hab : ∀ j, a j * b j = 1 := by
    intro j
    refine huniq _ (fun _ _ _ _ ↦ 1) (fun E _ _ E' _ _ ψ z _ ↦ (map_one ψ).symm) _ _ ?_ ?_
    · intro E _ _ z h
      rw [hmul _ _ h, ha j E z h, hb j E z h]
      exact Ring.mul_inverse_cancel _ (hu E z _ (hch j z h))
    · intro E _ _ z h
      exact hone _ _ h
  refine ⟨⟨fun j ↦ ⟨a j, b j, hab j, by rw [mul_comm]; exact hab j⟩⟩, ?_⟩
  intro i j
  apply Units.ext
  have hVi : (L.pull q.left).U i ⊓ (L.pull q.left).U j ≤ (L.pull q.left).U i := inf_le_left
  have hVj : (L.pull q.left).U i ⊓ (L.pull q.left).U j ≤ (L.pull q.left).U j := inf_le_right
  refine huniq ((L.pull q.left).U i ⊓ (L.pull q.left).U j) (fun E _ _ z ↦ t E z (i PUnit.unit))
    (fun E _ _ E' _ _ ψ z h ↦ hnat i E E' ψ z (fun p hp ↦ hVi (h hp))) _ _ ?_ ?_
  · intro E _ _ z h
    have e1 := evalSectionAtPointOrZero_restriction Y.left E z.left _ _ hVi (a i) h
    refine Eq.trans ?_ ((e1.trans (ha i E z (fun p hp ↦ hVi (h hp)))))
    rfl
  · intro E _ _ z h
    have hzi : ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U i := fun p hp ↦ hVi (h hp)
    have hzj : ⊤ ≤ z.left ⁻¹ᵁ (L.pull q.left).U j := fun p hp ↦ hVj (h hp)
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      fun p hp ↦ ⟨hch i z hzi hp, hch j z hzj hp⟩
    rw [Units.val_mul, hmul _ _ h]
    have e2 := evalSectionAtPointOrZero_restriction Y.left E z.left _ _ hVj (a j) h
    have e2' : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res hVj (⟨a j, b j, hab j, by rw [mul_comm]; exact hab j⟩ :
        Γ(Y.left, (L.pull q.left).U j)ˣ)).val = t E z (j PUnit.unit) :=
      e2.trans (ha j E z hzj)
    have e3 : evU z.left _ ((L.pull q.left).g i j).val =
        evU (z ≫ q).left (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g (i PUnit.unit) (j PUnit.unit)).val := by
      unfold evU
      rw [dite_eq_left h]
      have hij' : ⊤ ≤ (z ≫ q).left ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := hij
      rw [dite_eq_left hij']
      exact (evalAt_pull_g L q.left z.left i j hij h).symm
    rw [e3, e2']
    exact (hg E z (i PUnit.unit) (j PUnit.unit) (hch i z hzi) (hch j z hzj)).symm

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGeneratorStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t → GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  first | exact @GlobalTheory.PtExt.triv_pull_of_isPtGen | exact GlobalTheory.PtExt.triv_pull_of_isPtGen | (intros; apply GlobalTheory.PtExt.triv_pull_of_isPtGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullb
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem le_pull_chart {X Y : Scheme.{0}} (L : LB X) (q : Y ⟶ X) {D : Type} [CommRing D] (x : Sp D ⟶ Y)
    (i : L.ι) (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ (L.pull q).U (fun _ ↦ i) :=
  fun _ hp ↦ Set.mem_iInter.2 fun _ ↦ h hp

theorem evU_mul {Y : Scheme.{0}} {D : Type} [CommRing D] (x : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU x U (a * b) = evU x U a * evU x U b := by
  simpa only [evU, dite_eq_left h] using map_mul (evalAt x U h) a b

theorem exists_isPtGen : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB →
    ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  intro R _ X Y L _ q hT
  obtain ⟨s, hs⟩ := hT
  refine ⟨fun E _ _ z i ↦ evU z.left ((L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i)).val, ?_, ?_, ?_⟩
  · intro E _ _ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    simpa only [evU, dite_eq_left hz] using
      (s.s (fun _ ↦ i)).isUnit.map (evalAt z.left _ hz)
  · intro E _ _ E' _ _ ψ z i hi
    have hz := le_pull_chart L q.left z.left i hi
    exact evalSectionAtPointOrZero_specMap_comp _ E E' (ψ : E →+* E') z.left _ _ hz
  · intro E _ _ z i j hi hj
    have hzi := le_pull_chart L q.left z.left i hi
    have hzj := le_pull_chart L q.left z.left j hj
    have hV : ⊤ ≤ z.left ⁻¹ᵁ ((L.pull q.left).U (fun _ ↦ i) ⊓ (L.pull q.left).U (fun _ ↦ j)) :=
      fun p hp ↦ ⟨hzi hp, hzj hp⟩
    have hij : ⊤ ≤ (z.left ≫ q.left) ⁻¹ᵁ (L.U i ⊓ L.U j) := fun p hp ↦ ⟨hi hp, hj hp⟩
    have e := congrArg (fun u ↦ evU z.left _ (Units.val u)) (hs (fun _ ↦ i) (fun _ ↦ j))
    simp only [Units.val_mul] at e
    rw [evU_mul _ _ hV] at e
    have e1 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ i)) (s.s (fun _ ↦ i))).val =
        evU z.left _ (s.s (fun _ ↦ i)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e2 : evU z.left _ (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L.pull q.left).U (fun _ ↦ i) ⊓
        (L.pull q.left).U (fun _ ↦ j) ≤ (L.pull q.left).U (fun _ ↦ j)) (s.s (fun _ ↦ j))).val =
        evU z.left _ (s.s (fun _ ↦ j)).val := evalSectionAtPointOrZero_restriction _ _ _ _ _ _ _ hV
    have e3 : evU z.left _ ((L.pull q.left).g (fun _ ↦ i) (fun _ ↦ j)).val =
        evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val := by
      rw [Over.comp_left]
      simpa only [evU, dite_eq_left hV, dite_eq_left hij] using
        (evalAt_pull_g L q.left z.left (fun _ ↦ i) (fun _ ↦ j) hij hV).symm
    rw [e1, e2, e3] at e
    exact e

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseLineBundleGeneratorOfTrivialPullbStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ q : Y ⟶ X, GlobalTheory.AbLaw.Triv (L.pull q.left) → ∃ t, IsPtGen L q t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen | exact GlobalTheory.PtExt.exists_isPtGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundary
set_option autoImplicit false
noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.EpsGenCob

theorem evU_mul' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a b : Γ(Y, U)) : evU y U (a * b) = evU y U a * evU y U b := by
  simpa only [evU, dite_eq_left h] using map_mul (evalAt y U h) a b

theorem evU_isUnit' {Y : Scheme.{0}} {D : Type} [CommRing D] (y : Sp D ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (a : Γ(Y, U)ˣ) : IsUnit (evU y U a.val) := by
  simpa only [evU, dite_eq_left h] using a.isUnit.map (evalAt y U h)

theorem evU_cocycle {X : Scheme.{0}} (P : LB X) (hP : P.IsLB) {D : Type} [CommRing D] (y : Sp D ⟶ X)
    (a b c : P.ι) (ha : ⊤ ≤ y ⁻¹ᵁ P.U a) (hb : ⊤ ≤ y ⁻¹ᵁ P.U b) (hc : ⊤ ≤ y ⁻¹ᵁ P.U c) :
    evU y (P.U a ⊓ P.U c) (P.g a c).val =
      evU y (P.U a ⊓ P.U b) (P.g a b).val * evU y (P.U b ⊓ P.U c) (P.g b c).val := by
  have h3 : ⊤ ≤ y ⁻¹ᵁ (P.U a ⊓ P.U b ⊓ P.U c) := fun p hp ↦ ⟨⟨ha hp, hb hp⟩, hc hp⟩
  have e := congrArg (fun u ↦ evU y _ (Units.val u)) (hP.cocycle a b c)
  simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass] at e
  rw [evU_mul' y _ h3, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction, evalSectionAtPointOrZero_restriction] at e
  · exact e.symm
  all_goals exact h3

theorem snd_eq_fst_mul_dl {D : Type} [CommRing D] (u : DualNumber D) (hu : IsUnit u) : u.snd = u.fst * dl u := by
  have hfst : IsUnit u.fst := hu.map (TrivSqZeroExt.fstHom D D D)
  rw [dl, mul_left_comm, Ring.mul_inverse_cancel _ hfst, _root_.mul_one]

theorem dualNumber_inl_mul_one_add_inr_fst_snd {D : Type} [CommRing D] (a c : D) :
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).fst = a ∧
    (TrivSqZeroExt.inl a * (1 + TrivSqZeroExt.inr c) : DualNumber D).snd = a * c := by
  constructor <;> simp

end GlobalTheory.PtExt.EpsGenCob

namespace GlobalTheory.PtExt.EpsGenCob

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x = x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = toUnit _ ≫ η[B] := by
    refine Over.OverMorphism.ext ?_
    refine hv.trans ?_
    simp [spMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst, Category.comp_id]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by ext; simp
    rw [this]
    refine Over.OverMorphism.ext ?_
    simp [spOver, spMap]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', Hom.one_def, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

theorem ptV_mem (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (i : P.ι) (h : ⊤ ≤ x.left ⁻¹ᵁ chartsA P i) : ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U i := by
  apply dualNumberPoint_preimage_top_of_reduction
  change ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x).left ⁻¹ᵁ P.U i
  rw [red_ptV hv x]
  exact h

theorem ptV_nat (v : epsR R ⟶ B) {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (x : Pt A E) : ptV v (spOver ψ ≫ x) = spOver (epsHom ψ) ≫ ptV v x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
    congr 2
    ext a <;> simp [epsHom, DualNumber.lift_apply_inl]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    congr 2
    apply DualNumber.algHom_ext
    simp [epsHom, EpsWeil.epsMap]

theorem memV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    ⊤ ≤ (ptV v x).left ⁻¹ᵁ (P.U a ⊓ P.U b) := fun p hp ↦
  ⟨ptV_mem P hv x a ha hp, ptV_mem P hv x b hb hp⟩

theorem fst_gV (P : LB (A ⊗ B).left) {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E]
    (x : Pt A E) (a b : P.ι) (ha : ⊤ ≤ x.left ⁻¹ᵁ chartsA P a) (hb : ⊤ ≤ x.left ⁻¹ᵁ chartsA P b) :
    (evU (ptV v x).left (P.U a ⊓ P.U b) (P.g a b).val).fst =
      evU (x ≫ AbDual.inl A B).left (P.U a ⊓ P.U b) (P.g a b).val := by
  have h := evalSectionAtPointOrZero_specMap_comp _ _ _ (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) (ptV v x).left _
    (P.g a b).val (memV P hv x a b ha hb)
  have e : spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ (ptV v x).left =
      (x ≫ AbDual.inl A B).left := by
    rw [← red_ptV hv x, Over.comp_left]; rfl
  rw [e] at h
  rw [h]; rfl

end GlobalTheory.PtExt.EpsGenCob


open GlobalTheory.PtExt.EpsGenCob in
theorem GlobalTheory.PtExt.exists_isEpsGen_of_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j →
    ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  intro R _ A B _ _ P hP v hv j hj s hs k hk
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨fun E _ _ x i ↦ TrivSqZeroExt.inl (s E x i) * (1 + TrivSqZeroExt.inr
    (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)), ?_, ?_, ?_⟩
  · intro E _ _ x i h
    exact ((hs1 E x i h).map (TrivSqZeroExt.inlHom E E)).mul (EpsWeil.epsUnit _).isUnit
  · intro E _ _ E' _ _ ψ x i h
    have h' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P i := fun p _ ↦ h (Set.mem_univ _)
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, h⟩
    have hjx2 : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E x) := fun p _ ↦ hjx (Set.mem_univ _)
    have hjx' : ⊤ ≤ (spOver ψ ≫ x).left ⁻¹ᵁ chartsA P (j E' (spOver ψ ≫ x)) := hj E' _ ⟨i, h'⟩
    have hc := evU_cocycle P hP (ptV v (spOver ψ ≫ x)).left i (j E' (spOver ψ ≫ x)) (j E x)
      (ptV_mem P hv _ i h') (ptV_mem P hv _ _ hjx') (ptV_mem P hv _ _ hjx2)
    have u1 := evU_isUnit' _ _ (memV P hv _ i _ h' hjx') (P.g i (j E' (spOver ψ ≫ x)))
    have u2 := evU_isUnit' _ _ (memV P hv _ _ _ hjx' hjx2) (P.g (j E' (spOver ψ ≫ x)) (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E' _ _ u1 u2
    rw [← hc] at hd
    have uG := evU_isUnit' _ _ (memV P hv x i _ h hjx) (P.g i (j E x))
    have hnat : evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val =
        epsHom ψ (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) := by
      have e : (ptV v (spOver ψ ≫ x)).left = spMap (epsHom ψ : DualNumber E →+* DualNumber E') ≫ (ptV v x).left := by
        rw [ptV_nat, Over.comp_left]; rfl
      rw [e, evalSectionAtPointOrZero_specMap_comp _ _ _ _ _ _ _ (memV P hv x i _ h hjx)]
      rfl
    have e1 : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) =
        ψ (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val)) := by
      rw [hnat, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.2 uG]
    have hcob : dl (evU (ptV v (spOver ψ ≫ x)).left (P.U (j E' (spOver ψ ≫ x)) ⊓ P.U (j E x))
        (P.g (j E' (spOver ψ ≫ x)) (j E x)).val) = k E' (spOver ψ ≫ x) - ψ (k E x) := hk E E' ψ x ⟨i, h⟩
    have hs := hs2 E E' ψ x i h
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E' (spOver ψ ≫ x) i) (dl (evU (ptV v (spOver ψ ≫ x)).left
      (P.U i ⊓ P.U (j E' (spOver ψ ≫ x))) (P.g i (j E' (spOver ψ ≫ x))).val) + k E' (spOver ψ ≫ x))
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [b1, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).1, a1, hs]
    · rw [b2, (dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ _).2.1, a2, hs, map_mul, map_add (f := _)]
      linear_combination (ψ (s E x i)) * (-hd + e1 - hcob)
  · intro E _ _ x i i' hi hi'
    have hjx : ⊤ ≤ x.left ⁻¹ᵁ chartsA P (j E x) := hj E x ⟨i, hi⟩
    have hc := evU_cocycle P hP (ptV v x).left i i' (j E x) (ptV_mem P hv x i hi)
      (ptV_mem P hv x i' hi') (ptV_mem P hv x _ hjx)
    have u1 := evU_isUnit' _ _ (memV P hv x i i' hi hi') (P.g i i')
    have u2 := evU_isUnit' _ _ (memV P hv x i' (j E x) hi' hjx) (P.g i' (j E x))
    have hd := dualNumberSndMulInverseFst_mul_units E _ _ u1 u2
    rw [← hc] at hd
    have hsnd := snd_eq_fst_mul_dl _ u1
    have hfst := fst_gV P hv x i i' hi hi'
    have ht := hs3 E x i i' hi hi'
    obtain ⟨a1, a2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i) (dl (evU (ptV v x).left (P.U i ⊓ P.U (j E x)) (P.g i (j E x)).val) + k E x)
    obtain ⟨b1, b2⟩ := dualNumber_inl_mul_one_add_inr_fst_snd (s E x i') (dl (evU (ptV v x).left (P.U i' ⊓ P.U (j E x)) (P.g i' (j E x)).val) + k E x)
    beta_reduce
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [a1, TrivSqZeroExt.fst_mul, b1, hfst, ht]
    · rw [a2, TrivSqZeroExt.snd_mul, b1, b2, hsnd, hfst, hd, ht, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundaryStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  first | exact @GlobalTheory.PtExt.exists_isEpsGen_of_isCob | exact GlobalTheory.PtExt.exists_isEpsGen_of_isCob | (intros; apply GlobalTheory.PtExt.exists_isEpsGen_of_isCob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGe
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem epsGen_epsEv_apply {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) e u = u.fst + u.snd * ptAlg (R := R) (D := DualNumber R) e DualNumber.eps := by
  simp [epsEv, DualNumber.lift_apply_apply]

theorem epsGen_epsEv_nat {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (R := R) (E := E') (spOver ψ ≫ e) (epsHom ψ u) = ψ (epsEv (R := R) e u) := by
  obtain ⟨h1, h2, -⟩ := dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ u
  simp only [epsGen_epsEv_apply, h1, h2, ptAlg_comp, AlgHom.comp_apply, map_add, map_mul]

theorem epsGen_spMap_eq {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (p : Sp E) :
    (spMap (epsEv (R := R) e : DualNumber E →+* E)).base p =
      (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p := by
  apply PrimeSpectrum.ext
  ext u
  have hc : ptAlg (R := R) (D := DualNumber R) (E := E) e DualNumber.eps ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, ← map_mul, DualNumber.eps_mul_eps, map_zero]; exact p.asIdeal.zero_mem)
  change epsEv (R := R) e u ∈ p.asIdeal ↔ u.fst ∈ p.asIdeal
  rw [epsGen_epsEv_apply]
  constructor
  · intro h
    have := p.asIdeal.sub_mem h (p.asIdeal.mul_mem_left u.snd hc)
    simpa using this
  · intro h
    exact p.asIdeal.add_mem h (p.asIdeal.mul_mem_left u.snd hc)

theorem epsGen_mem {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) {Y : Scheme.{0}}
    (y : Sp (DualNumber E) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (spMap (epsEv (R := R) e : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U) :
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (Set.mem_univ p)
  change y.base ((spMap (epsEv (R := R) e : DualNumber E →+* E)).base p) ∈ U at this
  change y.base ((spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p) ∈ U
  rwa [← epsGen_spMap_eq (R := R) e p]

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem epsGen_red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV (R := R) (D := E) v x =
      x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = (1 : SpAlg R R ⟶ B) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, spOver_left]
    refine hv.trans ?_
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    change η[B].left = spMap (RingHom.id R) ≫ η[B].left
    rw [Cris.spMap_id, Category.id_comp]
  rw [AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      ext a
      simp
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', MonObj.comp_one]

theorem epsGen_key (v : epsR R ⟶ B) {E : Type} [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) :
    z ≫ lift (fst A (epsR R)) (snd A (epsR R) ≫ v) =
      spOver (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp
        (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      simp [epsEv]
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (R := R) (E := E) (z ≫ snd A (epsR R))).comp (EpsWeil.epsMap R E) =
        ptAlg (R := R) (D := DualNumber R) (E := E) (z ≫ snd A (epsR R)) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap, epsEv]
    rw [this, spOver_ptAlg, Category.assoc]

theorem exists_isPtGen_of_isEpsGen : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v →
    ∀ T, IsEpsGen (R := R) (A := A) P v T →
    ∃ t, IsPtGen (R := R) P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  intro R _ A B _ _ P _ v hv T hT
  obtain ⟨T1, T2, T3⟩ := hT
  have memV : ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
      ⊤ ≤ (ptV (R := R) (D := E) v x).left ⁻¹ᵁ P.U i := by
    intro E _ _ x i h
    apply dualNumberPoint_preimage_top_of_reduction _ E (ptV (R := R) (D := E) v x).left (P.U i)
    have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
    rw [← epsGen_red_ptV (R := R) (E := E) hv x] at h1
    exact h1
  have memA : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) (i : P.ι),
      ⊤ ≤ (z ≫ CartesianMonoidalCategory.lift (fst A (epsR R)) (snd A (epsR R) ≫ v)).left ⁻¹ᵁ P.U i →
      ⊤ ≤ (z ≫ fst _ _).left ⁻¹ᵁ chartsA P i := by
    intro E _ _ z i h
    rw [epsGen_key (R := R) (E := E) v z, Over.comp_left, spOver_left] at h
    have h2 := epsGen_mem (R := R) (E := E) (z ≫ snd A (epsR R)) _ _ h
    have h3 : ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫
        ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ P.U i := h2
    rw [epsGen_red_ptV hv] at h3
    exact h3
  refine ⟨fun E _ _ z i ↦ epsEv (R := R) (E := E) (z ≫ snd A (epsR R))
    (T E (z ≫ fst A (epsR R)) i), ?_, ?_, ?_⟩
  · intro E _ _ z i h
    exact (T1 E (z ≫ fst _ _) i (memA E z i h)).map _
  · intro E _ _ E' _ _ ψ z i h
    have h' := memA E z i h
    simp only [Category.assoc]
    rw [T2 E E' ψ (z ≫ fst A (epsR R)) i h', epsGen_epsEv_nat]
  · intro E _ _ z i j hi hj
    have hi' := memA E z i hi
    have hj' := memA E z j hj
    have hij : ⊤ ≤ (ptV (R := R) (D := E) v (z ≫ fst A (epsR R))).left ⁻¹ᵁ (P.U i ⊓ P.U j) :=
      fun p hp ↦ ⟨memV E _ i hi' hp, memV E _ j hj' hp⟩
    simp only
    rw [T3 E (z ≫ fst A (epsR R)) i j hi' hj', map_mul, epsGen_key (R := R) (E := E) v z,
      Over.comp_left, spOver_left, evalSectionAtPointOrZero_specMap_comp _ _ E
        (epsEv (R := R) (E := E) (z ≫ snd A (epsR R)) : DualNumber E →+* E) _ _ _ hij]
    rfl

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGeStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ T, IsEpsGen P v T → ∃ t, IsPtGen P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  first | exact @GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | exact GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen | (intros; apply GlobalTheory.PtExt.exists_isPtGen_of_isEpsGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivial
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem nonempty_ι_of_isLB (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (hP : P.IsLB) : Nonempty P.ι := by
  have hne : Nonempty (𝟙_ (Over (Sp R))).left := inferInstanceAs (Nonempty (PrimeSpectrum R))
  obtain ⟨p⟩ := hne
  let e : 𝟙_ (Over (Sp R)) ⟶ A ⊗ B := lift η[A] η[B]
  have h : e.left.base p ∈ (⨆ i, P.U i) := by rw [hP.cover]; trivial
  obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨i⟩

theorem exists_isChoice : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  intro R _ _ A B _ _ P hP
  have hne := nonempty_ι_of_isLB R A B P hP
  classical
  refine ⟨fun D _ _ x ↦ if h : Sm (chartsA P) x then
    Classical.choose (show ∃ i, ⊤ ≤ x.left ⁻¹ᵁ chartsA P i from h)
  else Classical.choice hne, ?_⟩
  unfold IsChoice
  intro D _ _ x h
  simp only [dite_eq_left h]
  exact Classical.choose_spec (show ∃ i, ⊤ ≤ x.left ⁻¹ᵁ chartsA P i from h)

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsChartChoiceForPointsOfNontrivialStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial : ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∃ j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι, IsChoice P j := by
  first | exact @GlobalTheory.PtExt.exists_isChoice | exact GlobalTheory.PtExt.exists_isChoice | (intros; apply GlobalTheory.PtExt.exists_isChoice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairing
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareKer

theorem mem_fil_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ y : HdR B, (∀ x ∈ Fil A, φ x y = 0) → y ∈ Fil B := by
  intro hH R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ y hy
  have hL := hP.isLB

  obtain ⟨v, hv, -⟩ := ((GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hH).2.1 R B g hB hgB).1.1 y

  have horth := GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hH R A B g hA hB hgA hgB P hL φ hφ
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial R A B P hL

  have hpairZero (h : HdR A) (hh : h ∈ Fil A) : φ h y = h (0 : primDR A) :=
    (hy h hh).trans h.map_zero.symm
  have hc : Cohom (chartsA P) (fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))) (tanCoc P j v).neg :=
    GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal hH R A B g hA hB hgA hgB P hL φ hφ horth y v hv 0
      hpairZero 0 (by rw [LinearMap.map_zero]; rfl) j hj
  obtain ⟨k, hk⟩ := hc
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    have h0 : fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) D D' ψ x = 0 := rfl
    simp only [Fn1.add, Fn1.neg, h0, zero_add, neg_neg] at e
    exact e

  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback R (A ⊗ B) A P hL (AbDual.inl A B) hP.zero_right

  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary R A B P hL v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hL v hv.1 T hT
  have htriv := GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator R (A ⊗ B) (A ⊗ epsR R) P hL _ t ht

  have hv1 : v = 1 := hP.ker_right (epsR R) v htriv
  subst hv1
  exact isLieImage_one_iff.mp hv

end GlobalTheory.PoincareKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOfOrthogonalPerfectPairingStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hodgeFiltration_of_orthogonal_perfectPairing : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ y : HdR B, (∀ x ∈ Fil A, φ x y = 0) → y ∈ Fil B := by
  first | exact @GlobalTheory.PoincareKer.mem_fil_of_orth | exact GlobalTheory.PoincareKer.mem_fil_of_orth | (intros; apply GlobalTheory.PoincareKer.mem_fil_of_orth <;> assumption)
end
