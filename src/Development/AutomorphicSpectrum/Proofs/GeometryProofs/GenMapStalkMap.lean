module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerRingInjective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtDom

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

theorem map_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
  have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
    Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  exact h1.trans (congrArg ξ h2)

theorem genMap_stalkMap {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (q : X') (hq : genPt ξ' ⤳ q) (hp : genPt ξ ⤳ f q)
    (s : X.presheaf.stalk (f q)) :
    genMap ξ' ⟨q, hq⟩ ((f.stalkMap q).hom s) = i (genMap ξ ⟨f q, hp⟩ s) := by
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact congrArg (fun g => g.hom s) e

theorem regAt_dominates :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type)
      [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), Dominates ξ' ξ f i →
      ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        (IsCptGen ξ' → ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, fun hg => ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := genMap_stalkMap hd q hq hp s
    have hone : (f.stalkMap q).hom s * t = 1 := by
      apply hg.inj ⟨q, hq⟩
      rw [map_mul, map_one, hv, ht]
      exact mul_inv_cancel₀ h0
    have hu : IsUnit ((f.stalkMap q).hom s) := IsUnit.of_mul_eq_one _ hone
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

end GlobalTheory.CompanionTheory.Ar.RegAtDom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValues
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem section_eq_zero_of_val_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 :=
  PositivityTheory.HtPt.Unc.sec_inj

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_eq_zero_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 :=
  @GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open AlgebraicGeometry CategoryTheory
open GlobalTheory.CompanionTheory.Ar.SncBase

def SncPts {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : ℕ)
    (B : Set (Cpt ξ)) : Prop :=
  ∀ p, Char0 ξ p → ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)

end GlobalTheory.CompanionTheory.Ar.GeoModel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {E : Type} [AddCommGroup E] [Module Ω E]

section Units

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}

theorem unitAt.zpow {u : Ω} (hu : unitAt ξ p u) (n : ℤ) : unitAt ξ p (u ^ n) := by
  obtain ⟨h0, h1, h2⟩ := hu
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_natCast]; exact pow_mem h1 n
    · rw [zpow_natCast, ← inv_pow]; exact pow_mem h2 n
  · refine ⟨zpow_ne_zero _ h0, ?_, ?_⟩
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem h2 n
    · rw [zpow_neg, zpow_natCast, inv_inv]; exact pow_mem h1 n

theorem unitAt.prod {K : Type} (s : Finset K) {u : K → Ω} (hu : ∀ k ∈ s, unitAt ξ p (u k)) :
    unitAt ξ p (∏ k ∈ s, u k) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k hk => (hu k hk).1, prod_mem fun k hk => (hu k hk).2.1, ?_⟩
  rw [← Finset.prod_inv_distrib]
  exact prod_mem fun k hk => (hu k hk).2.2

theorem span_singleton_eq_of_unitAt {u : Ω} (hu : unitAt ξ p u) {e e' : E} (h : e' = u • e) :
    Submodule.span (regAt ξ p) {e'} = Submodule.span (regAt ξ p) {e} := by
  obtain ⟨h0, h1, h2⟩ := hu
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨u, h1⟩, h.symm⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    refine ⟨⟨u⁻¹, h2⟩, ?_⟩
    show u⁻¹ • e' = e
    rw [h, smul_smul, inv_mul_cancel₀ h0, one_smul]

end Units

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

end Lat

section Pull

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}

theorem Dominates.map_genPt (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  let pt' : Spec (CommRingCat.of Ω') := IsLocalRing.closedPoint Ω'
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  have h1 : (ξ' ≫ f) pt' = (Spec.map (CommRingCat.ofHom i) ≫ ξ) pt' :=
    congrArg (fun g : Spec (CommRingCat.of Ω') ⟶ X => g pt') h
  have h2 : (Spec.map (CommRingCat.ofHom i)) pt' = pt :=
    (inferInstance : Subsingleton (PrimeSpectrum Ω)).elim _ _
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2] at h1
  exact h1

theorem Dominates.specializes (h : Dominates ξ' ξ f i) (p' : Cpt ξ') : genPt ξ ⤳ f p'.1 := by
  rw [← h.map_genPt]
  exact p'.2.map f.continuous

theorem Lat.pull_apply {F : Type} [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (h : Dominates ξ' ξ f i)
    (j : E →+ F) (p' : Cpt ξ') :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, h.specializes p'⟩ : Set E)) := by
  show Submodule.span _ _ = _
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨h.specializes p', e, he, rfl⟩

end Pull

namespace Lat

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

section Multi

variable {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω}

theorem block_ratio_mem {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h2 := h.2 (Function.update c k i)
  have e1 : ∏ k', y ⟨k', c k'⟩ = y ⟨k, c k⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
    (Finset.mul_prod_erase _ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)).symm
  have e2 : ∏ k', y ⟨k', Function.update c k i k'⟩ = y ⟨k, i⟩ * ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ := by
    rw [← Finset.mul_prod_erase _ (fun k' => y ⟨k', Function.update c k i k'⟩) (Finset.mem_univ k)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun k' hk' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
  have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 := by
    intro h0
    exact h.1 (by show ∏ k', y ⟨k', c k'⟩ = 0; rw [e1, h0, mul_zero])
  simp only [e1, e2] at h2
  rwa [mul_div_mul_right _ _ hP] at h2

theorem block_coord_ne_zero {p : Cpt ξ} {c : (k : K) → ι k}
    (h : InChart ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h.1 k (Finset.mem_univ k)

end Multi

section Single

variable {κ : Type} {x : κ → Ω}

end Single

end Lat

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSection
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem regularAt_forall_iff_exists_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t :=
  PositivityTheory.HtPt.Unc.reg_iff

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.regularAt_forall_iff_exists_section
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenLeClosedFibre
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenLeClosedFibre
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isFinite_open_le_of_closedFibre_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' :=
  @PositivityTheory.HtPt.Unc.finite_le

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenLeClosedFibreStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_open_le_closed_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le | exact GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_of_finite_of_closedFibre {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI := hY
  haveI : IsIso (⊤ : Y.left.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hfin : IsFinite ((⊤ : Y.left.Opens).ι ≫ Y.hom) := inferInstance
  have hle := GlobalTheory.T.finite_open_le_closed_fibre R Y.left Y.hom ⊤ (h.left ⁻¹ᵁ W) hfin (fun x hx => by
    apply hW
    have hw : h.left ≫ X.hom = Y.hom := Over.w h
    have hc := Scheme.Hom.comp_apply h.left X.hom x
    rw [hw] at hc
    rw [← hc]
    exact hx)
  exact hle (show z ∈ (⊤ : Y.left.Opens) from trivial)

abbrev openOver {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

abbrev openIncl {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : openOver X U ⟶ X := Over.homMk U.ι rfl

theorem exists_factor_openIncl {S : Scheme.{0}} {X Y : Over S} (U : X.left.Opens) (x : Y ⟶ X)
    (hx : ∀ z, x.left z ∈ U) : ∃ x' : Y ⟶ openOver X U, x' ≫ openIncl X U = x := by
  have hr : Set.range x.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hx z
  have hc : IsOpenImmersion.lift U.ι x.left hr ≫ U.ι = x.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι x.left hr) ?_, ?_⟩
  · simp only [Over.mk_hom]
    rw [← Category.assoc, hc]
    exact Over.w x
  · ext1
    exact hc

theorem QFGroup.isFinOpenSub_of_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
      (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) →
      (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite_of_closedFibre U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite_of_closedFibre U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite_of_closedFibre U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFiniteStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinOpenSub_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOnDualAndBidual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LatDual

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem mem_span_basis_iff (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E) (e : E) :
    e ∈ Submodule.span (regAt ξ p) (Set.range B) ↔ ∀ i, B.repr e i ∈ regAt ξ p := by
  constructor
  · intro he
    let N : Submodule (regAt ξ p) E :=
      { carrier := {x | ∀ i, B.repr x i ∈ regAt ξ p}
        add_mem' := fun ha hb i => by simpa using add_mem (ha i) (hb i)
        zero_mem' := fun i => by simp
        smul_mem' := fun c x hx i => by
          show B.repr ((c : Ω) • x) i ∈ regAt ξ p
          simpa using mul_mem c.2 (hx i) }
    have hle : Submodule.span (regAt ξ p) (Set.range B) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ∀ i, B.repr (B j) i ∈ regAt ξ p
      intro i
      rw [B.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact hle he
  · intro h
    rw [← B.sum_repr e]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : B.repr e i • B i = (⟨B.repr e i, h i⟩ : regAt ξ p) • B i := rfl
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_dual_iff (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (b : Fin r → E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range b)) (w : Module.Dual Ω E) :
    w ∈ L.dual p ↔ ∀ i, w (b i) ∈ regAt ξ p := by
  show (∀ e ∈ L p, w e ∈ regAt ξ p) ↔ _
  rw [h]
  constructor
  · intro hw i
    exact hw _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hw
    let N : Submodule (regAt ξ p) E :=
      { carrier := {x | w x ∈ regAt ξ p}
        add_mem' := fun {a c} ha hc => by
          show w (a + c) ∈ regAt ξ p
          rw [map_add (f := _)]
          exact add_mem ha hc
        zero_mem' := by
          show w 0 ∈ regAt ξ p
          simp
        smul_mem' := fun c x hx => by
          show w ((c : Ω) • x) ∈ regAt ξ p
          rw [map_smul, smul_eq_mul]
          exact mul_mem c.2 hx }
    have hle : Submodule.span (regAt ξ p) (Set.range b) ≤ N := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hw i
    intro e he
    exact hle he

theorem dual_eq_span (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range B)) :
    L.dual p = Submodule.span (regAt ξ p) (Set.range B.dualBasis) := by
  ext w
  rw [mem_dual_iff L p B h w, mem_span_basis_iff p B.dualBasis w]
  simp only [Module.Basis.dualBasis_repr]

end GlobalTheory.CompanionTheory.Ar.LatDual

namespace GlobalTheory.CompanionTheory.Ar

open LatDual

theorem Lat.isVBOn_dual_and_bidual :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ), L.IsVBOn T r ⊤ → L.dual.IsVBOn T r ⊤ ∧ ∀ p ∈ T, ∀ e : E, e ∈ L p ↔ ∀ w ∈ L.dual p, w e ∈ regAt ξ p := by
  intro X Ω _ ξ E _ _ L T r hL
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, -⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    refine ⟨U, hpU, ⇑B.dualBasis, B.dualBasis.span_eq, ?_⟩
    intro q hq hqU
    obtain ⟨-, hLq⟩ := hfr q hq hqU
    refine And.intro B.dualBasis.linearIndependent ?_
    exact LatDual.dual_eq_span L q B (by rw [hB]; exact hLq)
  · intro p hp e
    obtain ⟨U, hpU, b, hspan, hfr⟩ := hL p hp
    obtain ⟨hli, hLp0⟩ := hfr p hp hpU
    obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin r) Ω E, ⇑B = b :=
      ⟨Module.Basis.mk hli hspan.ge, Module.Basis.coe_mk hli _⟩
    have hLp : L p = Submodule.span (regAt ξ p) (Set.range B) := by rw [hB]; exact hLp0
    constructor
    · intro he w hw
      exact hw e he
    · intro h
      rw [hLp, LatDual.mem_span_basis_iff p B e]
      intro i
      have hmem : B.dualBasis i ∈ L.dual p := by
        rw [LatDual.dual_eq_span L p B hLp]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hi := h _ hmem
      rwa [Module.Basis.dualBasis_apply] at hi

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEqSpanOfIsFrameAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.wedge_eq_span_of_isFrameAt :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p →
      L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} := by
  intro X Ω _ ξ E _ _ L r b p h
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨v, hv, rfl⟩
    have hc : ∀ i, ∃ c : Fin r → regAt ξ p, ∑ j, c j • b j = v i := fun i => by
      have := hv i
      rw [h.2] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using hc
    have hv' : v = fun i => ∑ j, ((c i j : Ω)) • b j := by
      funext i
      rw [← hc i]
      rfl
    have hsum : exteriorPower.ιMulti Ω r v =
        ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
      rw [hv']
      have := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
        (fun i j => ((c i j : Ω)) • b j)
      refine this.trans (Finset.sum_congr rfl fun f _ => ?_)
      have h2 := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
        (fun i => (c i (f i) : Ω)) (fun i => b (f i))
      simp only [RingHom.id_apply] at h2
      refine h2.trans ?_
      have h3 : ((∏ i, c i (f i) : regAt ξ p) : Ω) = ∏ i, (c i (f i) : Ω) := by simp
      rw [← h3]
      rfl
    rw [SetLike.mem_coe, hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h4 := (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, h4]
      have hm := Submodule.mem_span_singleton_self (R := regAt ξ p) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  · refine Submodule.span_mono ?_
    rintro w rfl
    refine ⟨b, fun i => ?_, rfl⟩
    rw [h.2]
    exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSection
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

variable {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
  {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
  [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem ext_pair_mod {Z : Over S} (f g : ob x (P × P) ⟶ Z)
    (h₁ : hom x (LinearMap.fst R P P) ≫ f = hom x (LinearMap.fst R P P) ≫ g)
    (h₂ : hom x (LinearMap.snd R P P) ≫ f = hom x (LinearMap.snd R P P) ≫ g) : f = g := by
  ext1
  refine joint_epi (TrivSqZeroExt.map (LinearMap.fst R P P)).toRingHom
    (TrivSqZeroExt.map (LinearMap.snd R P P)).toRingHom ?_ ?_ f.left g.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)
  · intro a b hab
    have e₁ : TrivSqZeroExt.map (LinearMap.fst R P P) a = TrivSqZeroExt.map (LinearMap.fst R P P) b :=
      congrArg Prod.fst hab
    have e₂ : TrivSqZeroExt.map (LinearMap.snd R P P) a = TrivSqZeroExt.map (LinearMap.snd R P P) b :=
      congrArg Prod.snd hab
    ext
    · simpa using congrArg TrivSqZeroExt.fst e₁
    · simpa using congrArg TrivSqZeroExt.snd e₁
    · simpa using congrArg TrivSqZeroExt.snd e₂
  · intro p
    let q : PrimeSpectrum (TrivSqZeroExt R P) :=
      PrimeSpectrum.comap (TrivSqZeroExt.map (LinearMap.inl R P P)).toRingHom p
    refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
    change TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) ∈ p.asIdeal ↔
      a ∈ p.asIdeal
    set b := TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) with hb
    have h0 : (b - a).fst = 0 := by simp [hb]
    have hm : b - a ∈ p.asIdeal := by
      refine p.isPrime.mem_of_pow_mem 2 ?_
      have : (b - a) ^ 2 = 0 := by
        rw [pow_two]
        ext1 <;> simp [h0]
      rw [this]; exact zero_mem _
    constructor
    · intro h; simpa using p.asIdeal.sub_mem h hm
    · intro h; simpa using p.asIdeal.add_mem hm h

theorem hom_add_mod (G : Over S) [GrpObj G] (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  have h0 : hom x (0 : P →ₗ[R] P) ≫ u = 1 := by
    rw [hom_zero, Category.assoc, hu, MonObj.comp_one]
  have key : hom x (LinearMap.inl R P P + LinearMap.inr R P P) ≫ u =
      (hom x (LinearMap.inl R P P) ≫ u) * (hom x (LinearMap.inr R P P) ≫ u) := by
    apply ext_pair_mod
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, add_zero, h0, _root_.mul_one]
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.snd_comp_inl,
        LinearMap.snd_comp_inr, zero_add, h0, _root_.one_mul]
  have := congrArg (fun k => hom x (f.coprod g) ≫ k) key
  simpa only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.coprod_inl,
    LinearMap.coprod_inr] using this

theorem hom_add_mod_closed : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  fun _ _ _ x G _ _ _ _ _ _ _ _ _ _ _ u hu f g => hom_add_mod x G u hu f g

end GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomAddMulOfUnitSectionStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_add_mul_of_unit_section : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | exact GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed | (intros; apply GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc.hom_add_mod_closed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_scalar {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (π : X ⟶ Spec (CommRingCat.of A))
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : A →+* B) (hw : x ≫ π = Spec.map (CommRingCat.ofHom φ))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (hU : U ≤ π ⁻¹ᵁ ⊤) (b : A) :
    valAt x U h (π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) = φ b := by
  have h1 := Scheme.Hom.appLE_comp_appLE x π ⊤ U ⊤ hU h
  have h0 : ∀ (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) (e : ⊤ ≤ q ⁻¹ᵁ ⊤),
      q = Spec.map (CommRingCat.ofHom φ) →
      q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rintro q e rfl
    have : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [this]
    exact Scheme.ΓSpecIso_naturality _
  have h2 : (π.appLE ⊤ U hU ≫ x.appLE U ⊤ h) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1]
    exact h0 _ _ hw
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)) h2
  simpa [valAt] using h3

theorem QFGroup.regularAt_scalar_mul (Γ : QFGroup R T) {f : T → FractionRing R} {g : Γ.G.left} (b : R)
    (H : Γ.RegularAt f g) : Γ.RegularAt (fun t => algebraMap R (FractionRing R) b * f t) g := by
  obtain ⟨U, hg, s, hs⟩ := H
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have hU : U ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨U, hg, π.appLE ⊤ U hU ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) * s, fun t h => ?_⟩
  have hw : (Γ.pt t).left ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    rw [hπ]; exact Over.w (Γ.pt t)
  have h1 := valAt_scalar π (Γ.pt t).left (algebraMap R (FractionRing R)) hw U h hU b
  have h2 := hs t h
  show _ = algebraMap R (FractionRing R) b * f t
  rw [← h1, ← h2]
  simp [valAt, map_mul]

theorem QFGroup.compactSpace (Γ : QFGroup R T) : CompactSpace Γ.G.left := by
  obtain ⟨π, hπ⟩ : ∃ π : Γ.G.left ⟶ Spec (CommRingCat.of R), π = Γ.G.hom := ⟨_, rfl⟩
  have : QuasiCompact π := hπ ▸ Γ.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace π

theorem QFGroup.exists_denom [Finite T] (Γ : QFGroup R T) (f : T → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∀ g, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g := by
  classical
  have := Γ.compactSpace
  have key : ∀ g : Γ.G.left, ∃ d : R, d ≠ 0 ∧ ∃ U : Γ.G.left.Opens, g ∈ U ∧
      ∀ g' ∈ U, Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g' := by
    intro g
    have hreg : ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R (FractionRing R) d * f t) g :=
      RegDenom.exists_denom_regularAt R T Γ f g
    obtain ⟨d, hd, U, hg, s, hs⟩ := hreg
    exact ⟨d, hd, U, hg, fun g' hg' => ⟨U, hg', s, hs⟩⟩
  choose d hd U hgU hU using key
  obtain ⟨F, hF⟩ := CompactSpace.elim_nhds_subcover (fun g => (U g : Set Γ.G.left))
    (fun g => (U g).isOpen.mem_nhds (hgU g))
  refine ⟨∏ x ∈ F, d x, Finset.prod_ne_zero_iff.2 fun x _ => hd x, fun g => ?_⟩
  have hg : g ∈ ⋃ x ∈ F, (U x : Set Γ.G.left) := by rw [hF]; trivial
  simp only [Set.mem_iUnion] at hg
  obtain ⟨x, hx, hgx⟩ := hg
  have h1 := Γ.regularAt_scalar_mul (∏ y ∈ F.erase x, d y) (hU x g hgx)
  have h2 : (∏ y ∈ F, d y) = (∏ y ∈ F.erase x, d y) * d x := (Finset.prod_erase_mul F d hx).symm
  rw [h2]
  simpa [map_mul, _root_.mul_assoc] using h1

end GlobalTheory.CompanionTheory.Ar.BT


open Classical in
theorem GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T), ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
  classical
  intro R _ _ T _ _ Γ
  have := Fintype.ofFinite T
  let δ : T → T → R := fun s h => if h = s then 1 else 0
  choose e he hreg using fun s : T =>
    Γ.exists_denom (fun h => algebraMap R (FractionRing R) (δ s h))
  have hmem : ∀ s, (∏ x, e x) • δ s ∈ Γ.btOrder ⊤ := by
    intro s
    refine Algebra.subset_adjoin ?_
    intro t g _
    have h1 := Γ.regularAt_scalar_mul (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) (hreg (t⁻¹ * s) g)
    have h2 : (∏ y, e y) = (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) * e (t⁻¹ * s) :=
      (Finset.prod_erase_mul _ e (Finset.mem_univ _)).symm
    have h3 : (fun h => algebraMap R (FractionRing R) (((∏ x, e x) • δ s) (t * h))) =
        fun h => algebraMap R (FractionRing R) (∏ y ∈ Finset.univ.erase (t⁻¹ * s), e y) *
          (algebraMap R (FractionRing R) (e (t⁻¹ * s)) *
            algebraMap R (FractionRing R) (δ (t⁻¹ * s) h)) := by
      funext h
      have h4 : δ s (t * h) = δ (t⁻¹ * s) h := by
        have : t * h = s ↔ h = t⁻¹ * s := by
          constructor
          · rintro rfl; simp
          · rintro rfl; simp
        simp [δ, this]
      rw [Pi.smul_apply, h4, h2, smul_eq_mul, map_mul, map_mul, _root_.mul_assoc]
    rw [h3]
    exact h1
  refine ⟨∏ x, e x, Finset.prod_ne_zero_iff.2 fun x _ => he x, fun f => ?_⟩
  have hf : (∏ x, e x) • f = ∑ s, f s • ((∏ x, e x) • δ s) := by
    funext h
    simp [δ, Finset.sum_apply, _root_.mul_comm]
  rw [hf]
  exact Subalgebra.sum_mem _ fun s _ => Subalgebra.smul_mem _ (hmem s) _
end
