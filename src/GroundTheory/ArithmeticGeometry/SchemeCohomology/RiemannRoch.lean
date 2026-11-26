module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor
public import GroundTheory.FunctionField.ExistsBoundDegSubFinrankL
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleDual
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField

@[expose] public section

section -- merged from GroundTheory.FunctionField.WeilDifferential
namespace GroundTheory.FunctionField

open Module Repartition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

namespace Divisor

theorem A_sup_le (D E : Divisor k K) : A (D ⊔ E) ≤ A D ⊔ A E := by
  classical
  intro a ha
  let f : Place k K → K := fun v => if E v ≤ D v then a v else 0
  have hf : {v : Place k K | f v ∉ v.ring}.Finite :=
    a.finite_not_mem.subset fun v (hv : f v ∉ v.ring) => by
      show a v ∉ v.ring
      intro h
      apply hv
      simp only [f]
      split_ifs
      · exact h
      · exact v.ring.zero_mem
  let b := Repartition.mk f hf
  have hb : b ∈ A D := by
    intro v
    change v.valuation (f v) ≤ _
    simp only [f]
    split_ifs with h
    · have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_left h] at this
    · rw [map_zero]; exact zero_le
  have hc : a - b ∈ A E := by
    intro v
    rw [Repartition.sub_apply]
    change v.valuation (a v - f v) ≤ _
    simp only [f]
    split_ifs with h
    · rw [sub_self, map_zero]; exact zero_le
    · rw [sub_zero]
      have := ha v
      rwa [Finsupp.sup_apply, sup_of_le_right (not_le.1 h).le] at this
  have : a = b + (a - b) := by abel
  rw [this]
  exact Submodule.add_mem_sup hb hc

noncomputable def weilSpace (D : Divisor k K) : Submodule k (Module.Dual k (Repartition k K)) :=
  (A D ⊔ principal k K).dualAnnihilator

theorem mem_weilSpace {D : Divisor k K} {ω : Module.Dual k (Repartition k K)} :
    ω ∈ weilSpace D ↔ (∀ a ∈ A D, ω a = 0) ∧ ∀ x : K, ω (diag x) = 0 := by
  rw [weilSpace, Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Submodule.mem_sup_left ha),
      fun x => h _ (Submodule.mem_sup_right (diag_mem_principal x))⟩
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨b, hb, c, ⟨x, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
    rw [map_add (f := _), h1 b hb, h2 x, add_zero]

theorem weilSpace_anti {D E : Divisor k K} (h : D ≤ E) : weilSpace E ≤ weilSpace D :=
  Submodule.dualAnnihilator_anti (sup_le_sup_right (A_mono h) _)

theorem weilSpace_sup {D E : Divisor k K} {ω : Module.Dual k (Repartition k K)}
    (hD : ω ∈ weilSpace D) (hE : ω ∈ weilSpace E) : ω ∈ weilSpace (D ⊔ E) := by
  rw [mem_weilSpace] at hD hE ⊢
  refine ⟨fun a ha => ?_, hD.2⟩
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 (A_sup_le D E ha)
  rw [map_add (f := _), hD.1 b hb, hE.1 c hc, add_zero]

theorem finrank_weilSpace (D : Divisor k K) : finrank k (weilSpace D) = indexOfSpeciality D := by
  change finrank k (A D ⊔ principal k K).dualAnnihilator = _
  rw [indexOfSpeciality,
    ← (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).finrank_eq,
    Subspace.dual_finrank_eq]

theorem exists_indexOfSpeciality_eq_zero :
    ∃ c : ℤ, ∀ D : Divisor k K, c ≤ deg D → indexOfSpeciality D = 0 := by
  obtain ⟨E₀, hE₀⟩ := exists_eq_genusInt (k := k) (K := K)
  refine ⟨deg E₀ + genusInt k K, fun D hD => ?_⟩
  have h1 := le_genusInt (D - E₀)
  rw [map_sub] at h1
  have hpos : 0 < finrank k (L (D - E₀)) := by
    have : (0 : ℤ) < finrank k (L (D - E₀)) := by linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0 : (z : K) ≠ 0 := fun h => hz (Subtype.ext h)
  have hzL := (mem_L_iff_le hz0).1 z.2
  have hle : E₀ ≤ D + divisor (z : K) := by
    rw [← sub_nonneg]
    convert hzL using 1
    abel
  have hD' := eq_genusInt_of_le hE₀ hle
  rw [finrank_L_add_divisor D hz0, map_add (f := _), deg_divisor, add_zero] at hD'
  have hi := indexOfSpeciality_eq_genusInt D
  have : (indexOfSpeciality D : ℤ) = 0 := by linarith
  exact_mod_cast this

theorem exists_indexOfSpeciality_pos : ∃ D : Divisor k K, 0 < indexOfSpeciality D := by
  obtain ⟨P⟩ := Place.nonempty (k := k) (K := K)
  set N : ℕ := (2 - genusInt k K).toNat with hN
  refine ⟨-(N • Finsupp.single P 1), ?_⟩
  have h := indexOfSpeciality_eq_genusInt (-(N • Finsupp.single P 1) : Divisor k K)
  have hdeg : deg (-(N • Finsupp.single P 1) : Divisor k K) = -(N * P.deg) := by
    rw [map_neg, map_nsmul, deg_single, nsmul_eq_mul, one_mul]
  have hP : (1 : ℤ) ≤ P.deg := by exact_mod_cast P.deg_pos
  have hN' : (2 : ℤ) - genusInt k K ≤ N := Int.self_le_toNat _
  have hl : (0 : ℤ) ≤ finrank k (L (-(N • Finsupp.single P 1) : Divisor k K)) := Nat.cast_nonneg _
  have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg _
  have : (1 : ℤ) ≤ indexOfSpeciality (-(N • Finsupp.single P 1) : Divisor k K) := by
    rw [h, hdeg]
    nlinarith
  exact_mod_cast this

end Divisor

open Divisor


variable (k K) in
def weilDifferentials : Submodule k (Module.Dual k (Repartition k K)) where
  carrier := {ω | ∃ D : Divisor k K, ω ∈ weilSpace D}
  add_mem' := by
    rintro ω₁ ω₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    exact ⟨D₁ ⊓ D₂, add_mem (weilSpace_anti inf_le_left h₁) (weilSpace_anti inf_le_right h₂)⟩
  zero_mem' := ⟨0, zero_mem _⟩
  smul_mem' := by
    rintro c ω ⟨D, h⟩
    exact ⟨D, Submodule.smul_mem _ c h⟩


variable (k K) in
def WeilDifferential : Type _ := weilDifferentials k K

namespace WeilDifferential

instance : AddCommGroup (WeilDifferential k K) :=
  inferInstanceAs (AddCommGroup (weilDifferentials k K))

instance : Module k (WeilDifferential k K) := inferInstanceAs (Module k (weilDifferentials k K))

def toDual : WeilDifferential k K →ₗ[k] Module.Dual k (Repartition k K) :=
  (weilDifferentials k K).subtype

theorem toDual_injective : Function.Injective (toDual (k := k) (K := K)) :=
  Subtype.val_injective

def mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    WeilDifferential k K :=
  (⟨ω, h⟩ : weilDifferentials k K)

@[simp]
theorem toDual_mk (ω : Module.Dual k (Repartition k K)) (h : ∃ D : Divisor k K, ω ∈ weilSpace D) :
    toDual (mk ω h) = ω :=
  rfl

theorem exists_mem (ω : WeilDifferential k K) : ∃ D : Divisor k K, toDual ω ∈ weilSpace D :=
  (show weilDifferentials k K from ω).2

theorem exists_ne_zero : ∃ ω : WeilDifferential k K, ω ≠ 0 := by
  obtain ⟨D, hD⟩ := exists_indexOfSpeciality_pos (k := k) (K := K)
  rw [← finrank_weilSpace] at hD
  have hne : weilSpace D ≠ ⊥ := by
    intro h
    rw [h] at hD
    simp at hD
  obtain ⟨φ, hφmem, hφ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨mk φ ⟨D, hφmem⟩, fun h => hφ ?_⟩
  have := congrArg toDual h
  rwa [toDual_mk, map_zero] at this

noncomputable def toQuotDual (D : Divisor k K) :
    weilSpace D ≃ₗ[k] Module.Dual k (Repartition k K ⧸ (A D ⊔ principal k K)) :=
  (Submodule.dualQuotEquivDualAnnihilator (A D ⊔ principal k K)).symm

theorem exists_deg_lt {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ c : ℤ, ∀ D : Divisor k K, toDual ω ∈ weilSpace D → deg D < c := by
  obtain ⟨c, hc⟩ := exists_indexOfSpeciality_eq_zero (k := k) (K := K)
  refine ⟨c, fun D hD => ?_⟩
  by_contra hle
  push Not at hle
  have h0 : finrank k (Repartition k K ⧸ (A D ⊔ principal k K)) = 0 := hc D hle
  have hsub : Subsingleton (Repartition k K ⧸ (A D ⊔ principal k K)) :=
    Module.finrank_zero_iff.1 h0
  have h1 : toQuotDual D ⟨toDual ω, hD⟩ = 0 :=
    LinearMap.ext fun q => by simp [Subsingleton.elim q 0]
  have h2 : (⟨toDual ω, hD⟩ : weilSpace D) = 0 :=
    (toQuotDual D).injective (by rw [h1, map_zero])
  exact hω (toDual_injective (by rw [map_zero]; exact congrArg Subtype.val h2))

theorem exists_divisor {ω : WeilDifferential k K} (hω : ω ≠ 0) :
    ∃ W : Divisor k K, ∀ D : Divisor k K, toDual ω ∈ weilSpace D ↔ D ≤ W := by
  classical
  obtain ⟨c, hc⟩ := exists_deg_lt hω
  obtain ⟨D₀, hD₀⟩ := ω.exists_mem
  obtain ⟨n, ⟨W, hW, rfl⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd (P := fun n => ∃ D, toDual ω ∈ weilSpace D ∧ deg D = n)
      ⟨c, fun n ⟨D, hD, hn⟩ => hn ▸ (hc D hD).le⟩ ⟨deg D₀, D₀, hD₀, rfl⟩
  refine ⟨W, fun D => ⟨fun hD => ?_, fun h => weilSpace_anti h hW⟩⟩
  have hsup := weilSpace_sup hD hW
  have h1 := hmax _ ⟨_, hsup, rfl⟩
  have h2 : 0 ≤ (D ⊔ W) - W := sub_nonneg.2 le_sup_right
  have h3 : deg ((D ⊔ W) - W) = 0 := by
    have := deg_nonneg h2
    rw [map_sub] at this ⊢
    linarith
  have h4 := eq_zero_of_deg_eq_zero h2 h3
  have : D ⊔ W = W := sub_eq_zero.1 h4
  rw [← this]
  exact le_sup_left


open Classical in
noncomputable def divisor (ω : WeilDifferential k K) : Divisor k K :=
  if h : ω = 0 then 0 else Classical.choose (exists_divisor h)

end WeilDifferential

end GroundTheory.FunctionField
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveProper
open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

theorem isNoetherian_of_finiteType {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] : IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact ⟨⟩

theorem isLocallyFactorial_of_dim_le_one {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (hX : topologicalKrullDim X ≤ 1) : IsLocallyFactorial X := by
  refine ⟨fun x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    change UniqueFactorizationMonoid X.functionField
    infer_instance
  · let Z : PrimeDivisor X := ⟨x, ringKrullDim_stalk_eq_one hX hx⟩
    have : IsDedekindDomain (X.presheaf.stalk x) := Z.isDedekindDomain_stalk
    have : IsPrincipalIdealRing (X.presheaf.stalk x) := by
      refine IsPrincipalIdealRing.of_finite_maximals ?_
      refine (Set.finite_singleton (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).subset ?_
      intro I hI
      exact IsLocalRing.eq_maximalIdeal hI
    infer_instance

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.CurvePlaces
set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology

open scoped WithZero

universe u

namespace GroundTheory.Arith.SchemeCoh

section Valuation

end Valuation

section ToPlace

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor

lemma valuation_surjective (Z : PrimeDivisor X) : Function.Surjective Z.valuation := by
  have := Z.isDedekindDomain_stalk
  exact IsDedekindDomain.HeightOneSpectrum.valuation_surjective _ _

lemma valuation_le_one_iff (Z : PrimeDivisor X) (f : X.functionField) :
    Z.valuation f ≤ 1 ↔ f ∈ (algebraMap (X.presheaf.stalk Z.point) X.functionField).range := by
  by_cases hf : f = 0
  · subst hf
    simp only [map_zero, zero_le, true_iff]
    exact ⟨0, map_zero _⟩
  rw [← Z.ord_nonneg_iff hf, ← WithZero.exp_zero, Z.valuation_le_exp_iff hf, neg_zero]

noncomputable def toPlace (Z : PrimeDivisor X) : Place k X.functionField where
  ring := Z.valuation.valuationSubring
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := Z.valuation_surjective (WithZero.exp 1)
    have hmem : π ∈ Z.valuation.valuationSubring := htop ▸ trivial
    rw [Valuation.mem_valuationSubring_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (X.presheaf.stalk Z.point) X.functionField]
    exact Z.valuation_algebraMap_le_one _

lemma mem_toPlace_ring (Z : PrimeDivisor X) (f : X.functionField) :
    f ∈ (Z.toPlace (k := k)).ring ↔ Z.valuation f ≤ 1 :=
  Valuation.mem_valuationSubring_iff _ _

variable [IsFunctionField k X.functionField]

end PrimeDivisor

end ToPlace

section Center

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

lemma fromSpecStalk_genericPoint_comp :
    X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv, ← Scheme.ΓSpecIso_inv_naturality]
  have h1 : (homOfLE le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ⟶ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h1, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

variable (R : ValuationSubring X.functionField)

noncomputable def centerMorphism {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R) :
    Spec (.of R) ⟶ X :=
  Spec.map φ ≫ X.fromSpecStalk x

lemma specMap_comp_centerMorphism {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R)
    (hφ : ∀ a, ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a) :
    Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ centerMorphism R φ =
      X.fromSpecStalk (genericPoint X) := by
  unfold centerMorphism
  rw [← Category.assoc, ← Spec.map_comp]
  have h : φ ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      X.presheaf.stalkSpecializes (genericPoint_specializes x) := by
    ext a
    exact hφ a
  rw [h, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

lemma centerMorphism_closedPoint {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R)
    [IsLocalHom φ.hom] : centerMorphism R φ (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x (Spec.map φ (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]


omit [IsIntegral X] in
lemma eq_of_specMap_comp_eq {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]
    (hι : Function.Injective (algebraMap A K)) {g₁ g₂ : Spec (.of A) ⟶ Spec (.of k)}
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₁ =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g₂) : g₁ = g₂ := by
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext a
  have h' := congr($h a)
  exact hι h'

theorem center_unique [IsSeparated (X ↘ Spec (.of k))] {x y : X}
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of R) (ψ : X.presheaf.stalk y ⟶ CommRingCat.of R)
    [IsLocalHom φ.hom] [IsLocalHom ψ.hom]
    (hφ : ∀ a, ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a)
    (hψ : ∀ a, ((ψ a : R) : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a) :
    x = y := by
  let S : ValuativeCommSq (X ↘ Spec (.of k)) :=
    { R := R, K := X.functionField, i₁ := X.fromSpecStalk (genericPoint X),
      i₂ := centerMorphism R φ ≫ (X ↘ Spec (.of k)),
      commSq := ⟨by rw [← specMap_comp_centerMorphism R φ hφ, Category.assoc]⟩ }
  have hU := IsSeparated.valuativeCriterion (X ↘ Spec (.of k)) S
  let l₁ : S.commSq.LiftStruct :=
    { l := centerMorphism R φ, fac_left := specMap_comp_centerMorphism R φ hφ, fac_right := rfl }
  let l₂ : S.commSq.LiftStruct :=
    { l := centerMorphism R ψ, fac_left := specMap_comp_centerMorphism R ψ hψ,
      fac_right := by
        refine eq_of_specMap_comp_eq (A := R) (K := X.functionField) Subtype.val_injective ?_
        change _ ≫ centerMorphism R ψ ≫ _ = _ ≫ centerMorphism R φ ≫ _
        rw [← Category.assoc, ← Category.assoc, specMap_comp_centerMorphism R ψ hψ,
          specMap_comp_centerMorphism R φ hφ] }
  have h := congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  rw [← centerMorphism_closedPoint R φ, ← centerMorphism_closedPoint R ψ]
  exact congrArg (fun g : Spec (.of R) ⟶ X => g (IsLocalRing.closedPoint R)) h

lemma compatible_of_specMap_comp {x : X} (φ : X.presheaf.stalk x ⟶ CommRingCat.of R)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ centerMorphism R φ =
      X.fromSpecStalk (genericPoint X)) (a : X.presheaf.stalk x) :
    ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a := by
  unfold centerMorphism at h
  rw [← Category.assoc, ← Spec.map_comp,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x),
    cancel_mono, Spec.map_inj] at h
  exact congr($h a)

theorem exists_center [UniversallyClosed (X ↘ Spec (.of k))]
    (hR : ∀ c : k, algebraMap k X.functionField c ∈ R) :
    ∃ (x : X) (φ : X.presheaf.stalk x ⟶ CommRingCat.of R), IsLocalHom φ.hom ∧
      ∀ a, ((φ a : R) : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a := by
  have hE : ValuativeCriterion.Existence (X ↘ Spec (.of k)) := by
    have h := ‹UniversallyClosed (X ↘ Spec (.of k))›
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let ρ : k →+* R := (algebraMap k X.functionField).codRestrict R hR
  let S : ValuativeCommSq (X ↘ Spec (.of k)) :=
    { R := R, K := X.functionField, i₁ := X.fromSpecStalk (genericPoint X),
      i₂ := Spec.map (CommRingCat.ofHom ρ),
      commSq := ⟨by rw [fromSpecStalk_genericPoint_comp, ← Spec.map_comp]; rfl⟩ }
  obtain ⟨l, hl₁, -⟩ := (hE S).exists_lift
  refine ⟨l (IsLocalRing.closedPoint R), Scheme.stalkClosedPointTo l, inferInstance, ?_⟩
  refine compatible_of_specMap_comp R _ ?_
  unfold centerMorphism
  rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact hl₁

end Center

section PlaceEquiv

open GroundTheory.FunctionField

theorem valuationSubring_eq_of_le {K : Type*} [Field K] {A B : ValuationSubring K} (hAB : A ≤ B)
    (hloc : ∀ a ∈ A, a⁻¹ ∈ B → a⁻¹ ∈ A) : A = B := by
  refine le_antisymm hAB fun b hb => ?_
  by_contra hbA
  have hinv : b⁻¹ ∈ A := (A.mem_or_inv_mem b).resolve_left hbA
  have := hloc _ hinv (by rwa [inv_inv])
  rw [inv_inv] at this
  exact hbA this

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor

noncomputable def stalkToPlaceRing (Z : PrimeDivisor X) :
    X.presheaf.stalk Z.point ⟶ CommRingCat.of (Z.toPlace (k := k)).ring :=
  CommRingCat.ofHom ((algebraMap (X.presheaf.stalk Z.point) X.functionField).codRestrict
    (Z.toPlace (k := k)).ring fun a => (Z.mem_toPlace_ring _).mpr (Z.valuation_algebraMap_le_one a))

lemma stalkToPlaceRing_apply (Z : PrimeDivisor X) (a : X.presheaf.stalk Z.point) :
    ((Z.stalkToPlaceRing (k := k) a : (Z.toPlace (k := k)).ring) : X.functionField) =
      algebraMap (X.presheaf.stalk Z.point) X.functionField a := rfl

instance (Z : PrimeDivisor X) : IsLocalHom (Z.stalkToPlaceRing (k := k)).hom := by
  refine ⟨fun a ha => ?_⟩
  have := Z.isDedekindDomain_stalk
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hK : algebraMap (X.presheaf.stalk Z.point) X.functionField a * (b : X.functionField) = 1 := by
    rw [← stalkToPlaceRing_apply (k := k)]
    exact congrArg Subtype.val hb
  have hb1 : Z.valuation (b : X.functionField) ≤ 1 := (Z.mem_toPlace_ring _).mp b.2
  have hval : Z.valuation (algebraMap (X.presheaf.stalk Z.point) X.functionField a) = 1 := by
    refine le_antisymm (Z.valuation_algebraMap_le_one a) ?_
    have h1 := congrArg Z.valuation hK
    rw [map_mul, map_one] at h1
    by_contra hlt
    push Not at hlt
    have : Z.valuation (algebraMap (X.presheaf.stalk Z.point) X.functionField a) *
        Z.valuation (b : X.functionField) < 1 :=
      mul_lt_one_of_lt_of_le hlt hb1
    rw [h1] at this
    exact lt_irrefl _ this
  by_contra hnu
  have hm : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.point) :=
    (IsLocalRing.mem_maximalIdeal a).mpr hnu
  have hlt : Z.valuation (algebraMap (X.presheaf.stalk Z.point) X.functionField a) < 1 := by
    simp only [PrimeDivisor.valuation]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hm
  rw [hval] at hlt
  exact lt_irrefl _ hlt

end PrimeDivisor

variable [IsProper (X ↘ Spec (.of k))]

theorem PrimeDivisor.toPlace_injective :
    Function.Injective (PrimeDivisor.toPlace (k := k) (X := X)) := by
  intro Z W h
  have hring : (Z.toPlace (k := k)).ring = (W.toPlace (k := k)).ring := congrArg Place.ring h
  apply PrimeDivisor.point_injective
  let ψ : X.presheaf.stalk W.point ⟶ CommRingCat.of (Z.toPlace (k := k)).ring :=
    W.stalkToPlaceRing (k := k) ≫ CommRingCat.ofHom (RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring hring.symm)).toRingHom
  have : IsLocalHom ψ.hom := by
    dsimp [ψ]
    infer_instance
  exact center_unique (k := k) (Z.toPlace (k := k)).ring (Z.stalkToPlaceRing (k := k)) ψ
    (fun a => rfl) (fun a => rfl)

theorem PrimeDivisor.toPlace_surjective (hX : topologicalKrullDim X ≤ 1) :
    Function.Surjective (PrimeDivisor.toPlace (k := k) (X := X)) := by
  intro v
  obtain ⟨x, φ, hφl, hφ⟩ := exists_center (k := k) v.ring v.algebraMap_mem
  have hx : x ≠ genericPoint X := by
    intro hxη
    apply v.ne_top
    rw [eq_top_iff]
    intro f _
    have hs : x ⤳ genericPoint X := hxη ▸ specializes_rfl
    have h2 : algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.stalkSpecializes hs f) = f := by
      rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
        TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    have h3 := (φ (X.presheaf.stalkSpecializes hs f)).2
    rw [hφ, h2] at h3
    exact h3
  let Z : PrimeDivisor X := ⟨x, ringKrullDim_stalk_eq_one hX hx⟩
  refine ⟨Z, Place.ext ?_⟩
  have hrange : ∀ f : X.functionField, f ∈ (Z.toPlace (k := k)).ring ↔
      f ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := fun f =>
    (Z.mem_toPlace_ring f).trans (Z.valuation_le_one_iff f)
  refine valuationSubring_eq_of_le ?_ ?_
  · intro f hf
    obtain ⟨a, rfl⟩ := (hrange f).mp hf
    rw [← hφ a]
    exact (φ a).2
  · intro f hf hinv
    obtain ⟨a, rfl⟩ := (hrange f).mp hf
    by_cases ha : algebraMap (X.presheaf.stalk x) X.functionField a = 0
    · rw [ha, inv_zero]
      exact zero_mem _
    have hu : IsUnit (φ a) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
      apply Subtype.val_injective
      change ((φ a : v.ring) : X.functionField) * _ = 1
      rw [hφ a]
      exact mul_inv_cancel₀ ha
    have hau : IsUnit a := (isUnit_map_iff φ.hom a).mp hu
    obtain ⟨u, rfl⟩ := hau
    rw [hrange]
    exact ⟨((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x),
      map_units_inv (algebraMap (X.presheaf.stalk x) X.functionField) u⟩

noncomputable def placeEquiv (hX : topologicalKrullDim X ≤ 1) :
    PrimeDivisor X ≃ Place k X.functionField :=
  Equiv.ofBijective PrimeDivisor.toPlace
    ⟨PrimeDivisor.toPlace_injective, PrimeDivisor.toPlace_surjective hX⟩

end PlaceEquiv

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology Module

open scoped WithZero

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormalScheme X]

namespace PrimeDivisor


noncomputable def degree (Z : PrimeDivisor X) : ℕ :=
  finrank k (IsLocalRing.ResidueField (X.presheaf.stalk Z.point))

end PrimeDivisor

noncomputable def WeilDivisor.degree : WeilDivisor X →+ ℤ :=
  Finsupp.liftAddHom fun Z => AddMonoidHom.mulRight ((Z.degree (k := k) : ℕ) : ℤ)

variable [IsProper (X ↘ Spec (.of k))]

noncomputable def divisorEquiv (hX : topologicalKrullDim X ≤ 1) :
    WeilDivisor X ≃+ Divisor k X.functionField :=
  Finsupp.domCongr (placeEquiv hX)

variable [IsFunctionField k X.functionField]

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCanonical
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MonoidalCategory

universe u

variable {X : Scheme.{u}}

lemma nonempty_inf_of_mem [IsIntegral X] {V W : X.Opens} (y : V) (w : W) : Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨y.1, y.2⟩ ⟨w.1, w.2⟩
  exact ⟨⟨z, hz⟩⟩

section RatVal

variable {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀)

noncomputable def coeffOn {V : X.Opens} (l : P.obj (op V)) : ringOn X (V ⊓ U₀) :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).symm (resM P inf_le_left l)

lemma coeffOn_spec {V : X.Opens} (l : P.obj (op V)) :
    coeffOn hs₀ l • resM P inf_le_right s₀ = resM P inf_le_left l :=
  (Equiv.ofBijective _ (hs₀ (V ⊓ U₀) inf_le_right)).apply_symm_apply _

variable [IsIntegral X] [Nonempty U₀]

noncomputable def ratVal {V : X.Opens} (l : P.obj (op V)) (y : V) : X.functionField :=
  haveI := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  X.germToFunctionField (V ⊓ U₀) (coeffOn hs₀ l)

theorem ratVal_eq {V W : X.Opens} (hWV : W ≤ V) (hWU : W ≤ U₀) [Nonempty W]
    (l : P.obj (op V)) (a : ringOn X W) (ha : a • resM P hWU s₀ = resM P hWV l) (y : V) :
    ratVal hs₀ l y = X.germToFunctionField W a := by
  have hW' : W ≤ V ⊓ U₀ := le_inf hWV hWU
  have h1 := congrArg (resM P hW') (coeffOn_spec hs₀ l)
  rw [resM_smul_res, resM_resM] at h1
  have h2 : a = resR hW' (coeffOn hs₀ l) := (hs₀ W hWU).1 (ha.trans h1.symm)
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [h2]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

lemma ratVal_const {V : X.Opens} (l : P.obj (op V)) (y z : V) :
    ratVal hs₀ l y = ratVal hs₀ l z := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) z]

lemma ratVal_res {V W : X.Opens} (h : W ≤ V) (l : P.obj (op V)) (y : W) :
    ratVal hs₀ (resM P h l) y = ratVal hs₀ l ⟨y.1, h y.2⟩ := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e := coeffOn_spec hs₀ (resM P h l)
  rw [resM_resM] at e
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ (coeffOn_spec hs₀ (resM P h l)) y,
    ratVal_eq hs₀ ((inf_le_left : W ⊓ U₀ ≤ W).trans h) inf_le_right l _ e]

lemma ratVal_smul {V : X.Opens} (a : ringOn X V) (l : P.obj (op V)) (y : V) :
    ratVal hs₀ (a • l) y = sectionValue V y a * ratVal hs₀ l y := by
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  have e : (resR inf_le_left a * coeffOn hs₀ l) • resM P (inf_le_right : V ⊓ U₀ ≤ U₀) s₀ =
      resM P inf_le_left (a • l) := by
    rw [mul_smul, coeffOn_spec, resM_smul]
  rw [ratVal_eq hs₀ inf_le_left inf_le_right _ _ e y,
    ratVal_eq hs₀ inf_le_left inf_le_right l _ (coeffOn_spec hs₀ l) y]
  refine (map_mul (X.germToFunctionField (V ⊓ U₀)).hom
    (show Γ(X, V ⊓ U₀) from resR inf_le_left a) (show Γ(X, V ⊓ U₀) from coeffOn hs₀ l)).trans ?_
  congr 1
  refine Eq.trans ?_ (sectionValue_eq V y (show Γ(X, V) from a)).symm
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

end RatVal

section Invertible

variable [IsIntegral X]
  {P : PMod X} {U₀ : X.Opens} {s₀ : P.obj (op U₀)} (hs₀ : IsBasisOn P U₀ s₀) [Nonempty U₀]

lemma ratVal_ne_zero_of_isBasisOn {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    (y : U) : ratVal hs₀ s y ≠ 0 := by
  intro h
  have := nonempty_inf_of_mem y (Classical.arbitrary U₀)
  rw [ratVal_eq hs₀ inf_le_left inf_le_right s _ (coeffOn_spec hs₀ s) y] at h
  have hr : coeffOn hs₀ s = 0 := Scheme.germToFunctionField_injective X (U ⊓ U₀)
    (h.trans (map_zero _).symm)
  have hz : resM P (inf_le_left : U ⊓ U₀ ≤ U) s = 0 := by
    rw [← coeffOn_spec hs₀ s, hr, zero_smul]
  have hb := (hs (U ⊓ U₀) inf_le_left).1
  have h10 : (1 : ringOn X (U ⊓ U₀)) = 0 := hb (by simp only [hz, smul_zero])
  exact one_ne_zero (α := Γ(X, U ⊓ U₀)) h10


variable {L : X.Modules} (hL : IsInvertibleSheaf L)

noncomputable def basisOpen (x : X) : X.Opens := (hL x).choose

omit [IsIntegral X] in
lemma mem_basisOpen (x : X) : x ∈ basisOpen hL x := (hL x).choose_spec.choose

noncomputable def basisSec (x : X) : ((preMod X).obj L).obj (op (basisOpen hL x)) :=
  (hL x).choose_spec.choose_spec.choose

omit [IsIntegral X] in
lemma isBasisOn_basisSec (x : X) :
    IsBasisOn ((preMod X).obj L) (basisOpen hL x) (basisSec hL x) :=
  (hL x).choose_spec.choose_spec.choose_spec

instance (x : X) : Nonempty (basisOpen hL x) := ⟨⟨x, mem_basisOpen hL x⟩⟩

noncomputable def secVal {V : X.Opens} (l : ((preMod X).obj L).obj (op V)) (y : V) :
    X.functionField :=
  ratVal (isBasisOn_basisSec hL (Classical.arbitrary X)) l y

lemma secVal_basisSec_ne_zero (x : X) (y : basisOpen hL x) :
    secVal hL (basisSec hL x) y ≠ 0 :=
  ratVal_ne_zero_of_isBasisOn _ (isBasisOn_basisSec hL x) y

variable [IsNoetherian X] [IsLocallyFactorial X]

lemma ord_secVal_basisSec (Z : PrimeDivisor X) (x : X) (hZ : Z.point ∈ basisOpen hL x) :
    Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZ⟩) =
      Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩) := by
  set W := basisOpen hL x ⊓ basisOpen hL Z.point
  have hZW : Z.point ∈ W := ⟨hZ, mem_basisOpen hL Z.point⟩
  have : Nonempty W := ⟨⟨Z.point, hZW⟩⟩
  obtain ⟨u, hu⟩ := (isBasisOn_basisSec hL Z.point W inf_le_right).2
    (resM _ inf_le_left (basisSec hL x))
  obtain ⟨v, hv⟩ := (isBasisOn_basisSec hL x W inf_le_left).2
    (resM _ inf_le_right (basisSec hL Z.point))
  have hu' : u • resM _ inf_le_right (basisSec hL Z.point) = resM _ inf_le_left (basisSec hL x) :=
    hu
  have hv' : v • resM _ inf_le_left (basisSec hL x) = resM _ inf_le_right (basisSec hL Z.point) :=
    hv
  have huv : u * v = 1 := (isBasisOn_basisSec hL x W inf_le_left).1 (by
    change (u * v) • resM _ inf_le_left (basisSec hL x) = (1 : ringOn X W) • _
    rw [mul_smul, hv', hu', one_smul])
  have hunit : IsUnit (M := Γ(X, W)) u := isUnit_iff_exists_inv.mpr ⟨v, huv⟩
  have h1 := ratVal_smul (isBasisOn_basisSec hL (Classical.arbitrary X)) u
    (resM _ inf_le_right (basisSec hL Z.point)) ⟨Z.point, hZW⟩
  rw [hu', ratVal_res, ratVal_res] at h1
  change secVal hL (basisSec hL x) ⟨Z.point, hZ⟩ = sectionValue W ⟨Z.point, hZW⟩ u *
    secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩ at h1
  have hsv : sectionValue W ⟨Z.point, hZW⟩ u ≠ 0 := by
    intro h0
    apply hunit.ne_zero
    exact Scheme.germToFunctionField_injective X W
      ((sectionValue_eq _ _ _).symm.trans (h0.trans (map_zero _).symm))
  have h0 : Z.ord (sectionValue W ⟨Z.point, hZW⟩ u) = 0 :=
    (congrArg Z.ord (sectionValue_eq _ _ _)).trans (Z.ord_germToFunctionField_of_isUnit hZW hunit)
  rw [h1, Z.ord_mul hsv (secVal_basisSec_ne_zero hL _ _), h0, zero_add]

noncomputable def divisorOfInvertible : WeilDivisor X :=
  Finsupp.ofSupportFinite
    (fun Z => - Z.ord (secVal hL (basisSec hL Z.point) ⟨Z.point, mem_basisOpen hL Z.point⟩)) (by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (basisOpen hL x : Set X))
      (fun x => (basisOpen hL x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_basisOpen hL x⟩)
    refine (t.finite_toSet.biUnion fun x _ => PrimeDivisor.finite_ord_ne_zero
      (secVal_basisSec_ne_zero hL x ⟨x, mem_basisOpen hL x⟩)).subset ?_
    intro Z hZ
    obtain ⟨x, hx, hZx⟩ : ∃ x ∈ t, Z.point ∈ basisOpen hL x := by
      have := ht (Set.mem_univ Z.point)
      simpa using this
    refine Set.mem_biUnion hx ?_
    simp only [Function.mem_support, ne_eq, neg_eq_zero] at hZ
    change Z.ord (ratVal _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩) ≠ 0
    rw [ratVal_const _ (basisSec hL x) ⟨x, mem_basisOpen hL x⟩ ⟨Z.point, hZx⟩]
    change Z.ord (secVal hL (basisSec hL x) ⟨Z.point, hZx⟩) ≠ 0
    rwa [ord_secVal_basisSec hL Z x hZx])

end Invertible

end GroundTheory.Arith.SchemeCoh
end

open CategoryTheory AlgebraicGeometry Order Topology Module MonoidalCategory

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField]


omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in
noncomputable def invertibleDegree {L : X.Modules} (hL : IsInvertibleSheaf L) : ℤ :=
  WeilDivisor.degree (k := k) (divisorOfInvertible hL)



variable (hX : topologicalKrullDim X ≤ 1)

noncomputable def canonicalDifferential : WeilDifferential k X.functionField :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose


noncomputable def canonicalDivisor : WeilDivisor X :=
  (divisorEquiv (k := k) hX).symm (canonicalDifferential (k := k) (X := X)).divisor

noncomputable def canonicalSheaf : X.Modules :=
  divisorSheaf (canonicalDivisor (k := k) hX)

end GroundTheory.Arith.SchemeCoh
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Module MonoidalCategory

universe w' u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

variable [IsIntegral X] [IsProper (X ↘ Spec (.of k))] [IsNormalScheme X]

section Instances

variable (hX : topologicalKrullDim X = 1)


omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
include hX in
theorem curve_instances :
    IsNoetherian X ∧ IsLocallyFactorial X ∧ IsFunctionField k X.functionField := by
  have : IsNoetherian X := isNoetherian_of_finiteType (k := k) X
  exact ⟨this, isLocallyFactorial_of_dim_le_one hX.le, isFunctionField X hX⟩

end Instances

section Genus



end Genus

section Degree

noncomputable def sheafDegree (hX : topologicalKrullDim X = 1) {L : X.Modules}
    (hL : IsInvertibleSheaf L) : ℤ :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  invertibleDegree (k := k) hL

end Degree

section Canonical

noncomputable def omega (hX : topologicalKrullDim X = 1) : X.Modules :=
  haveI := (curve_instances (k := k) hX).1
  haveI := (curve_instances (k := k) hX).2.1
  haveI := (curve_instances (k := k) hX).2.2
  canonicalSheaf (k := k) hX.le

end Canonical

section RiemannRoch

end RiemannRoch

end GroundTheory.Arith.SchemeCoh
