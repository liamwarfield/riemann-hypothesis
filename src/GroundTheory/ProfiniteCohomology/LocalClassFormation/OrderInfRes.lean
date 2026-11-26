module

public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.LocalFields.Unramified
public import GroundTheory.LocalFields.RamificationStructure

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderBound
section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderCyclic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Bridge

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem galUnits_norm_apply (x : Additive Lˣ) :
    (galUnits.{u} K L).ρ.norm x =
      Additive.ofMul (GroundTheory.LocalField.tateNorm Gal(L/K) Lˣ (Additive.toMul x)) := by
  rw [Representation.norm, LinearMap.sum_apply, GroundTheory.LocalField.tateNorm_apply, ofMul_prod]
  rfl


omit [FiniteDimensional K L] in
theorem mem_invariants_galUnits_iff (x : Additive Lˣ) :
    x ∈ (galUnits.{u} K L).ρ.invariants ↔
      Additive.toMul x ∈ GroundTheory.LocalField.invariants Gal(L/K) Lˣ :=
  Iff.rfl

def invariantsGalUnitsEquiv :
    (galUnits.{u} K L).ρ.invariants ≃ GroundTheory.LocalField.invariants Gal(L/K) Lˣ where
  toFun x := ⟨Additive.toMul x.1, (mem_invariants_galUnits_iff K L x.1).1 x.2⟩
  invFun y := ⟨Additive.ofMul y.1, (mem_invariants_galUnits_iff K L _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def tateZeroGalUnitsEquiv :
    ((galUnits.{u} K L).ρ.invariants ⧸ GroundTheory.GroupCoh.normRangeInvariants (galUnits.{u} K L)) ≃
      GroundTheory.LocalField.TateZero Gal(L/K) Lˣ :=
  Quotient.congr (invariantsGalUnitsEquiv K L) fun a b => by
    rw [Submodule.quotientRel_def, QuotientGroup.leftRel_apply,
      GroundTheory.GroupCoh.mem_normRangeInvariants_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨(Additive.toMul (α := Lˣ) m)⁻¹, ?_⟩
      rw [galUnits_norm_apply] at hm
      have h := congrArg Additive.toMul hm
      simp only [toMul_ofMul] at h
      rw [map_inv, h]
      simp [invariantsGalUnitsEquiv, div_eq_mul_inv, mul_comm]
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul (α := Lˣ) y⁻¹, ?_⟩
      rw [galUnits_norm_apply, toMul_ofMul, map_inv, hy]
      simp [invariantsGalUnitsEquiv, mul_comm]
      rfl

end Bridge

section Cyclic

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem natCard_groupCohomology_two_galUnits_of_isCyclic [IsCyclic Gal(L/K)] :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) = Module.finrank K L := by
  classical
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (galUnits.{u} K L) 2 ≅
      (GroundTheory.GroupCoh.tateZeroFunctor (R := ULift.{u} ℤ) (G := Gal(L/K))).obj (galUnits.{u} K L) :=
    ((TateCohomology.isoGroupCohomology 2).app (galUnits.{u} K L)).symm ≪≫
      GroundTheory.GroupCoh.tateCohomologyPeriodicIso (galUnits.{u} K L) hσ 0 ≪≫
      (GroundTheory.GroupCoh.tateCohomologyZeroIso (R := ULift.{u} ℤ) (G := Gal(L/K))).app (galUnits.{u} K L)
  rw [Nat.card_congr e.toLinearEquiv.toEquiv]
  rw [← GroundTheory.LocalField.natCard_tateZero_units (K := K) (L := L)]
  exact Nat.card_congr (tateZeroGalUnitsEquiv K L)

end Cyclic

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits IntermediateField

universe u

section Transport

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

noncomputable def subgroupEquivGalFixedField (H : Subgroup Gal(L/K)) :
    H ≃* Gal(L/fixedField H) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans
    (fixingSubgroupEquiv (fixedField H))

noncomputable def groupCohomologyResGalUnitsIso (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (galUnits.{u} K L)) n ≅
      groupCohomology (galUnits.{u} (fixedField H) L) n :=
  groupCohomology.mapIso (subgroupEquivGalFixedField H) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

theorem isZero_groupCohomology_one_res_galUnits (H : Subgroup Gal(L/K)) :
    IsZero (groupCohomology (Rep.res H.subtype (galUnits.{u} K L)) 1) :=
  (isZero_groupCohomology_one_galUnits (fixedField H) L).of_iso
    (groupCohomologyResGalUnitsIso H 1)

end Transport

section Step

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def openNormalOfNormal (N : Subgroup Gal(L/K)) [N.Normal] : OpenNormalSubgroup Gal(L/K) where
  toSubgroup := N
  isOpen' := isOpen_discrete _
  isNormal' := inferInstance

theorem natCard_groupCohomology_two_galUnits_dvd_of_normal (N : Subgroup Gal(L/K)) [N.Normal]
    (hLE : Nat.card (groupCohomology (galUnits.{u} (fixedField N) L) 2) ∣
      Module.finrank (fixedField N) L)
    (hEK : Nat.card (groupCohomology (galUnits.{u} K (fixedField N)) 2) ∣
      Module.finrank K (fixedField N)) :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ Module.finrank K L := by
  have h1 := isZero_groupCohomology_one_res_galUnits (K := K) (L := L) N
  have hinj := GroundTheory.GroupCoh.inflation_two_injective (A := galUnits.{u} K L) (S := N) h1
  have hex := GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := galUnits.{u} K L) (S := N) h1
  set res := (GroundTheory.GroupCoh.restriction (galUnits.{u} K L) N 2).hom
  set infl := (GroundTheory.GroupCoh.inflation (galUnits.{u} K L) N 2).hom

  have hcard : Nat.card (groupCohomology (galUnits.{u} K L) 2) =
      Nat.card (LinearMap.range res) * Nat.card (LinearMap.ker res) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker res),
      Nat.card_congr (LinearMap.quotKerEquivRange res).toEquiv, mul_comm]

  have hker : Nat.card (LinearMap.ker res) =
      Nat.card (groupCohomology (galUnits.{u} K (fixedField N)) 2) := by
    rw [← hex, ← Nat.card_congr (LinearEquiv.ofInjective infl hinj).toEquiv]
    exact Nat.card_congr (groupCohomologyQuotientGalUnitsIso (openNormalOfNormal N) 2).toLinearEquiv.toEquiv

  have hrange : Nat.card (LinearMap.range res) ∣
      Nat.card (groupCohomology (galUnits.{u} (fixedField N) L) 2) := by
    rw [← Nat.card_congr (groupCohomologyResGalUnitsIso N 2).toLinearEquiv.toEquiv]
    exact AddSubgroup.card_addSubgroup_dvd_card (LinearMap.range res).toAddSubgroup
  rw [hcard, hker, ← (letI : Module.Free (fixedField N) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K (fixedField N) L), mul_comm (Module.finrank K _)]
  exact Nat.mul_dvd_mul (hrange.trans hLE) hEK

end Step

section Solvable

theorem exists_normal_ne_bot_ne_top_of_not_isCyclic {G : Type*} [Group G] [Group.IsSolvable G]
    (h : ¬IsCyclic G) : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hN
  push Not at hN
  have : Nontrivial G := by
    by_contra ht
    rw [not_nontrivial_iff_subsingleton] at ht
    exact h inferInstance
  have : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN' => by
        by_cases hb : N = ⊥
        · exact Or.inl hb
        · exact Or.inr (hN N hN' hb) }
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 inferInstance
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  exact h IsSimpleGroup.isCyclic

end Solvable

section Bound

theorem natCard_groupCohomology_two_galUnits_dvd_of_finrank (n : ℕ) :
    ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K]
      [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
      [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L = n → Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ hn
  subst hn
  by_cases hcyc : IsCyclic Gal(L/K)
  · exact (natCard_groupCohomology_two_galUnits_of_isCyclic (K := K) (L := L)).dvd
  have := GroundTheory.LocalField.isSolvable_algEquiv (K := K) (L := L)
  obtain ⟨N, hN, hbot, htop⟩ := exists_normal_ne_bot_ne_top_of_not_isCyclic hcyc
  have hpos : 0 < Module.finrank K (fixedField N) := Module.finrank_pos
  have hLE : Module.finrank (fixedField N) L = Nat.card N := finrank_fixedField_eq_card N
  have hmul := (letI : Module.Free (fixedField N) L := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank K (fixedField N) L)
  have hcardG : Nat.card Gal(L/K) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hNlt : Nat.card N < Module.finrank K L := by
    rw [← hcardG]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group N)
      fun h => htop ((Subgroup.card_eq_iff_eq_top N).1 h)
  have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hbot
  apply natCard_groupCohomology_two_galUnits_dvd_of_normal N
  · exact ih _ (by rw [hLE]; exact hNlt) (fixedField N) L rfl
  · refine ih _ ?_ K (fixedField N) rfl
    rw [← hmul, hLE]
    exact lt_mul_right hpos hN1

end Bound

section Main

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem natCard_groupCohomology_two_galUnits_dvd :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) ∣ Module.finrank K L :=
  natCard_groupCohomology_two_galUnits_dvd_of_finrank _ K L rfl

theorem finite_groupCohomology_two_galUnits :
    Finite (groupCohomology (galUnits.{u} K L) 2) :=
  Nat.finite_of_card_ne_zero fun h =>
    Module.finrank_pos.ne' (Nat.eq_zero_of_zero_dvd (h ▸ natCard_groupCohomology_two_galUnits_dvd))

end Main

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits

universe u

section Tower

theorem additive_units_ext {M : Type u} [Field M] {x y : Additive Mˣ}
    (h : ((Additive.toMul x : Mˣ) : M) = ((Additive.toMul y : Mˣ) : M)) : x = y :=
  Additive.toMul.injective (Units.ext h)

variable (K F M : Type u) [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M] [Algebra F M]
  [IsScalarTower K F M]

def galRestrictScalars : Gal(M/F) →* Gal(M/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

theorem galRestrictScalars_injective : Function.Injective (galRestrictScalars K F M) :=
  fun _ _ h => AlgEquiv.ext fun x => DFunLike.congr_fun h x

def unitsResScalarsHom :
    Rep.res (galRestrictScalars K F M) (galUnits.{u} K M) ⟶ galUnits.{u} F M :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

noncomputable def unitsRes (n : ℕ) :
    groupCohomology (galUnits.{u} K M) n ⟶ groupCohomology (galUnits.{u} F M) n :=
  groupCohomology.map (galRestrictScalars K F M) (unitsResScalarsHom K F M) n

variable [Normal K F]

noncomputable def unitsInclHom :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F) (galUnits.{u} K F) ⟶
      galUnits.{u} K M :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Fˣ) (B := Additive Mˣ)
    (MonoidHom.toAdditive (Units.map ((algebraMap F M : F →+* M) : F →* M))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)⟩

noncomputable def unitsInfl (n : ℕ) :
    groupCohomology (galUnits.{u} K F) n ⟶ groupCohomology (galUnits.{u} K M) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom F) (unitsInclHom K F M) n

variable [FiniteDimensional K M] [IsGalois K M]

noncomputable abbrev galFixing : Subgroup Gal(M/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F).ker

omit [FiniteDimensional K M] [IsGalois K M] in
theorem mem_galFixing_iff (σ : Gal(M/K)) :
    σ ∈ galFixing K F M ↔ ∀ x : F, σ (algebraMap F M x) = algebraMap F M x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ F x]
    change algebraMap F M ((AlgEquiv.restrictNormalHom F σ) x) = _
    rw [h]
    rfl
  · intro h
    ext x
    apply (algebraMap F M).injective
    change algebraMap F M ((AlgEquiv.restrictNormal σ F) x) = _
    rw [AlgEquiv.restrictNormal_commutes, h]
    rfl

omit [FiniteDimensional K M] [IsGalois K M] in
theorem range_galRestrictScalars : (galRestrictScalars K F M).range = galFixing K F M := by
  ext σ
  rw [mem_galFixing_iff]
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

noncomputable def galFixingEquiv : Gal(M/F) ≃* galFixing K F M :=
  (MonoidHom.ofInjective (galRestrictScalars_injective K F M)).trans
    (MulEquiv.subgroupCongr (range_galRestrictScalars K F M))


noncomputable def galFixingCohomologyIso (n : ℕ) :
    groupCohomology (galUnits.{u} F M) n ≅
      groupCohomology (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) n :=
  groupCohomology.mapIso (galFixingEquiv K F M) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

omit [FiniteDimensional K M] [IsGalois K M] in
theorem unitsRes_eq (n : ℕ) :
    unitsRes K F M n = GroundTheory.GroupCoh.restriction (galUnits.{u} K M) (galFixing K F M) n ≫
      (galFixingCohomologyIso K F M n).inv := by
  have hinv : (galFixingCohomologyIso K F M n).inv = groupCohomology.map
      (galFixingEquiv K F M : Gal(M/F) →* galFixing K F M)
      (Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩ : Rep.res (galFixingEquiv K F M : Gal(M/F) →* _)
        (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) ⟶ galUnits.{u} F M) n := rfl
  rw [hinv, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext σ x
    rfl
  · rfl

omit [IsGalois K M] in
theorem isZero_groupCohomology_one_galFixing :
    IsZero (groupCohomology (Rep.res (galFixing K F M).subtype (galUnits.{u} K M)) 1) := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  exact (isZero_groupCohomology_one_galUnits F M).of_iso (galFixingCohomologyIso K F M 1).symm

noncomputable def unitsToInvariantsTower :
    Additive Fˣ →ₗ[ULift.{u} ℤ]
      Representation.invariants ((galUnits.{u} K M).ρ.comp (galFixing K F M).subtype) :=
  LinearMap.codRestrict _ (unitsInclHom K F M).hom.toLinearMap fun x σ => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (mem_galFixing_iff K F M σ.1).1 σ.2 _

theorem unitsToInvariantsTower_bijective : Function.Bijective (unitsToInvariantsTower K F M) := by
  have : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite K F M
  have : IsGalois F M := IsGalois.tower_top_of_isGalois K F M
  constructor
  · intro x y h
    have h' := congrArg (fun v => ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M)) h
    apply Additive.toMul.injective
    apply Units.ext
    exact (algebraMap F M).injective h'
  · intro v
    have hfix : ∀ τ : Gal(M/F), τ ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M) =
        ((Additive.toMul (α := Mˣ) v.1 : Mˣ) : M) := by
      intro τ
      have := v.2 ⟨galRestrictScalars K F M τ, (range_galRestrictScalars K F M) ▸ ⟨τ, rfl⟩⟩
      exact congrArg (fun w => ((Additive.toMul (α := Mˣ) w : Mˣ) : M)) this
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 hfix)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (Additive.toMul (α := Mˣ) v.1).ne_zero hy.symm
    refine ⟨Additive.ofMul (Units.mk0 y hy0), Subtype.ext ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    exact hy

noncomputable def unitsInvariantsEquivTower :
    Additive Fˣ ≃ₗ[ULift.{u} ℤ]
      Representation.invariants ((galUnits.{u} K M).ρ.comp (galFixing K F M).subtype) :=
  LinearEquiv.ofBijective _ (unitsToInvariantsTower_bijective K F M)

noncomputable def galQuotientEquiv : Gal(M/K) ⧸ galFixing K F M ≃* Gal(F/K) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (AlgEquiv.restrictNormalHom_surjective M)

noncomputable def galQuotientCohomologyIso (n : ℕ) :
    groupCohomology (galUnits.{u} K F) n ≅
      groupCohomology ((galUnits.{u} K M).quotientToInvariants (galFixing K F M)) n :=
  groupCohomology.mapIso (galQuotientEquiv K F M).symm (unitsInvariantsEquivTower K F M) (fun g => by
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) M g
    have hq : (galQuotientEquiv K F M).symm (AlgEquiv.restrictNormalHom F σ) =
        (σ : Gal(M/K) ⧸ galFixing K F M) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hq]
    refine LinearMap.ext fun x => Subtype.ext (additive_units_ext ?_)
    exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)) n

theorem unitsInfl_eq (n : ℕ) :
    unitsInfl K F M n = (galQuotientCohomologyIso K F M n).hom ≫
      GroundTheory.GroupCoh.inflation (galUnits.{u} K M) (galFixing K F M) n := by
  have hhom : (galQuotientCohomologyIso K F M n).hom = groupCohomology.map
      (galQuotientEquiv K F M : Gal(M/K) ⧸ galFixing K F M →* Gal(F/K))
      (Rep.ofHom ⟨(unitsInvariantsEquivTower K F M).toLinearMap, fun g => by
        obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
        refine LinearMap.ext fun x => Subtype.ext (additive_units_ext ?_)
        exact AlgEquiv.restrictNormal_commutes σ F ((Additive.toMul (α := Fˣ) x : Fˣ) : F)⟩ :
        Rep.res (galQuotientEquiv K F M : Gal(M/K) ⧸ galFixing K F M →* Gal(F/K))
          (galUnits.{u} K F) ⟶ (galUnits.{u} K M).quotientToInvariants (galFixing K F M)) n := rfl
  rw [hhom, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ n
  · ext σ x
    rfl
  · rfl

theorem unitsInfl_two_injective : Function.Injective (unitsInfl K F M 2).hom := by
  rw [unitsInfl_eq, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (GroundTheory.GroupCoh.inflation_two_injective (A := galUnits.{u} K M) (S := galFixing K F M)
    (isZero_groupCohomology_one_galFixing K F M)).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

theorem range_unitsInfl_two_eq_ker_unitsRes :
    LinearMap.range (unitsInfl K F M 2).hom = LinearMap.ker (unitsRes K F M 2).hom := by
  have hsurj : Function.Surjective (galQuotientCohomologyIso K F M 2).hom.hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hinj : Function.Injective (galFixingCohomologyIso K F M 2).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [unitsInfl_eq, unitsRes_eq, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 hsurj, Submodule.map_top, LinearMap.ker_comp,
    LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot]
  exact GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := galUnits.{u} K M)
    (S := galFixing K F M) (isZero_groupCohomology_one_galFixing K F M)

end Tower

section Count

variable (K E F M : Type u) [Field K] [Field E] [Field F] [Field M] [Algebra K E] [Algebra K F]
  [Algebra K M] [Algebra E M] [Algebra F M] [IsScalarTower K E M] [IsScalarTower K F M]
  [Normal K E] [Normal K F] [FiniteDimensional K M] [IsGalois K M]

theorem natCard_le_of_unitsInfl_comp_unitsRes_eq_zero
    (h : unitsInfl K E M 2 ≫ unitsRes K F M 2 = 0)
    [Finite (groupCohomology (galUnits.{u} K F) 2)] :
    Nat.card (groupCohomology (galUnits.{u} K E) 2) ≤
      Nat.card (groupCohomology (galUnits.{u} K F) 2) := by
  have hmem : ∀ y, (unitsInfl K E M 2).hom y ∈ LinearMap.range (unitsInfl K F M 2).hom := by
    intro y
    rw [range_unitsInfl_two_eq_ker_unitsRes, LinearMap.mem_ker]
    exact congrArg (fun φ => φ.hom y) h
  choose g hg using hmem
  refine Nat.card_le_card_of_injective g fun y y' hyy' => ?_
  apply unitsInfl_two_injective K E M
  rw [← hg y, ← hg y', hyy']

end Count

end GroundTheory.ProfCoh
