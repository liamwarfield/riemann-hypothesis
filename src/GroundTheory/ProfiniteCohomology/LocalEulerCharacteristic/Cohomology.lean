module

public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.KummerOpen
public import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.SubsingletonCohomologyOneGalUnitsSubgroupOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Formation

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {C : Rep.{u} k G} [IsDiscreteRep C]


omit [CompactSpace G] in
theorem cohomologyRes_subgroupOf_surjective {U V : OpenSubgroup G} (h : V ≤ U) (n : ℕ)
    (hs : Function.Surjective (cohomologyResLE C (show (V : Subgroup G) ≤ U from h) n).hom) :
    Function.Surjective
      (cohomologyRes (Rep.res (U : Subgroup G).subtype C) ((V : Subgroup G).subgroupOf U) n).hom := by
  intro y
  set e := cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe (show (V : Subgroup G) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom (show (V : Subgroup G) ≤ U from h) C) n
  have he : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  obtain ⟨x, hx⟩ := hs (e.hom y)
  refine ⟨x, he ?_⟩
  rw [← hx, cohomologyResLE_eq_cohomologyRes_comp]
  rfl

theorem ClassFormation.cohomologyConj_two_eq_id (F : ClassFormation C) {U V : OpenSubgroup G}
    (h : V ≤ U) [((V : Subgroup G).subgroupOf (U : Subgroup G)).Normal] (g : (U : Subgroup G)) :
    cohomologyConj (Rep.res (U : Subgroup G).subtype C) ((V : Subgroup G).subgroupOf U) 2 g = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := cohomologyRes_subgroupOf_surjective h 2 (ClassFormation.cohomologyResLE_surjective F h) y
  exact congrArg (fun φ => φ.hom x) (cohomologyRes_comp_cohomologyConj (Rep.res (U : Subgroup G).subtype C)
    ((V : Subgroup G).subgroupOf U) 2 g)

end Formation

section Local

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {l : ℕ}

noncomputable abbrev kummerSequenceResRes (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    ShortComplex (Rep (ULift.{0} ℤ) N) :=
  ((kummerSequence K Ksep l).map (Rep.resFunctor U.subtype)).map (Rep.resFunctor N.subtype)

instance isDiscreteRep_kummerSequenceResRes_X₁ (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).X₁ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_kummerSequenceResRes_X₂ (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).X₂ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_kummerSequenceResRes_X₃ (l : ℕ) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).X₃ :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_galRootsOfUnity (U : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res U.subtype (galRootsOfUnity.{0} K Ksep l)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_galUnits (U : Subgroup Gal(Ksep/K)) :
    IsDiscreteRep (Rep.res U.subtype (galUnits.{0} K Ksep)) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_res_galUnits (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (Rep.res N.subtype (Rep.res U.subtype (galUnits.{0} K Ksep))) :=
  isDiscreteRep_res_subtype _ _

instance isDiscreteRep_res_res_res_galRootsOfUnity (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    IsDiscreteRep (Rep.res N.subtype (Rep.res U.subtype (galRootsOfUnity.{0} K Ksep l))) :=
  isDiscreteRep_res_subtype _ _

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem kummerSequenceResRes_shortExact (hl : (l : K) ≠ 0) (U : Subgroup Gal(Ksep/K)) (N : Subgroup U) :
    (kummerSequenceResRes (K := K) (Ksep := Ksep) l U N).ShortExact :=
  shortExact_map_res N (shortExact_map_res U (kummerSequence_shortExact l hl))


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem subsingleton_cohomology_one_galUnits_subgroupOf {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) :
    Subsingleton (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf U).subtype
      (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep))) 1) := by
  have e := asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
    (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ (galUnits.{0} K Ksep)) 1)
  exact (ModuleCat.isZero_iff_subsingleton).1 ((isZero_H1_open K Ksep V).of_iso e)

theorem cohomologyConj_two_galRootsOfUnity_eq_id (hl : (l : K) ≠ 0) {U V : OpenSubgroup Gal(Ksep/K)}
    (h : V ≤ U) [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal] (g : (U : Subgroup Gal(Ksep/K))) :
    cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf U) 2 g = 𝟙 _ := by
  set N := (V : Subgroup Gal(Ksep/K)).subgroupOf U
  set f := (Rep.resFunctor (U : Subgroup Gal(Ksep/K)).subtype).map (kummerSequence K Ksep l).f
  set fN := cohomologyMap ((Rep.resFunctor N.subtype).map f) 2
  have hinj : Function.Injective fN.hom :=
    cohomologyMap_f_injective_of_subsingleton (kummerSequenceResRes_shortExact hl _ N) 1
      (subsingleton_cohomology_one_galUnits_subgroupOf h)
  have hnat := cohomologyConj_naturality (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
    (galRootsOfUnity.{0} K Ksep l)) N f 2 g
  refine ModuleCat.hom_ext (LinearMap.ext fun y => hinj ?_)
  have e1 : (cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)) N 2 g).hom
      (fN.hom y) = fN.hom ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) N 2 g).hom y) :=
    congrArg (fun φ => φ.hom y) hnat
  have e2 := congrArg (fun φ => φ.hom (fN.hom y))
    ((localClassFormationOfIsSepClosure K Ksep).cohomologyConj_two_eq_id h g)
  exact e1.symm.trans (e2.trans rfl)

end Local

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyKummer
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField

section FixedField

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)
  [hN : ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]


include h hN in
theorem inv_mul_mul_mem_of_subgroupOf_normal (g : (U : Subgroup Gal(Ksep/K))) {v : Gal(Ksep/K)}
    (hv : v ∈ (V : Subgroup Gal(Ksep/K))) :
    (g : Gal(Ksep/K))⁻¹ * v * g ∈ (V : Subgroup Gal(Ksep/K)) := by
  have := hN.conj_mem ⟨v, h hv⟩ (Subgroup.mem_subgroupOf.2 hv) g⁻¹
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this


include h hN in
theorem apply_mem_fixedField (g : (U : Subgroup Gal(Ksep/K))) {x : Ksep}
    (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K))) :
    (g : Gal(Ksep/K)) x ∈ fixedField (V : Subgroup Gal(Ksep/K)) := by
  rw [mem_fixedField_iff] at hx ⊢
  intro v hv
  have e := hx _ (inv_mul_mul_mem_of_subgroupOf_normal h g hv)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv] at e
  calc v ((g : Gal(Ksep/K)) x) = (g : Gal(Ksep/K)) ((g : Gal(Ksep/K)).symm (v ((g : Gal(Ksep/K)) x))) :=
        ((g : Gal(Ksep/K)).apply_symm_apply _).symm
    _ = (g : Gal(Ksep/K)) x := by rw [e]

def fixedFieldConj (g : (U : Subgroup Gal(Ksep/K))) :
    fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)) where
  toFun x := ⟨(g : Gal(Ksep/K)) (x : Ksep), apply_mem_fixedField h g x.2⟩
  invFun x := ⟨((g⁻¹ : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) (x : Ksep), apply_mem_fixedField h g⁻¹ x.2⟩
  left_inv x := Subtype.ext (by
    change ((g⁻¹ : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) ((g : Gal(Ksep/K)) (x : Ksep)) = x
    rw [Subgroup.coe_inv, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  right_inv x := Subtype.ext (by
    change (g : Gal(Ksep/K)) (((g⁻¹ : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) (x : Ksep)) = x
    rw [Subgroup.coe_inv, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
  map_mul' x y := Subtype.ext (map_mul (g : Gal(Ksep/K)) (x : Ksep) y)
  map_add' x y := Subtype.ext (map_add (g : Gal(Ksep/K)) (x : Ksep) y)
  commutes' c := Subtype.ext ((g : Gal(Ksep/K)).commutes c)

def fixedFieldConjHom :
    (U : Subgroup Gal(Ksep/K)) →* (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K))) where
  toFun := fixedFieldConj h
  map_one' := AlgEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => Subtype.ext rfl

end FixedField

section Invariants

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)

def unitOfMemFixedField (a : Ksepˣ) (ha : (a : Ksep) ∈ fixedField (V : Subgroup Gal(Ksep/K))) :
    (fixedField (V : Subgroup Gal(Ksep/K)))ˣ :=
  Units.mk0 ⟨a, ha⟩ fun h0 => a.ne_zero (congrArg Subtype.val h0)


include h in
theorem mem_fixedField_of_forall_subgroupOf {x : Ksep}
    (hx : ∀ n : ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))),
      ((n : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) x = x) :
    x ∈ fixedField (V : Subgroup Gal(Ksep/K)) :=
  (mem_fixedField_iff _ _).2 fun v hv => hx ⟨⟨v, h hv⟩, Subgroup.mem_subgroupOf.2 hv⟩

theorem subgroupOf_apply_of_mem_fixedField {x : Ksep} (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (n : ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) :
    ((n : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) x = x :=
  (mem_fixedField_iff _ _).1 hx _ (Subgroup.mem_subgroupOf.1 n.2)

noncomputable def unitsInvariantsOpenEquiv :
    Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ ≃+
      (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep))).ρ.invariants where
  toFun u := ⟨Additive.ofMul (Units.map (algebraMap (fixedField (V : Subgroup Gal(Ksep/K))) Ksep : _ →* Ksep)
      u.toMul), fun n => congrArg Additive.ofMul (Units.ext
        (subgroupOf_apply_of_mem_fixedField ((u.toMul : fixedField (V : Subgroup Gal(Ksep/K)))).2 n))⟩
  invFun v := Additive.ofMul (unitOfMemFixedField (Additive.toMul (v : Additive Ksepˣ))
    (mem_fixedField_of_forall_subgroupOf h fun n => congrArg (fun w : Additive Ksepˣ => ((w.toMul : Ksepˣ) : Ksep))
      (v.2 n)))
  left_inv _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  right_inv _ := Subtype.ext (Additive.toMul.injective (Units.ext rfl))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Units.ext rfl))

noncomputable def rootsInvariantsOpenEquiv (l : ℕ) :
    (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))).ρ.invariants ≃+
      TorsN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l where
  toFun ζ := ⟨Additive.ofMul (unitOfMemFixedField ((Additive.toMul (ζ : Additive (rootsOfUnity l Ksep)) :
        rootsOfUnity l Ksep) : Ksepˣ)
      (mem_fixedField_of_forall_subgroupOf h fun n => congrArg
        (fun w : Additive (rootsOfUnity l Ksep) => (((w.toMul : rootsOfUnity l Ksep) : Ksepˣ) : Ksep)) (ζ.2 n))),
    (mem_ker_lsmul_iff l _).2 (Additive.toMul.injective (Units.ext (Subtype.ext (by
      change ((((Additive.toMul (ζ : Additive (rootsOfUnity l Ksep)) : rootsOfUnity l Ksep) : Ksepˣ) ^ l :
        Ksepˣ) : Ksep) = 1
      exact (congrArg Units.val ((mem_rootsOfUnity l _).1
        (Additive.toMul (ζ : Additive (rootsOfUnity l Ksep))).2)).trans Units.val_one))))⟩
  invFun x := ⟨Additive.ofMul ⟨Units.map (algebraMap (fixedField (V : Subgroup Gal(Ksep/K))) Ksep : _ →* Ksep)
        ((x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul),
      (mem_rootsOfUnity l _).2 (by
        have hx : l • (x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) = 0 :=
          (mem_ker_lsmul_iff l _).1 x.2
        rw [← map_pow]
        have : ((x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul) ^ l = 1 :=
          congrArg Additive.toMul hx
        rw [this, map_one])⟩,
    fun n => congrArg Additive.ofMul (Subtype.ext (Units.ext
      (subgroupOf_apply_of_mem_fixedField
        (((x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul : fixedField (V : Subgroup Gal(Ksep/K)))).2 n)))⟩
  left_inv ζ := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext rfl)))
  right_inv x := Subtype.ext (Additive.toMul.injective (Units.ext (Subtype.ext rfl)))
  map_add' a b := Subtype.ext (Additive.toMul.injective (Units.ext (Subtype.ext rfl)))

end Invariants

section Equivariance

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)

noncomputable def cohomologyZeroRootsEquiv (l : ℕ) :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 0 ≃+
      TorsN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l :=
  (H0Iso _).toLinearEquiv.toAddEquiv.trans (rootsInvariantsOpenEquiv h l)

variable [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]


omit [IsSepClosure K Ksep] in
theorem unitsInvariantsOpenEquiv_smul (g : (U : Subgroup Gal(Ksep/K)))
    (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    unitsInvariantsOpenEquiv h (fixedFieldConjHom h g • u) =
      invariantsConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep))
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) g (unitsInvariantsOpenEquiv h u) :=
  Subtype.ext (Additive.toMul.injective (Units.ext rfl))


omit [IsSepClosure K Ksep] in
theorem rootsInvariantsOpenEquiv_invariantsConj (l : ℕ) (g : (U : Subgroup Gal(Ksep/K)))
    (ζ : (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))).ρ.invariants) :
    rootsInvariantsOpenEquiv h l (invariantsConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) g ζ) =
      torsNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldConjHom h g)
        (rootsInvariantsOpenEquiv h l ζ) :=
  Subtype.ext (Additive.toMul.injective (Units.ext (Subtype.ext rfl)))

theorem cohomologyZeroRootsEquiv_cohomologyConj (l : ℕ) (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 0) :
    cohomologyZeroRootsEquiv h l ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 0 g).hom x) =
      torsNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldConjHom h g)
        (cohomologyZeroRootsEquiv h l x) := by
  exact (congrArg (rootsInvariantsOpenEquiv h l) (H0Iso_hom_cohomologyConj _ _ g x)).trans
    (rootsInvariantsOpenEquiv_invariantsConj h l g _)

end Equivariance

section Kummer

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) {l : ℕ} (hl : (l : K) ≠ 0)

noncomputable def kummerOpenHom :
    Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ →+
      cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1 :=
  ((δ (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
      (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)))).inv.hom.toAddMonoidHom).comp
    (unitsInvariantsOpenEquiv h).toAddMonoidHom

theorem kummerOpenHom_apply (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    kummerOpenHom h hl u = (δ (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) 0 1 rfl).hom
      ((H0Iso (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)))).inv.hom
        (unitsInvariantsOpenEquiv h u)) :=
  rfl


include hl in
theorem kummerOpenHom_surjective : Function.Surjective (kummerOpenHom (l := l) h hl) := by
  intro x
  obtain ⟨v, hv⟩ := exists_δ_H0Iso_inv_eq (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
    ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))))
    (subsingleton_cohomology_one_galUnits_subgroupOf h) x
  obtain ⟨u, rfl⟩ := (unitsInvariantsOpenEquiv h).surjective v
  exact ⟨u, hv⟩


include hl in
theorem kummerOpenHom_eq_zero_iff (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    kummerOpenHom h hl u = 0 ↔ ∃ w, l • w = u := by
  rw [kummerOpenHom_apply]
  refine (δ_H0Iso_inv_eq_zero_iff (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
    ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) _).trans ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := (unitsInvariantsOpenEquiv h).surjective w
    refine ⟨w, (unitsInvariantsOpenEquiv h).injective ?_⟩
    rw [← hw, map_nsmul]
    apply Subtype.ext
    exact (nsmul_id_hom_apply (galUnits.{0} K Ksep) l _).symm
  · rintro ⟨w, rfl⟩
    refine ⟨unitsInvariantsOpenEquiv h w, ?_⟩
    rw [map_nsmul]
    apply Subtype.ext
    exact nsmul_id_hom_apply (galUnits.{0} K Ksep) l _

include hl in
theorem range_lsmul_eq_ker_kummerOpenHom :
    LinearMap.range (LinearMap.lsmul ℤ (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) (l : ℤ)) =
      LinearMap.ker (kummerOpenHom (l := l) h hl).toIntLinearMap := by
  ext u
  rw [LinearMap.mem_range, LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap,
    kummerOpenHom_eq_zero_iff]
  simp only [LinearMap.lsmul_apply, natCast_zsmul]

noncomputable def kummerOpenModNHom :
    ModN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l →ₗ[ℤ]
      cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1 :=
  (LinearMap.range (LinearMap.lsmul ℤ (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) (l : ℤ))).liftQ
    (kummerOpenHom h hl).toIntLinearMap (range_lsmul_eq_ker_kummerOpenHom h hl).le

include hl in
theorem kummerOpenModNHom_bijective : Function.Bijective (kummerOpenModNHom (l := l) h hl) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, kummerOpenModNHom, Submodule.ker_liftQ_eq_bot']
    exact range_lsmul_eq_ker_kummerOpenHom h hl
  · intro x
    obtain ⟨u, rfl⟩ := kummerOpenHom_surjective h hl x
    exact ⟨Submodule.Quotient.mk u, rfl⟩

noncomputable def cohomologyOneRootsEquiv :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1 ≃+
      ModN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l :=
  (AddEquiv.ofBijective (kummerOpenModNHom h hl).toAddMonoidHom (kummerOpenModNHom_bijective h hl)).symm

theorem cohomologyOneRootsEquiv_symm_mk (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    (cohomologyOneRootsEquiv h hl).symm (Submodule.Quotient.mk u) = kummerOpenHom h hl u :=
  rfl

theorem cohomologyOneRootsEquiv_kummerOpenHom (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    cohomologyOneRootsEquiv h hl (kummerOpenHom h hl u) = Submodule.Quotient.mk u := by
  rw [← cohomologyOneRootsEquiv_symm_mk, AddEquiv.apply_symm_apply]

variable [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

theorem kummerOpenHom_smul (g : (U : Subgroup Gal(Ksep/K)))
    (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    kummerOpenHom h hl (fixedFieldConjHom h g • u) =
      (cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 1 g).hom (kummerOpenHom h hl u) := by
  rw [kummerOpenHom_apply, kummerOpenHom_apply, unitsInvariantsOpenEquiv_smul]
  exact δ_H0Iso_inv_invariantsConj _ (shortExact_map_res (U : Subgroup Gal(Ksep/K))
    (kummerSequence_shortExact l hl)) g _

theorem cohomologyOneRootsEquiv_cohomologyConj (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1) :
    cohomologyOneRootsEquiv h hl ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 1 g).hom x) =
      modNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldConjHom h g)
        (cohomologyOneRootsEquiv h hl x) := by
  obtain ⟨u, rfl⟩ := kummerOpenHom_surjective h hl x
  rw [← kummerOpenHom_smul, cohomologyOneRootsEquiv_kummerOpenHom, cohomologyOneRootsEquiv_kummerOpenHom,
    modNRep_mk]

end Kummer

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyGal
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IntermediateField

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)
  [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

noncomputable def fixedFieldGalHom :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    (U : Subgroup Gal(Ksep/K)) →* (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
      fixedField (V : Subgroup Gal(Ksep/K))) :=
  letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  { toFun := fun g => AlgEquiv.ofRingEquiv (f := (fixedFieldConj h g).toRingEquiv) fun e =>
      Subtype.ext ((mem_fixedField_iff _ _).1 e.2 g g.2)
    map_one' := AlgEquiv.ext fun _ => Subtype.ext rfl
    map_mul' := fun _ _ => AlgEquiv.ext fun _ => Subtype.ext rfl }

theorem fixedFieldGalHom_surjective : Function.Surjective (fixedFieldGalHom h) := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))) Ksep :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) Ksep :=
    IsGalois.tower_top_of_isGalois K (fixedField (U : Subgroup Gal(Ksep/K))) Ksep
  intro σ
  set τ := σ.liftNormal Ksep
  have hτU : τ.restrictScalars K ∈ (U : Subgroup Gal(Ksep/K)) :=
    (fixingSubgroup_fixedField_openSubgroup U).le
      ((mem_fixingSubgroup_iff _ _).2 fun x hx => τ.commutes ⟨x, hx⟩)
  exact ⟨⟨τ.restrictScalars K, hτU⟩, AlgEquiv.ext fun x => Subtype.ext (σ.liftNormal_commutes Ksep x)⟩

theorem fixedFieldGalHom_ker :
    (fixedFieldGalHom h).ker = (V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)) := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    exact (fixingSubgroup_fixedField_openSubgroup V).le ((mem_fixingSubgroup_iff _ _).2 fun x hx =>
      congrArg Subtype.val (AlgEquiv.ext_iff.1 hg ⟨x, hx⟩))
  · intro hg
    exact AlgEquiv.ext fun x => Subtype.ext ((mem_fixedField_iff _ _).1 x.2 _ hg)

noncomputable def quotientFixedFieldGalEquiv :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    (U : Subgroup Gal(Ksep/K)) ⧸ (V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)) ≃*
      (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
        fixedField (V : Subgroup Gal(Ksep/K))) :=
  letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  (QuotientGroup.quotientMulEquivOfEq (fixedFieldGalHom_ker h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fixedFieldGalHom_surjective h))

theorem quotientFixedFieldGalEquiv_mk (g : (U : Subgroup Gal(Ksep/K))) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    quotientFixedFieldGalEquiv h (g : (U : Subgroup Gal(Ksep/K)) ⧸
      (V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) = fixedFieldGalHom h g :=
  rfl

theorem cohomologyZeroRootsEquiv_cohomologyConj_gal (l : ℕ) (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 0) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    cohomologyZeroRootsEquiv h l ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 0 g).hom x) =
      torsNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
          fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldGalHom h g)
        (cohomologyZeroRootsEquiv h l x) :=
  cohomologyZeroRootsEquiv_cohomologyConj h l g x

theorem cohomologyOneRootsEquiv_cohomologyConj_gal {l : ℕ} (hl : (l : K) ≠ 0) (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    cohomologyOneRootsEquiv h hl ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 1 g).hom x) =
      modNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
          fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldGalHom h g)
        (cohomologyOneRootsEquiv h hl x) := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  rw [cohomologyOneRootsEquiv_cohomologyConj]
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective _ (cohomologyOneRootsEquiv h hl x)
  rw [← hu]
  rfl

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {l : ℕ} (hl : (l : K) ≠ 0)

section Open

noncomputable def rootsOfUnityTwoInv (l : ℕ) (V : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)) 2 →+ QZ :=
  ((localClassFormationOfIsSepClosure K Ksep).inv V).comp
    (cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K))).f 2).hom.toAddMonoidHom

theorem rootsOfUnityTwoInv_apply (V : OpenSubgroup Gal(Ksep/K))
    (x : cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)) 2) :
    rootsOfUnityTwoInv l V x = (localClassFormationOfIsSepClosure K Ksep).inv V
      ((cohomologyMap (kummerSequenceRes (K := K) (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K))).f 2).hom x) :=
  AddMonoidHom.comp_apply _ _ x


include hl in
theorem rootsOfUnityTwoInv_injective (V : OpenSubgroup Gal(Ksep/K)) :
    Function.Injective (rootsOfUnityTwoInv (K := K) (Ksep := Ksep) l V) :=
  ((localClassFormationOfIsSepClosure K Ksep).inv_bijective V).1.comp
    (cohomologyMap_f_injective_of_subsingleton
      (kummerSequenceRes_shortExact (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K)) hl) 1
      (subsingleton_cohomology_one_galUnits_open K Ksep V))


include hl in
theorem range_rootsOfUnityTwoInv (V : OpenSubgroup Gal(Ksep/K)) :
    (rootsOfUnityTwoInv (K := K) (Ksep := Ksep) l V).range = (zmodToQZ l).range := by
  have : NeZero l := ⟨by rintro rfl; exact hl Nat.cast_zero⟩
  set F := localClassFormationOfIsSepClosure K Ksep
  set S := kummerSequenceRes (K := K) (Ksep := Ksep) l (V : Subgroup Gal(Ksep/K))
  have hS : S.ShortExact := kummerSequenceRes_shortExact l _ hl
  ext q
  simp only [AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine exists_zmodToQZ_eq ?_
    have e : l • (cohomologyMap S.f 2).hom x = 0 :=
      (cohomologyMap_kummerSequenceRes_g_apply l (V : Subgroup Gal(Ksep/K)) 2 _).symm.trans
        (cohomologyMap_g_cohomologyMap_f_apply (S := S) 2 x)
    rw [rootsOfUnityTwoInv_apply]
    exact (map_nsmul (F.inv V) l _).symm.trans ((congrArg (F.inv V) e).trans (map_zero _))
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := (F.inv_bijective V).2 (zmodToQZ l a)
    have hny : l • y = 0 := by
      apply (F.inv_bijective V).1
      rw [map_nsmul, hy, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero, map_zero]
    obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hS 2 y
      ((cohomologyMap_kummerSequenceRes_g_apply l (V : Subgroup Gal(Ksep/K)) 2 y).trans hny)
    exact ⟨x, (rootsOfUnityTwoInv_apply V x).trans ((congrArg (F.inv V) hx).trans hy)⟩

noncomputable def rootsOfUnityTwoEquivOpen (V : OpenSubgroup Gal(Ksep/K)) :
    cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)) 2 ≃+ ZMod l :=
  haveI : NeZero l := ⟨by rintro rfl; exact hl Nat.cast_zero⟩
  (AddMonoidHom.ofInjective (rootsOfUnityTwoInv_injective hl V)).trans
    ((AddEquiv.addSubgroupCongr (range_rootsOfUnityTwoInv hl V)).trans
      (AddMonoidHom.ofInjective (zmodToQZ_injective (n := l))).symm)

end Open

variable {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)

noncomputable def cohomologyTwoRootsEquiv :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 2 ≃+ ZMod l :=
  (asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe
      (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)).symm.toMonoidHom
    (continuous_subgroupOfEquivOfLe_symm _) (resSubgroupOfHom _ (galRootsOfUnity.{0} K Ksep l)) 2)).toLinearEquiv.toAddEquiv.trans
    (rootsOfUnityTwoEquivOpen hl V)

variable [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

theorem cohomologyTwoRootsEquiv_cohomologyConj (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 2) :
    cohomologyTwoRootsEquiv hl h ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 2 g).hom x) =
      cohomologyTwoRootsEquiv hl h x := by
  rw [cohomologyConj_two_galRootsOfUnity_eq_id hl h g]
  rfl

end GroundTheory.ProfCoh
