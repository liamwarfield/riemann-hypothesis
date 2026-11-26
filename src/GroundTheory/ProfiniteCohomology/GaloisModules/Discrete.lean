module

public import GroundTheory.ProfiniteCohomology.FilteredHomology
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
namespace GroundTheory.ProfCoh

open IntermediateField

universe w u

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

section Topology

variable (K L)

theorem galois_compactSpace [IsGalois K L] : CompactSpace Gal(L/K) :=
  inferInstance

theorem galois_t2Space [Algebra.IsIntegral K L] : T2Space Gal(L/K) :=
  inferInstance

theorem galois_isProfinite [IsGalois K L] :
    CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧ TotallyDisconnectedSpace Gal(L/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Topology

section Open

theorem apply_eq_of_mem_fixingSubgroup_adjoin {x : L} {σ : Gal(L/K)}
    (hσ : σ ∈ (K⟮x⟯).fixingSubgroup) : σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (mem_adjoin_simple_self K x)

theorem isOpen_of_forall_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K)) (x : L)
    (h : ∀ σ : Gal(L/K), σ x = x → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact Subgroup.isOpen_mono (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ))
    (fixingSubgroup_isOpen K⟮x⟯)

end Open

section Discrete

variable [Algebra.IsIntegral K L]

instance isDiscreteRep_galAdd : IsDiscreteRep (galAdd K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galAddInt : IsDiscreteRep (galAddInt.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galUnits : IsDiscreteRep (galUnits.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnits_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩

instance isDiscreteRep_galUnitsZ : IsDiscreteRep (galUnitsZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnitsZ_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩

instance isDiscreteRep_galRootsOfUnity (n : ℕ) : IsDiscreteRep (galRootsOfUnity.{w} K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnity_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩

end Discrete

section Galois

variable (K L) [IsGalois K L]

end Galois

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
namespace GroundTheory.ProfCoh

open IntermediateField InfiniteGalois

universe u

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

section FixingSubgroup

theorem isOpen_fixingSubgroup_finiteGalois (E : FiniteGaloisIntermediateField K L) :
    IsOpen (E.fixingSubgroup : Set Gal(L/K)) :=
  fixingSubgroup_isOpen E.toIntermediateField

theorem normal_fixingSubgroup_finiteGalois [IsGalois K L] (E : FiniteGaloisIntermediateField K L) :
    E.fixingSubgroup.Normal :=
  (normal_iff_isGalois E.toIntermediateField).2 E.isGalois

variable [IsGalois K L]

def fixingOpenNormalSubgroup (E : FiniteGaloisIntermediateField K L) :
    OpenNormalSubgroup Gal(L/K) where
  toSubgroup := E.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_finiteGalois E
  isNormal' := normal_fixingSubgroup_finiteGalois E

end FixingSubgroup

section FixedField

variable [IsGalois K L] (U : OpenNormalSubgroup Gal(L/K))

def openNormalToClosed : ClosedSubgroup Gal(L/K) :=
  ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩

instance : (openNormalToClosed U).Normal :=
  U.isNormal'

@[simp]
theorem fixingSubgroup_fixedField_openNormalSubgroup :
    (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup = U :=
  fixingSubgroup_fixedField (openNormalToClosed U)

instance finiteDimensional_fixedField_openNormalSubgroup :
    FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (isOpen_iff_finite _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isOpen

instance isGalois_fixedField_openNormalSubgroup :
    IsGalois K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (normal_iff_isGalois _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isNormal'

noncomputable def fixedFiniteGalois : FiniteGaloisIntermediateField K L where
  toIntermediateField := fixedField (U : Subgroup Gal(L/K))

noncomputable def quotientEquivGal :
    Gal(L/K) ⧸ (U : Subgroup Gal(L/K)) ≃* Gal(fixedField (U : Subgroup Gal(L/K))/K) :=
  normalAutEquivQuotient (openNormalToClosed U)

@[simp]
theorem quotientEquivGal_mk_apply (σ : Gal(L/K)) (x : fixedField (U : Subgroup Gal(L/K))) :
    ((quotientEquivGal U (σ : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) x : _) : L) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x


omit [IsGalois K L] in
theorem mem_invariants_galAdd_iff (x : L) :
    x ∈ Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ↔
      x ∈ fixedField (U : Subgroup Gal(L/K)) :=
  ⟨fun h σ => h σ, fun h σ => h σ⟩


omit [IsGalois K L] in
def invariantsGalAddEquiv :
    Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ≃ₗ[K]
      fixedField (U : Subgroup Gal(L/K)) where
  toFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).1 x.2⟩
  invFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem invariantsGalAddEquiv_quotientToInvariants (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (x : Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsGalAddEquiv U (((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q x) =
      quotientEquivGal U q (invariantsGalAddEquiv U x) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply Subtype.ext
    rw [quotientEquivGal_mk_apply]
    rfl

end FixedField

section Correspondence

variable [IsGalois K L]

@[simp]
theorem fixedFiniteGalois_fixingOpenNormalSubgroup
    (E : FiniteGaloisIntermediateField K L) : fixedFiniteGalois (fixingOpenNormalSubgroup E) = E :=
  FiniteGaloisIntermediateField.val_injective (fixedField_fixingSubgroup E.toIntermediateField)

end Correspondence

section Cofinal

variable [IsGalois K L]

theorem exists_finiteGalois_le (E : IntermediateField K L) [FiniteDimensional K E] :
    ∃ F : FiniteGaloisIntermediateField K L, E ≤ F.toIntermediateField :=
  ⟨{ toIntermediateField := normalClosure K E L
     finiteDimensional := normalClosure.is_finiteDimensional K E L
     isGalois := IsGalois.normalClosure K E L }, le_normalClosure E⟩

theorem exists_finiteGalois_mem (x : L) :
    ∃ F : FiniteGaloisIntermediateField K L, x ∈ F.toIntermediateField :=
  ⟨FiniteGaloisIntermediateField.adjoin K {x},
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩

end Cofinal

end GroundTheory.ProfCoh
end
