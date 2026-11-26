module

public import GroundTheory.LocalFields.NormCorrespondence
public import GroundTheory.LocalFields.ConductorReciprocity

@[expose] public section

section -- merged from GroundTheory.LocalFields.LocalArtinCompletion
section -- merged from GroundTheory.LocalFields.OpenCompletion
namespace GroundTheory.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}


variable {G} in
def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h


def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]

namespace openCompletion

variable {G}






theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

end openCompletion

end Completion

end GroundTheory.LocalField
end

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_eq_of_le {E E' : IntermediateField F Ω} [Normal F E] [Normal F E']
    (hE' : E' ≤ maximalAbelianExtension F Ω) (hEE' : E ≤ E')
    {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : restrictAb E' hE' σ = restrictAb E' hE' τ) :
    restrictAb E (hEE'.trans hE') σ = restrictAb E (hEE'.trans hE') τ := by
  ext y
  have := congrArg (fun ρ : E' ≃ₐ[F] E' => ((ρ ⟨y, hEE' y.2⟩ : E') : Ω)) h
  simp only [restrictAb_apply] at this ⊢
  exact this

end Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section ClassField


variable (K Ω) in
def classField (H : openFiniteIndex Kˣ) : finiteAbelianExtensions K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual ⟨H.1, H.2⟩)

theorem range_normUnits_classField (H : openFiniteIndex Kˣ) :
    (normUnits K (classField K Ω H : IntermediateField K Ω)).range = H.1 :=
  congrArg (fun y => (OrderDual.ofDual y).1)
    ((normGroupOrderIso K Ω).apply_symm_apply (OrderDual.toDual ⟨H.1, H.2⟩))

end ClassField

section Coord


variable (K Ω) in
def artinCoord (H : openFiniteIndex Kˣ) :
    (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* Kˣ ⧸ H.1 :=
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField H)).toMonoidHom.comp
    ((localReciprocityAbelian (classField K Ω H : IntermediateField K Ω)).toMonoidHom.comp
      (restrictAb _ (le_maximalAbelianExtension _)))

theorem artinCoord_eq_of (H : openFiniteIndex Kˣ)
    (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) (x : Kˣ)
    (h : have := (classField K Ω H).2.1; have := (classField K Ω H).2.2
      restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) σ =
        restrictAb _ (le_maximalAbelianExtension _) (localArtinMap K Ω x)) :
    artinCoord K Ω H σ = (x : Kˣ ⧸ H.1) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  simp only [artinCoord, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, restrictAb_localArtinMap, MulEquiv.apply_symm_apply, QuotientGroup.quotientMulEquivOfEq_mk]

theorem artinCoord_localArtinMap (H : openFiniteIndex Kˣ) (x : Kˣ) :
    artinCoord K Ω H (localArtinMap K Ω x) = (x : Kˣ ⧸ H.1) :=
  artinCoord_eq_of H _ x rfl

theorem continuous_artinCoord (H : openFiniteIndex Kˣ) : Continuous (artinCoord K Ω H) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  change Continuous ((fun ρ => (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField (Ω := Ω) H)).toFun
    (localReciprocityAbelian (classField K Ω H : IntermediateField K Ω) ρ)) ∘
      restrictAb _ (le_maximalAbelianExtension _))
  exact continuous_of_discreteTopology.comp (continuous_restrictAb _ _)

end Coord

section Completion



end Completion

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.ConductorMatch
noncomputable section

open ValuativeRel

namespace GroundTheory.LocalField

section Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]

def conductor : ℕ :=
  sInf {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}

theorem conductor_le_iff [IsSepClosure K Ω] (n : ℕ) :
    conductor L ≤ n ↔ unitFiltrationUnits K n ≤ (normUnits K L).range := by
  have hne : {n : ℕ | unitFiltrationUnits K n ≤ (normUnits K L).range}.Nonempty :=
    exists_unitFiltrationUnits_le (isOpen_range_normUnits_and_finiteIndex L).1
  constructor
  · intro h
    exact (unitFiltrationUnits_antitone h).trans (Nat.sInf_mem hne)
  · intro h
    exact Nat.sInf_le h

end Def

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

section Conductor

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem unitFiltrationUnits_le_range_normUnits_iff (n : ℕ) :
    unitFiltrationUnits K n ≤ (normUnits K L).range ↔ upperRamificationGroup K L n = ⊥ := by
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap L n, Subgroup.map_eq_bot_iff,
    ker_restrictAb_localArtinMap]

theorem upperRamificationGroup_natCast_eq_bot_iff (n : ℕ) :
    upperRamificationGroup K L n = ⊥ ↔ conductor L ≤ n := by
  rw [conductor_le_iff, unitFiltrationUnits_le_range_normUnits_iff]

end Conductor

section Ab


end Ab

end GroundTheory.LocalField
end
end
