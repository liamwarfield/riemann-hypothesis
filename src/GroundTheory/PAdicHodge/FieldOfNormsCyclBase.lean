module

public import GroundTheory.PAdicHodge.FieldOfNormsRam
public import GroundTheory.PAdicHodge.CyclotomicTower
public import GroundTheory.PAdicHodge.TiltAlgClosed
public import GroundTheory.LocalFields.KroneckerWeber

@[expose] public section

section -- merged from GroundTheory.PAdicHodge.FieldOfNormsResidue
section -- merged from GroundTheory.PAdicHodge.FieldOfNormsDef
section -- merged from GroundTheory.PAdicHodge.FieldOfNormsAPF
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

section GaloisAPF

variable {L : IntermediateField K Ω} [IsGalois K L]

variable (hL : IsAPF K Ω L)
include hL

end GaloisAPF

section Tower

variable {L : IntermediateField K Ω} [IsGalois K L] (hL : IsAPF K Ω L)
include hL

end Tower

section Construction

variable {L : IntermediateField K Ω} [IsGalois K L]

structure APFData (L : IntermediateField K Ω) where
  apf : IsAPF K Ω L
  c : ℝ
  c_pos : 0 < c
  u₀ : ℝ
  one_le_u₀ : 1 ≤ u₀
  le_psi : ∀ u, u₀ ≤ u → c * apfIndex K Ω L u ≤ apfPsi K Ω L u

namespace APFData

variable (d : APFData L)

def u (n : ℕ) : ℝ := d.u₀ + n * (d.c / 2)


end APFData

end Construction



namespace APFData

variable {L : IntermediateField K Ω} [IsGalois K L] (d : APFData L)


end APFData

end GroundTheory.PAdicHodge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

section Def

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] {L : IntermediateField K Ω}

variable (K Ω L) in
abbrev FinSub : Type _ := {E : IntermediateField K Ω // E ≤ L ∧ FiniteDimensional K E}

abbrev inclAlgebra {E E' : IntermediateField K Ω} (h : E ≤ E') : Algebra E E' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra


open Classical in
def relNorm {E E' : IntermediateField K Ω} (h : E ≤ E') (y : Ω) : Ω :=
  if hy : y ∈ E' then ((@Algebra.norm E E' _ _ (inclAlgebra h) ⟨y, hy⟩ : E) : Ω) else 0


variable (K Ω L) in
def FieldOfNorms : Type _ :=
  {x : FinSub K Ω L → Ω //
    (∀ E, x E ∈ E.1) ∧ ∀ E E' : FinSub K Ω L, ∀ h : E.1 ≤ E'.1, relNorm h (x E') = x E}

end Def

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p) (L : IntermediateField K Ω)

variable {t L}



end NormTower

end Tower

section GaloisNorm

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]

end GaloisNorm

section APF

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]

namespace APFData

variable (d : APFData L)

end APFData

end APF

end GroundTheory.PAdicHodge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField IsLocalRing

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}

namespace NormTower

variable (t : NormTower K Ω p)

end NormTower

end Tower

section FieldOfNorms

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]
  [hsapf : Fact (IsStrictlyAPF K Ω L)] [hinf : Fact (¬ FiniteDimensional K L)]

namespace FieldOfNorms

instance isLocalRing_integer_L : IsLocalRing 𝒪[L] :=
  inferInstanceAs (IsLocalRing (valuation L).valuationSubring)

end FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
end
end

section -- merged from GroundTheory.PAdicHodge.UntiltIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]



omit [NontriviallyNormedField K] [IsUltrametricDist K] [NontriviallyNormedField C] [NormedAlgebra K C]
  [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p] in
theorem norm_eq_of_norm_sub_lt {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rw [sub_add_cancel, max_eq_right h.le] at this
  exact this

end

end GroundTheory.PAdicHodge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace CyclNorms

open GroundTheory.LocalField ValuativeRel

variable (p : ℕ) [Fact p.Prime]

scoped instance padicAlgCl_valuativeRel : ValuativeRel (PadicAlgCl p) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := PadicAlgCl p))

variable {p}

theorem vle_iff_norm_le (x y : PadicAlgCl p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

scoped instance padicAlgCl_compatible : (NormedField.valuation (K := PadicAlgCl p)).Compatible :=
  Valuation.Compatible.ofValuation _

scoped instance padicAlgCl_isValuativeTopology : IsValuativeTopology (PadicAlgCl p) := by
  let : Valued (PadicAlgCl p) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (PadicAlgCl p) NNReal).Compatible := padicAlgCl_compatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

scoped instance padicAlgCl_valuativeExtension : ValuativeExtension ℚ_[p] (PadicAlgCl p) := by
  refine ⟨fun {a b} ↦ ?_⟩
  rw [vle_iff_norm_le, PadicAlgCl.norm_extends, PadicAlgCl.norm_extends,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le]

end CyclNorms

end GroundTheory.PAdicHodge
