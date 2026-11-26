module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def ratioField (x : Cone n (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    (Set.range fun p : (k : ι) × Fin (n k + 1) × Fin (n k + 1) ↦ x p.1 p.2.1 / x p.1 p.2.2)

theorem ratioField_le_coordField (x : Cone n (AlgebraicClosure ℚ)) :
    ratioField x ≤ coordField x := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨p, rfl⟩
  exact div_mem (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.1⟩, rfl⟩)
    (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.2⟩, rfl⟩)

theorem div_mem_ratioField (x : Cone n (AlgebraicClosure ℚ)) (k : ι) (i j : Fin (n k + 1)) :
    x k i / x k j ∈ ratioField x :=
  IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i, j⟩, rfl⟩

variable [Fintype ι]

instance (x : Cone n (AlgebraicClosure ℚ)) : FiniteDimensional ℚ (ratioField x) :=
  IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral_algebraicClosure_rat y

instance (x : Cone n (AlgebraicClosure ℚ)) : NumberField (ratioField x) := {}

def orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x)) :
    Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span {F | ∃ d : ι → ℕ, Geo.IsMultiHomog (ι := blockIdx n) F d ∧
    v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k}

variable [DecidableEq ι]

theorem X_mem_orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x))
    (k : ι) (i : Fin (n k + 1)) (hi : v (coordVec x k i) < ⨆ j, v (coordVec x k j)) :
    (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∈ orbitCenter x v := by
  refine Ideal.subset_span ⟨coordDeg n ⟨k, i⟩, (geoMultiHomog_iff _ _).mpr
    (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, i⟩), ?_⟩
  simpa [evalCone, coordDeg, Pi.single_apply, pow_ite] using hi

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → 0 < Geo.degC (ι := blockIdx n) (orbitIdeal x)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitCurve.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def HeightRecR.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (I : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) * height A x

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDivVertical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitDivVertical.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ¬ Geo.IsHorizontal (ι := blockIdx n) V

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitArchSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitArchSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ σ : coordField x →+* ℂ,
          Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
            A.metric (fun k i ↦ σ (coordVec x k i)))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitFiniteSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitFiniteSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
      (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) / Module.finrank ℚ (coordField x) *
        ∑ᶠ v : FinitePlace (coordField x),
          (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)))

end GroundTheory.Heights₂.Heights
end
