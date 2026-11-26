module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam

@[expose] public section

namespace PositivityTheory.RgDs

export CompanionTheory.RgDs (ExplicitFunctionSquareIntegrable InCone KeyFor Key Hilb)

theorem inCone_refl {n : ℕ} (abelian₂ : Fin n → ℝ) : InCone abelian₂ abelian₂ := ⟨0, by simp, by simp⟩

end PositivityTheory.RgDs
