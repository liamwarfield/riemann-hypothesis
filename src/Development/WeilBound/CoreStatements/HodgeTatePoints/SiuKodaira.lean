module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaKodOf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne
public import Development.WeilBound.CoreStatements.HodgeTatePoints.SiubOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.SiuSegre
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siub

theorem siu_segre :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 :=
  siu_segre_of PositivityTheory.HtPt.Siua.siu_num

end PositivityTheory.HtPt.Siub
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siua

theorem siu_kodaira : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement :=
  siu_kodaira_of PositivityTheory.HtPt.Siub.siu_segre

end PositivityTheory.HtPt.Siua
