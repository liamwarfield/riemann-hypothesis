module

public import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
public import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCount
noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

variable (D : D7) {Dall Dgood : ℕ}

def CountCylAt (A : AllRowsAt D Dall Dgood) (c₃ : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    |(A.dimT (cyl D k S) : ℝ) -
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) *
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))

end Formalism.MainNotions.N.CylinderCountFamily
end
end

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas

variable (D : D7) {Dall Dgood : ℕ}

def PCountTie (A : AllRowsAt D Dall Dgood) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    Formalism.MainNotions.S.CountE.PCount A.B.I A.B.μf (D.host.g (1 - k)) (A.eT (cyl D k S))

theorem countCylAt_of (A : AllRowsAt D Dall Dgood) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (h1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb)
    (hT : TieCountAt A n₀ Alev C₃ cb) (hP : PCountTie D A) : CountCylAt D A c₃ := by
  intro k S
  obtain ⟨b, h, hST, hgap, hC, hlf, hlb, -⟩ := hT
  exact h1 A.B.I b A.B.lam A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) _ A.B.σ A.B.w _ A.B.σs A.B.tens
    A.B.μf A.B.fund A.B.R (A.ReT (cyl D k S)) h (hST k S).1 (hP k S) (hST k S).2 hgap hC hlf hlb

end Formalism.MainNotions.N.CylinderCountFamily
