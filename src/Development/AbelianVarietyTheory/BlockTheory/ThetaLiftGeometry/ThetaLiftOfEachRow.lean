module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes
open Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

def AgreeAtAlmostAllSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) : Prop :=
  {w : PlE H | IsSplitPl H w ∧ A.locG χ w ≠ A.locG χ' w}.Finite

def HeckeCharEqOfSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ χ χ' : A.CG 1, AgreeAtAlmostAllSplit A χ χ' → χ = χ'

theorem agreeAtAlmostAllSplit_iff {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) :
    AgreeAtAlmostAllSplit A χ χ' ↔
      ∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locG χ w = A.locG χ' w := by
  simp only [AgreeAtAlmostAllSplit, Filter.eventually_cofinite, Classical.not_imp]

end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.NoLocalInvariants
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def eps (i : N.Loc) : G H.E N.Om →* (N.O i)ˣ :=
  (Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom).comp
    (cycZ (F := H.E) (Ω := N.Om) (N.l i))

end GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
end
end
