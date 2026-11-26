module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.InertDeltaFirstCaseEqPower

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FBL

def LpowMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w))
  (g : UL n w → ℂ), IsOpen (K' : Set (UL n w)) → K' ≤ KL n w → IsHecke K' g → ∀ m k : ℕ, U.lpow K' (U.lpow K' g m) k = U.lpow K' g (m * k)

def EllHom : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) [MeasurableSpace (GA E a)]
  [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (c : ℂ) (φ : GA E a × GA E b → ℂ),
    ellSum2 μ₁ μ₂ (c • φ) = c * ellSum2 μ₁ μ₂ φ

def NontrivInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → Nontrivial (InfinitePlace E)

end PositivityTheory.Rg.BcB.F.FBL

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BadEx2
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def fixFn (n a : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m : ℕ) (KB : Subgroup (UL n w)) : LF a (n - a) w :=
  if ha : a ≤ n then (if IsSplitAt w then ctMu (Nat.add_sub_cancel' ha) w μ (U.lone KB)
    else fun y => ((KB.relIndex (KL n w) : ℕ) : ℂ) * MB.pairIndicatorMatch n a (n - a) w m y) else 0

def BadEx2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a : ℕ), a ≤ n → ∀ (w : Pl E)
  (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) → ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ L : Subgroup (GLw a w × GLw (n - a) w), IsPairLevel L ∧ IsHecke L (fixFn n a w μ m KB) ∧
      Match n a (n - a) w μ (U.lone KB) (fixFn n a w μ m KB)

end PositivityTheory.Rg.BcB.F.Ex0

end
end
