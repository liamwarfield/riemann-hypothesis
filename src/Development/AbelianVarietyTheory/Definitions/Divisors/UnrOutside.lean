module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open Classical in
def sat (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) : Multiset ℂˣ :=
  if h : ∃ B, π.HasSat w B then h.choose else 0

def UnrOutside (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CG E a) : Prop := ∀ w ∉ S, ∃ B, π.HasSat w B

def locL (q : ℕ) (B B' : Multiset ℂˣ) (s : ℂ) : ℂ :=
  ((B ×ˢ B').map fun p : ℂˣ × ℂˣ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-s))⁻¹).prod

def partialL (S : Finset (HeightOneSpectrum (𝓞 E))) {b : ℕ} (π : CG E a) (π' : CG E b) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) (sat π' w.1) s

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff

namespace GlobalTheory.HenQ

section Fin

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end Fin

section Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


open Classical in
def pdL (v : InfinitePlace K) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  fderiv ℝ F x (toL (Matrix.single i j (Pi.single v 1)))


def detD (v : InfinitePlace K) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr (fun j G => pdL v (p j) j G) F x

def IsTest (Φ : Lie K n → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ invSet K n

variable [IsTotallyReal K]

end Inf

end GlobalTheory.HenQ
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Filter Topology

noncomputable section

namespace GlobalTheory.FlagAr

open GlobalTheory.FlagPoly

variable {D : D7} (Y : ShimX D.what₂.Tau)

def setB (B : ℝ) : Finset ℕ :=
  ((Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime) ∪
    (Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ Y.lev)

end GlobalTheory.FlagAr
end
end
