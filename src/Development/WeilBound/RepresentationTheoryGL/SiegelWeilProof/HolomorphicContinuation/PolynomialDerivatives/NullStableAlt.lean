module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def cr (c : ℝ) (k : Fin m × Fin n × Bool) : Module.End ℂ (PX m n) :=
  if k.2.2 then -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, false) : PX m n)
  else -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, true) : PX m n)

def fockMono (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (cr c k) ^ (s k)).prod) 1

def fock (c : ℝ) (p : PX m n) : PX m n := ∑ s ∈ p.support, p.coeff s • fockMono c s

def Dop (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    ∑ i, (X (b, i, true) * pderiv (a, i, true) p - X (a, i, false) * pderiv (b, i, false) p)
  else
    ∑ i, ((2 * c : ℂ) • pderiv (b, i, false) (pderiv (a, i, true) p) - (1 / (2 * c) : ℂ) • (X (a, i, false) * X (b, i, true) * p))

def contr (c : ℝ) (p : PX m n) : ℂ :=
  ∑ s ∈ p.support, if ∀ a i, s (a, i, false) = s (a, i, true) then
    p.coeff s * ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

def KopL (ε : Fin m → Bool) (i j : Fin n) : Module.End ℂ (PX m n) :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = true), LinearMap.mulLeft ℂ (X (a, i, false) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, j, false)).toLinearMap -
    ∑ a ∈ Finset.univ.filter (fun a => ε a = false), LinearMap.mulLeft ℂ (X (a, j, true) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, i, true)).toLinearMap

def mulQ (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) : PX m n := Qp ε i j * P

def lapS (ε : Fin m → Bool) (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, i, false) (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P) -
    C (c : ℂ) * X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P))

def eulH (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, j, false) * (pderiv (a, i, false) P - C (c : ℂ) * X (a, i, true) * P)

def eulA (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P)

def kAlg (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2)

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def FockBasic : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → IsLinearMap ℂ (fock (m := m) (n := n) c) ∧ Function.Bijective (fock (m := m) (n := n) c) ∧
    ∀ k (p : PX m n), fock c (X k * p) = cr c k (fock c p)

def FockHOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (a b : Fin m) (p : PX m n),
    hOp ε c a b (fock c p) = fock c (Dop ε c a b p)

def FockMom : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → mom (m := m) (n := n) c 1 ≠ 0 ∧ ∀ p : PX m n, mom c (fock c p) = mom c (1 : PX m n) * contr c p

def NullStable : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (i j : Fin n) (P : PX m n), NullSec ε c P →
    NullSec ε c (lapS ε c i j P) ∧ NullSec ε c (eulH c i j P) ∧ NullSec ε c (eulA c i j P) ∧ NullSec ε c (mulQ ε i j P)

def FockK : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∃ a₁ a₂ a₃ a₄ a₅ : ℂ, ∀ (i j : Fin n) (p : PX m n),
    fock c (KopL ε i j p) = a₁ • mulQ ε i j (fock c p) + a₂ • lapS ε c i j (fock c p) + a₃ • eulH c i j (fock c p) +
      a₄ • eulA c i j (fock c p) + (if i = j then a₅ else 0) • fock c p

def CoreLC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ Λ : PX m n →ₗ[ℂ] ℂ, (∀ a b p, Λ (Dop ε c a b p) = 0) →
    ∀ p, ∃ w ∈ kAlg ε, Λ p = contr c (w p)

end PositivityTheory.Rg.Sw.LC
