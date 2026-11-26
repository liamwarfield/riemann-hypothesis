module

public import Formalism.RealPlaceAnalysis.StatementKT
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

@[expose] public section

section -- merged from Formalism.RealPlaceAnalysis.StatementE
open Finset

noncomputable section

namespace Formalism.REAL

def Tm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) : A :=
  (if a = b then algebraMap ℂ A u else 0) + E a b

def qminor {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod

def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E id id u

def QSkewRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n)
    (τ : Equiv.Perm (Fin t)) (u : ℂ),
    qminor E (a ∘ τ) b u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u

def QSkewCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (τ : Equiv.Perm (Fin t)) (u : ℂ),
      qminor E a (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u

def QDetCentral : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (u : ℂ) (c d : Fin n), qdet E u * E c d = E c d * qdet E u

def QDetHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ u : ℂ, qdet E u v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v

def QComatrix : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
    ∀ (u : ℂ) (i l : Fin (m + 1)),
      ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
          qminor E (Fin.succAbove j) (Fin.succAbove i) u * Tm E (u - (m : ℂ)) j l =
        if i = l then qdet E u else 0

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
open MeasureTheory

noncomputable section

namespace Formalism.REAL

instance instLocallyCompactUJ (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) :=
  uJLocCompact_of isClosedEmbeddingMatrix n ε

instance instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _

instance instBorelSpaceUJ (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩

instance instSecondCountableUJ (n : ℕ) (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbeddingMatrix n ε).1.isInducing.secondCountableTopology

def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) := Measure.haar

instance instIsHaarMuG (n : ℕ) (ε : Fin n → Bool) : (muG ε).IsHaarMeasure := by
  unfold muG; infer_instance

def hsG {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ :=
  hs ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def Unimodular : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε), Measure.map (fun x => x * g) (muG ε) = muG ε

def InvInvariant : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), Measure.map (fun x : UJ ε => x⁻¹) (muG ε) = muG ε

def BallFinite : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : ℝ), muG ε {g | hsG g ≤ R} < ⊤

def VolGrowth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2))

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.StatementC
open Finset

noncomputable section

namespace Formalism.REAL

def cyc {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W}

def CharId : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, ∀ a b : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b x = 0

end Formalism.REAL
end
end
