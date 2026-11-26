module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible.GLNegationOpposite

open Formalism.REAL Formalism.HermitianLatticeCounting.P MulOpposite

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}


omit [Algebra ℂ A] in
private theorem glRel_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => op (X j i) := _root_.GlobalTheory.CapPair.glRel_op h

private theorem qdet_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (y : ℂ) :
    qdet (fun i j => op (X j i)) y = op (qdet X y) := _root_.GlobalTheory.CapPair.qdet_op h y

private theorem qdet_antipode {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (x : ℂ) :
    qdet (fun i j => -op (X i j)) x = op ((-1 : ℂ) ^ n • qdet X ((n : ℂ) - 1 - x)) := _root_.GlobalTheory.CapPair.qdet_antipode h x

omit [Algebra ℂ A] in
private theorem glRel_negOp {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) :
    Formalism.REAL.GlRel fun i j => -op (X i j) := by
  intro a b c d
  have h1 := congrArg op (h c d a b)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  simp only [neg_mul_neg]
  rw [h1]
  simp only [eq_comm (a := d) (b := a), eq_comm (a := b) (b := c)]
  split_ifs <;> abel

end UpperTheory.V.AlgRepEndIrreducible.GLNegationOpposite

theorem UpperTheory.V.AlgRepEndIrreducible.glNegOp :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
      Formalism.REAL.GlRel (fun i j => -MulOpposite.op (X i j)) ∧
      ∀ x : ℂ, Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) x =
        MulOpposite.op ((-1 : ℂ) ^ n • Formalism.REAL.qdet X ((n : ℂ) - 1 - x)) :=
  fun _ _ _ _ _ h => ⟨GLNegationOpposite.glRel_negOp h, fun x => GLNegationOpposite.qdet_antipode h x⟩
