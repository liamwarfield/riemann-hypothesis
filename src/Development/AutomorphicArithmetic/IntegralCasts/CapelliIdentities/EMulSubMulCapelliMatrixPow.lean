module

public import Mathlib

@[expose] public section

/-!
# Commutation Relations for Powers of the Capelli Matrix in `U(𝔤𝔩ₙ)`

Defines the matrix Lie algebra `𝔤𝔩ₙ(ℂ)`, its universal enveloping algebra `U(𝔤𝔩ₙ)`,
the canonical generators `e_{a,b} = ι(E_{a,b})`, and the Capelli matrix `(e_{i,j})`.
Proves by induction on `k` that `[e_{a,b}, (capelliMatrix ^ k)_{c,d}]` obeys the same
`𝔤𝔩ₙ`-commutation law `δ_{b,c} (M^k)_{a,d} - δ_{d,a} (M^k)_{c,b}`.
-/

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk36.gl (n : ℕ) : Type :=
  Matrix (Fin n) (Fin n) ℂ

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk36.U (n : ℕ) : Type :=
  letI : LieRing (UpperTheory.Reformulated.B.Qk36.gl n) := LieRing.ofAssociativeRing
  letI : LieAlgebra ℂ (UpperTheory.Reformulated.B.Qk36.gl n) := LieAlgebra.ofAssociativeAlgebra
  UniversalEnvelopingAlgebra ℂ (UpperTheory.Reformulated.B.Qk36.gl n)

noncomputable def UpperTheory.Reformulated.B.Qk36.E {n : ℕ} (a : Fin n × Fin n) :
    UpperTheory.Reformulated.B.Qk36.gl n :=
  Matrix.single a.1 a.2 1

noncomputable def UpperTheory.Reformulated.B.Qk36.e {n : ℕ} (a : Fin n × Fin n) :
    UpperTheory.Reformulated.B.Qk36.U n :=
  letI : LieRing (UpperTheory.Reformulated.B.Qk36.gl n) := LieRing.ofAssociativeRing
  letI : LieAlgebra ℂ (UpperTheory.Reformulated.B.Qk36.gl n) := LieAlgebra.ofAssociativeAlgebra
  UniversalEnvelopingAlgebra.ι ℂ (UpperTheory.Reformulated.B.Qk36.E a)

noncomputable def UpperTheory.Reformulated.B.Qk36.capelliMatrix {n : ℕ} :
    Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.Qk36.U n) :=
  fun i j => UpperTheory.Reformulated.B.Qk36.e (i, j)

private theorem UpperTheory.Reformulated.B.Qk36.commutator_matrix_pow {R : Type*} [Ring R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (x : R) (a b : Fin n)
    (h : ∀ c d, x * M c d - M c d * x
      = (if b = c then M a d else 0) - (if d = a then M c b else 0))
    (k : ℕ) (c d : Fin n) :
    x * (M ^ k) c d - (M ^ k) c d * x
      = (if b = c then (M ^ k) a d else 0) - (if d = a then (M ^ k) c b else 0) := by
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
      sub_self]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp [h1, h2, eq_comm (a := a), eq_comm (a := c)]
  | succ k ih =>
    have key : ∀ j, x * ((M ^ k) c j * M j d) - (M ^ k) c j * M j d * x
        = ((if b = c then (M ^ k) a j else 0) - (if j = a then (M ^ k) c b else 0)) * M j d
          + (M ^ k) c j * ((if b = j then M a d else 0) - (if d = a then M j b else 0)) := by
      intro j
      rw [← ih j, ← h j d]
      noncomm_ring
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun j _ => key j)]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : d = a <;>
      simp only [h1, h2, if_true, if_false, Finset.sum_const_zero] <;> abel

private theorem UpperTheory.Reformulated.B.Qk36.E_comm {n : ℕ} (a b c d : Fin n) :
    UpperTheory.Reformulated.B.Qk36.E (a, b) * UpperTheory.Reformulated.B.Qk36.E (c, d)
        - UpperTheory.Reformulated.B.Qk36.E (c, d) * UpperTheory.Reformulated.B.Qk36.E (a, b)
      = (if b = c then UpperTheory.Reformulated.B.Qk36.E (a, d) else 0)
        - (if d = a then UpperTheory.Reformulated.B.Qk36.E (c, b) else 0) := by
  have h : ∀ p q r s : Fin n,
      UpperTheory.Reformulated.B.Qk36.E (p, q) * UpperTheory.Reformulated.B.Qk36.E (r, s)
        = if q = r then UpperTheory.Reformulated.B.Qk36.E (p, s) else 0 := by
    intro p q r s
    unfold UpperTheory.Reformulated.B.Qk36.E
    split_ifs with hqr
    · subst hqr
      simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ hqr _
  rw [h, h]

private theorem UpperTheory.Reformulated.B.Qk36.e_comm {n : ℕ} (a b c d : Fin n) :
    UpperTheory.Reformulated.B.Qk36.e (a, b) * UpperTheory.Reformulated.B.Qk36.e (c, d)
        - UpperTheory.Reformulated.B.Qk36.e (c, d) * UpperTheory.Reformulated.B.Qk36.e (a, b)
      = (if b = c then UpperTheory.Reformulated.B.Qk36.e (a, d) else 0)
        - (if d = a then UpperTheory.Reformulated.B.Qk36.e (c, b) else 0) := by
  letI : LieRing (UpperTheory.Reformulated.B.Qk36.gl n) := LieRing.ofAssociativeRing
  letI : LieRing (UpperTheory.Reformulated.B.Qk36.U n) := LieRing.ofAssociativeRing
  unfold UpperTheory.Reformulated.B.Qk36.e
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie,
    LieRing.of_associative_ring_bracket, UpperTheory.Reformulated.B.Qk36.E_comm, map_sub]
  congr 1 <;> split_ifs <;> first | rfl | exact map_zero _

theorem UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow
    {n : ℕ} (a b : Fin n) (k : ℕ) (c d : Fin n) :
    UpperTheory.Reformulated.B.Qk36.e (a, b) *
          (UpperTheory.Reformulated.B.Qk36.capelliMatrix ^ k) c d -
        (UpperTheory.Reformulated.B.Qk36.capelliMatrix ^ k) c d *
          UpperTheory.Reformulated.B.Qk36.e (a, b) =
      (if b = c then (UpperTheory.Reformulated.B.Qk36.capelliMatrix ^ k) a d else 0) -
        if d = a then (UpperTheory.Reformulated.B.Qk36.capelliMatrix ^ k) c b else 0 :=
  UpperTheory.Reformulated.B.Qk36.commutator_matrix_pow
    UpperTheory.Reformulated.B.Qk36.capelliMatrix _ a b
    (fun c d => UpperTheory.Reformulated.B.Qk36.e_comm a b c d) k c d
