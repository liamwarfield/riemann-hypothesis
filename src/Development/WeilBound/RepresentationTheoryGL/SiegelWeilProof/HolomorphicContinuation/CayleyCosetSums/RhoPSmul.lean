module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetSecondCayleyBlockNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperators
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DifferentiableHf
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseSecondBlockEqNegConjTranspose
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

private theorem mul_toBlocks₂₁_eq (g h : M2 n) :
    (g * h).toBlocks₂₁ = g.toBlocks₂₁ * h.toBlocks₁₁ + g.toBlocks₂₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

private theorem mul_toBlocks₂₂_eq (g h : M2 n) :
    (g * h).toBlocks₂₂ = g.toBlocks₂₁ * h.toBlocks₁₂ + g.toBlocks₂₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂]

private theorem mul_toBlocks₁₁' (g h : M2 n) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ + g.toBlocks₁₂ * h.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

private theorem mul_toBlocks₁₂ (g h : M2 n) :
    (g * h).toBlocks₁₂ = g.toBlocks₁₁ * h.toBlocks₁₂ + g.toBlocks₁₂ * h.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

private theorem conjTranspose_toBlocks (g : M2 n) :
    (gᴴ).toBlocks₁₁ = (g.toBlocks₁₁)ᴴ ∧ (gᴴ).toBlocks₁₂ = (g.toBlocks₂₁)ᴴ ∧
      (gᴴ).toBlocks₂₁ = (g.toBlocks₁₂)ᴴ ∧ (gᴴ).toBlocks₂₂ = (g.toBlocks₂₂)ᴴ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.conjTranspose_apply]

private theorem JJ_toBlocks :
    (JJ n).toBlocks₁₁ = 0 ∧ (JJ n).toBlocks₁₂ = 1 ∧ (JJ n).toBlocks₂₁ = -1 ∧ (JJ n).toBlocks₂₂ = 0 := by
  simp [JJ]

private theorem inK_toBlocks₂_eq {k : M2 n} (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have h2 : k * kᴴ = 1 := mul_eq_one_comm.mp hk.2
  have h3 : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [h2, Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ h3
  have e2 := congrArg Matrix.toBlocks₁₂ h3
  rw [mul_toBlocks₁₁', mul_toBlocks₁₁', j11, j12, j21] at e1
  rw [mul_toBlocks₁₂, mul_toBlocks₁₂, j11, j12, j22] at e2
  simp at e1 e2
  exact ⟨e1, e2⟩

private theorem neg_toBlocks₁₁_toBlocks₂₁ (g : M2 n) :
    (-g).toBlocks₁₁ = -g.toBlocks₁₁ ∧ (-g).toBlocks₂₁ = -g.toBlocks₂₁ := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

private theorem one_toBlocks₁₁_toBlocks₁₂ :
    (1 : M2 n).toBlocks₁₁ = 1 ∧ (1 : M2 n).toBlocks₁₂ = 0 := by
  refine ⟨?_, ?_⟩ <;> ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply]

private theorem inK_toBlocks₁_unitary_relations {k : M2 n} (hk : InK k) :
    (k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂ = 1 ∧
      (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂ = (k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  have hU : kᴴ * k = 1 := hk.2
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks k
  obtain ⟨o11, o12⟩ := (one_toBlocks₁₁_toBlocks₁₂ (n := n))
  have e1 := congrArg Matrix.toBlocks₁₁ hU
  have e2 := congrArg Matrix.toBlocks₁₂ hU
  rw [mul_toBlocks₁₁', c11, c12, hc, o11] at e1
  rw [mul_toBlocks₁₂, c11, c12, hc, hd, o12] at e2
  simp only [Matrix.conjTranspose_neg, neg_mul, mul_neg, neg_neg] at e1 e2
  refine ⟨e1, ?_⟩
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg] using e2

theorem first_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u1 (g * k) = u1 g * u1 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem second_cayley_block_mul_compact (g : M2 n) {k : M2 n} (hk : InK k) : u2 (g * k) = u2 g * u2 k := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hc, hd, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, Complex.I_mul_I]
  module

theorem first_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u1 k)ᴴ * u1 k = 1 := by
  obtain ⟨hc, hd⟩ := inK_toBlocks₂_eq hk
  obtain ⟨h1, h2⟩ := inK_toBlocks₁_unitary_relations hk
  have e : (u1 k)ᴴ * u1 k = ((k.toBlocks₁₁)ᴴ * k.toBlocks₁₁ + (k.toBlocks₁₂)ᴴ * k.toBlocks₁₂) +
      Complex.I • ((k.toBlocks₁₂)ᴴ * k.toBlocks₁₁ - (k.toBlocks₁₁)ᴴ * k.toBlocks₁₂) := by
    simp only [u1, hc, hd, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_neg,
      Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_neg, Matrix.neg_mul, smul_add, smul_neg, smul_smul, neg_smul, Complex.I_mul_I, neg_mul]
    module
  rw [e, h1, h2, sub_self, smul_zero, add_zero]

def eps (n : ℕ) : M2 n := fromBlocks 1 0 0 (-1)

theorem eps_sq : eps n * eps n = 1 := by
  simp [eps, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem eps_JJ : eps n * JJ n * eps n = -JJ n := by
  simp [eps, JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg]

theorem eps_conj : (eps n)ᴴ = eps n := by simp [eps, fromBlocks_conjTranspose]

theorem inK_eps {k : M2 n} (hk : InK k) : InK (eps n * k * eps n) := by
  have hG : kᴴ * JJ n * k = JJ n := hk.1
  have hU : kᴴ * k = 1 := hk.2
  have e : eps n * JJ n * eps n = -JJ n := eps_JJ
  refine ⟨?_, ?_⟩
  · show (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n) = JJ n
    calc (eps n * k * eps n)ᴴ * JJ n * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * JJ n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = -(eps n * (kᴴ * JJ n * k) * eps n) := by
          rw [e]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hG, e, neg_neg]
  · show (eps n * k * eps n)ᴴ * (eps n * k * eps n) = 1
    calc (eps n * k * eps n)ᴴ * (eps n * k * eps n)
        = eps n * (kᴴ * (eps n * eps n) * k) * eps n := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, eps_conj]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [eps_sq, Matrix.mul_one, hU, Matrix.mul_one, eps_sq]

theorem first_cayley_block_swap_conj (k : M2 n) : u1 (eps n * k * eps n) = u2 k := by
  simp [u1, u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, eps]

theorem second_cayley_block_compact_unitary {k : M2 n} (hk : InK k) : (u2 k)ᴴ * u2 k = 1 := by
  rw [← first_cayley_block_swap_conj]
  exact first_cayley_block_compact_unitary (inK_eps hk)

theorem second_cayley_block_inv_eq_conjTranspose {k : M2 n} (hk : InK k) : (u2 k)⁻¹ = (u2 k)ᴴ := Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk)

theorem inverse_second_block_eq_neg_conjTranspose {x : M2 n} (hx : InG x) : ub2 x = -(u2 x)ᴴ := by
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks x
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  obtain ⟨n11, n21⟩ := neg_toBlocks₁₁_toBlocks₂₁ (JJ n * xᴴ * JJ n)
  simp only [ub2, u2, inv_of_inG hx, n11, n21, mul_toBlocks₁₁', mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, mul_toBlocks₁₂,
    c11, c12, c21, c22,
    j11, j12, j21, j22, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_I, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_neg, neg_smul, smul_neg]
  module

theorem Om_K {k : M2 n} (hk : InK k) : Om k = -((u2 k)⁻¹ * u1 k) := by
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose hk.1, inverse_first_block_eq_conjTranspose hk.1, Matrix.inv_eq_left_inv (mul_eq_one_comm.mp (first_cayley_block_compact_unitary hk)),
    ← second_cayley_block_inv_eq_conjTranspose hk, Matrix.neg_mul]

theorem normSq_det_u1K {k : M2 n} (hk : InK k) : Complex.normSq (u1 k).det = 1 := by
  have h := congrArg Matrix.det (first_cayley_block_compact_unitary hk)
  rw [det_mul, det_conjTranspose, det_one] at h
  have h' : (Complex.normSq (u1 k).det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h
  exact_mod_cast h'

theorem fz_K (m : ℕ) (e : ℤ) (z : ℂ) {k : M2 n} (hk : InK k) : fz m e z k = fz m e 0 k := by
  have hd : (u1 k).det * (ub1 k).det = 1 := by
    rw [inverse_first_block_eq_conjTranspose hk.1, Matrix.det_conjTranspose, Complex.star_def, mul_comm,
      ← Complex.normSq_eq_conj_mul_self, normSq_det_u1K hk, Complex.ofReal_one]
  simp only [fz, hd, Complex.one_cpow, neg_zero, Complex.cpow_zero]

theorem first_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u1 (p * y) = p.toBlocks₂₂ * u1 y := by
  simp only [u1, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]

theorem second_cayley_block_upper_triangular_mul {p : M2 n} (hp : p.toBlocks₂₁ = 0) (y : M2 n) : u2 (p * y) = p.toBlocks₂₂ * u2 y := by
  simp only [u2, mul_toBlocks₂₁_eq, mul_toBlocks₂₂_eq, hp, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_neg]

theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hy' : yᴴ * JJ n * y = JJ n := hy
  show (x * y)ᴴ * JJ n * (x * y) = JJ n
  calc (x * y)ᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx', hy']

theorem Om_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) : Om (p * y) = Om y := by
  have hp' : pᴴ * JJ n * p = JJ n := hp
  obtain ⟨c11, c12, c21, c22⟩ := conjTranspose_toBlocks p
  obtain ⟨j11, j12, j21, j22⟩ := (JJ_toBlocks (n := n))
  have e := congrArg Matrix.toBlocks₁₂ hp'
  rw [mul_toBlocks₁₂, mul_toBlocks₁₁', mul_toBlocks₁₂, c11, c12, j11, j12, j21, j22, hp21] at e
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    zero_add, add_zero, Matrix.mul_neg, neg_zero] at e
  have hq : (p.toBlocks₂₂)ᴴ * p.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.conjTranspose e
    simpa [Matrix.conjTranspose_mul] using this
  unfold Om
  rw [inverse_second_block_eq_neg_conjTranspose (inG_mul hp hy), inverse_first_block_eq_conjTranspose (inG_mul hp hy), inverse_second_block_eq_neg_conjTranspose hy, inverse_first_block_eq_conjTranspose hy, second_cayley_block_upper_triangular_mul hp21, first_cayley_block_upper_triangular_mul hp21,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hq,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (p.toBlocks₂₂)ᴴ, hq, Matrix.one_mul]

def lam (m : ℕ) (e : ℤ) (z : ℂ) (p : M2 n) : ℂ :=
  p.det ^ e * (p.toBlocks₂₂).det ^ (-(m : ℤ)) * ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) ^ (-z)

theorem fz_up {p y : M2 n} (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (m : ℕ) (e : ℤ) (z : ℂ) :
    fz m e z (p * y) = lam m e z p * fz m e z y := by
  have h1 : (u1 (p * y)).det = (p.toBlocks₂₂).det * (u1 y).det := by rw [first_cayley_block_upper_triangular_mul hp21, Matrix.det_mul]
  have h2 : (u1 (p * y)).det * (ub1 (p * y)).det =
      ((Complex.normSq (p.toBlocks₂₂).det : ℝ) : ℂ) * ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose (inG_mul hp hy), Matrix.det_conjTranspose, h1, star_mul', Complex.star_def,
      Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have h3 : (u1 y).det * (ub1 y).det = ((Complex.normSq (u1 y).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hy, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  simp only [fz, lam]
  rw [h2, h3, h1, Matrix.det_mul, mul_zpow, mul_zpow,
    Complex.mul_cpow_ofReal_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)]
  ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SpanUnitaryMatrix
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

variable {n : ℕ}

theorem span_unitary_matrix :
    Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) = ⊤ := by
  open scoped Matrix.Norms.L2Operator in exact CStarAlgebra.span_unitary (A := Matrix (Fin n) (Fin n) ℂ)

def pm (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if σ i = j then 1 else 0

theorem pm_conj (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    pm σ * X * (pm σ)ᴴ = X.submatrix σ σ := by
  ext i j
  simp [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, eq_comm]

theorem pm_unit (σ : Equiv.Perm (Fin n)) : (pm σ)ᴴ * pm σ = 1 := by
  ext i j
  simp only [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases h : i = j <;> simp [h, eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
  · intro k _ hk
    have : σ k ≠ i := fun e => hk (by rw [← e]; simp)
    simp [this]
  · simp

def dph (a : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = a then Complex.I else 1

theorem dph_unit (a : Fin n) : (dph a)ᴴ * dph a = 1 := by
  rw [dph, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  by_cases hi : i = a <;> simp [hi]

theorem dph_conj {a b : Fin n} (hab : a ≠ b) :
    dph a * Matrix.single a b (1 : ℂ) * (dph a)ᴴ = Complex.I • Matrix.single a b (1 : ℂ) := by
  ext i j
  rw [dph, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [hab.symm]
  · simp [hj]
  · simp [hi]
  · simp [hi, hj]

theorem inv_trace (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → Xᴴ * X = 1 → L (U * X * Uᴴ) = L X) :
    ∀ X, L X = L 1 / n * X.trace := by

  have h' : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → L (U * X * Uᴴ) = L X := by
    intro U X hU
    let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      L.comp ((LinearMap.mulLeft ℂ U).comp (LinearMap.mulRight ℂ Uᴴ)) - L
    have hC : Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set _) ≤ LinearMap.ker C := by
      rw [Submodule.span_le]
      intro Y hY
      have hY' : Yᴴ * Y = 1 := hY.1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, C, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc]
      rw [h U Y hU hY', sub_self]
    have hX : X ∈ LinearMap.ker C := hC (by rw [span_unitary_matrix]; trivial)
    simpa [C, sub_eq_zero, ← Matrix.mul_assoc] using hX

  have hoff : ∀ a b : Fin n, a ≠ b → L (Matrix.single a b 1) = 0 := by
    intro a b hab
    have e := h' (dph a) (Matrix.single a b 1) (dph_unit a)
    rw [dph_conj hab, L.map_smul, smul_eq_mul] at e
    have : (Complex.I - 1) * L (Matrix.single a b 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by simp [sub_eq_zero, Complex.ext_iff])
    · exact h0

  have hdiag : ∀ a b : Fin n, L (Matrix.single a a 1) = L (Matrix.single b b 1) := by
    intro a b
    have e := h' (pm (Equiv.swap a b)) (Matrix.single a a 1) (pm_unit _)
    rw [pm_conj] at e
    have : (Matrix.single a a (1 : ℂ)).submatrix (Equiv.swap a b) (Equiv.swap a b) = Matrix.single b b 1 := by
      have key : ∀ x, a = (Equiv.swap a b) x ↔ b = x := by
        intro x; rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.single_apply, key]
    rw [this] at e
    exact e.symm
  intro X
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : X = 0 := Subsingleton.elim _ _
    simp [this]
  set κ := L (Matrix.single (⟨0, hn⟩ : Fin n) ⟨0, hn⟩ 1)
  have hsum : ∀ Y : Matrix (Fin n) (Fin n) ℂ, L Y = κ * Y.trace := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    rw [Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [show Matrix.single a a (Y a a) = Y a a • Matrix.single a a (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, smul_eq_mul, hdiag a ⟨0, hn⟩, Matrix.diag_apply]; ring
    · intro b _ hb
      rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, hoff a b (Ne.symm hb), smul_zero]
    · simp
  have h1 : L 1 = κ * n := by rw [hsum, trace_one, Fintype.card_fin]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hsum X, h1]; field_simp

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Hf (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (y : M2 n) : ℂ :=
  ∫ t, fz m e z (y * a * nU (herm t) * b) * ψ t

theorem isClosed_G : IsClosed {x : M2 n | InG x} := by
  show IsClosed {x : M2 n | xᴴ * JJ n * x = JJ n}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance instLC : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance instFC : FirstCountableTopology (M2 n) :=
  inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

def Gs (n : ℕ) : Set (M2 n) := {x | InG x}

theorem continuousAt_fz {x : M2 n} (hx : InG x) (m : ℕ) (e : ℤ) (z : ℂ) :
    ContinuousAt (fun p : M2 n × ℂ => fz m e p.2 p.1) (x, z) := by
  have hdx : x.det ≠ 0 := (LoweringDerivative.isUnit_det_of_inG hx).ne_zero
  have hdet : Continuous (fun y : M2 n => y.det) := continuous_id.matrix_det
  have hdetn : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => M.det) := continuous_id.matrix_det
  have hu1 : Continuous (fun y : M2 n => u1 y) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply,
      smul_eq_mul]
    fun_prop
  have hub : ContinuousAt (fun y : M2 n => ub1 y) x :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      (contDiffOn_inverse_first_block i j).continuousOn.continuousAt (isOpen_det_ne.mem_nhds hdx)
  have hw : (u1 x).det * (ub1 x).det = ((Complex.normSq (u1 x).det : ℝ) : ℂ) := by
    rw [inverse_first_block_eq_conjTranspose hx, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  have hslit : (u1 x).det * (ub1 x).det ∈ Complex.slitPlane := by
    rw [hw, Complex.ofReal_mem_slitPlane]
    exact Complex.normSq_pos.2 (det_first_block_ne_zero_group hx)
  show ContinuousAt (fun p : M2 n × ℂ =>
    p.1.det ^ e * (u1 p.1).det ^ (-(m : ℤ)) * ((u1 p.1).det * (ub1 p.1).det) ^ (-p.2)) (x, z)
  have hA : ContinuousAt (fun p : M2 n × ℂ => p.1.det) (x, z) := (hdet.comp continuous_fst).continuousAt
  have hB : ContinuousAt (fun p : M2 n × ℂ => (u1 p.1).det) (x, z) :=
    ((hu1.comp continuous_fst).matrix_det).continuousAt
  have hub' : ContinuousAt (fun y : M2 n => (ub1 y).det) x := hdetn.continuousAt.comp hub
  have hC : ContinuousAt (fun p : M2 n × ℂ => (ub1 p.1).det) (x, z) :=
    ContinuousAt.comp (g := fun y : M2 n => (ub1 y).det) (f := Prod.fst) (x := (x, z)) hub'
      continuous_fst.continuousAt
  refine ((hA.zpow₀ e (Or.inl hdx)).mul (hB.zpow₀ _ (Or.inl (det_first_block_ne_zero_group hx)))).mul ?_
  exact (hB.mul hC).cpow continuous_snd.neg.continuousAt hslit

theorem inG_path {y a b : M2 n} (hy : InG y) (ha : InG a) (hb : InG b) (t : Fin n → Fin n → ℝ) :
    InG (y * a * nU (herm t) * b) := by
  have hH : (herm t)ᴴ = herm t := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add (f := _), map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hN : InG (nU (herm t)) := by
    show (nU (herm t))ᴴ * JJ n * nU (herm t) = JJ n
    simp [nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hH]
  exact inG_mul (inG_mul (inG_mul hy ha) hN) hb

private theorem continuous_nU_herm : Continuous (fun t : Fin n → Fin n → ℝ => nU (herm t)) := by
  have hherm : Continuous (fun t : Fin n → Fin n → ℝ => herm t) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  unfold nU
  exact continuous_const.matrix_fromBlocks hherm continuous_const continuous_const

private theorem continuous_fz_mul_nU_herm_mul {X : Type} [TopologicalSpace X] (m : ℕ) (e : ℤ)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) {a b : M2 n} (ha : InG a) (hb : InG b)
    (Y : X → M2 n) (hY : Continuous Y) (hYG : ∀ x, InG (Y x)) (Z : X → ℂ) (hZ : Continuous Z)
    (T : X → (Fin n → Fin n → ℝ)) (hT : Continuous T) :
    Continuous fun x => fz m e (Z x) (Y x * a * nU (herm (T x)) * b) * ψ (T x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine ContinuousAt.mul ?_ (hψ.comp hT).continuousAt
  have hG := inG_path (hYG x) ha hb (T x)
  have hP : Continuous fun x => (Y x * a * nU (herm (T x)) * b, Z x) :=
    (((hY.matrix_mul continuous_const).matrix_mul (continuous_nU_herm.comp hT)).matrix_mul
      continuous_const).prodMk hZ
  exact ContinuousAt.comp (g := fun p : M2 n × ℂ => fz m e p.2 p.1)
    (f := fun x => (Y x * a * nU (herm (T x)) * b, Z x)) (x := x)
    (continuousAt_fz hG m e (Z x)) hP.continuousAt

theorem continuous_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b : M2 n} (ha : InG a) (hb : InG b) :
    Continuous fun q : ↥(Gs n) × ℂ => Hf m e ψ a b q.2 q.1.1 := by
  haveI : LocallyCompactSpace ↥(Gs n) := (isClosed_G (n := n)).locallyCompactSpace
  have hF := continuous_fz_mul_nU_herm_mul (X := (↥(Gs n) × ℂ) × (Fin n → Fin n → ℝ)) m e hψ ha hb
    (fun p => p.1.1.1) (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    (fun p => p.1.1.2) (fun p => p.1.2) (continuous_snd.comp continuous_fst) (fun p => p.2) continuous_snd
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin n → Fin n → ℝ)))
    (f := fun (q : ↥(Gs n) × ℂ) t => fz m e q.2 (q.1.1 * a * nU (herm t) * b) * ψ t) hF hψc
  refine key.congr fun q => ?_
  unfold Hf
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
    rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]

theorem differentiable_Hf (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {a b y : M2 n} (ha : InG a) (hb : InG b) (hy : InG y) : Differentiable ℂ fun z => Hf m e ψ a b z y := by
  have hC : IsCompact (tsupport ψ) := hψc
  haveI : IsFiniteMeasure ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  have hnull : ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ)) (tsupport ψ)ᶜ = 0 := by
    rw [Measure.restrict_apply' (isClosed_tsupport ψ).measurableSet, Set.compl_inter_self, measure_empty]
  have hF := continuous_fz_mul_nU_herm_mul (X := (Fin n → Fin n → ℝ) × ℂ) m e hψ ha hb (fun _ => y) continuous_const
    (fun _ => hy) (fun p => p.2) continuous_snd (fun p => p.1) continuous_fst
  have hdiff : ∀ t ∈ tsupport ψ,
      DifferentiableOn ℂ (fun z => fz m e z (y * a * nU (herm t) * b) * ψ t) Set.univ := by
    intro t _ z _
    have hG := inG_path hy ha hb t
    have hc : (u1 (y * a * nU (herm t) * b)).det * (ub1 (y * a * nU (herm t) * b)).det ≠ 0 := by
      refine mul_ne_zero (det_first_block_ne_zero_group hG) ?_
      rw [inverse_first_block_eq_conjTranspose hG, Matrix.det_conjTranspose]
      exact star_ne_zero.2 (det_first_block_ne_zero_group hG)
    simp only [fz]
    exact (((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hc))).mul_const
      _).differentiableWithinAt
  have main := (AbsSt.holParam (Fin n → Fin n → ℝ) ((volume : Measure (Fin n → Fin n → ℝ)).restrict (tsupport ψ))
    (tsupport ψ) hC hnull Set.univ (fun t z => fz m e z (y * a * nU (herm t) * b) * ψ t) isOpen_univ
    hF.continuousOn hdiff).1
  rw [differentiableOn_univ] at main
  have hEq : ∀ z, Hf m e ψ a b z y = ∫ t in tsupport ψ, fz m e z (y * a * nU (herm t) * b) * ψ t := by
    intro z
    unfold Hf
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]).symm
  simp only [hEq]
  exact main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem vacuum_at_zero_mul_compact (m : ℕ) (e : ℤ) (x : M2 n) {k : M2 n} (hk : InK k) :
    fz m e 0 (x * k) = fz m e 0 x * fz m e 0 k := by
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  rw [first_cayley_block_mul_compact x hk, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow]
  ring

theorem norm_fz0K (m : ℕ) (e : ℤ) {k : M2 n} (hk : InK k) : star (fz m e 0 k) * fz m e 0 k = 1 := by
  have hk1 : Complex.normSq (det k) = 1 := by
    have h := congrArg Matrix.det hk.2
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      mul_comm, Complex.mul_conj] at h
    exact_mod_cast h
  have hu := normSq_det_u1K hk
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one, map_mul, map_zpow₀, hk1, hu, _root_.one_zpow]
  simp

theorem first_cayley_block_one : u1 (1 : M2 n) = 1 := by
  unfold u1
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp
theorem second_cayley_block_one : u2 (1 : M2 n) = 1 := by
  unfold u2
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)

include hK in
theorem ιK (k : Kg) : InK (ι k) := (hK _).mpr ⟨k, rfl⟩

include hK in
theorem first_cayley_block_inv (k : Kg) : u1 (ι k⁻¹) = (u1 (ι k))⁻¹ := by
  have h : u1 (ι k⁻¹) * u1 (ι k) = 1 := by
    rw [← first_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, first_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem second_cayley_block_inv (k : Kg) : u2 (ι k⁻¹) = (u2 (ι k))⁻¹ := by
  have h : u2 (ι k⁻¹) * u2 (ι k) = 1 := by
    rw [← second_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, second_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem vacuum_at_zero_inv_star (m : ℕ) (e : ℤ) (k : Kg) : fz m e 0 (ι k⁻¹) = star (fz m e 0 (ι k)) := by
  have hk := ιK ι hK k
  have h1 : fz m e 0 (ι k⁻¹) * fz m e 0 (ι k) = 1 := by
    rw [← vacuum_at_zero_mul_compact m e _ hk, ← map_mul, inv_mul_cancel, map_one]
    unfold fz
    simp [first_cayley_block_one]
  have h2 := norm_fz0K m e hk
  have hne : fz m e 0 (ι k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

include hK in
theorem rho_shift (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k1 k : Kg) :
    rhoP ι m e Y (k1⁻¹ * k) = fz m e 0 (ι k1) * rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) k := by
  have ha := ιK ι hK k1
  have hb := ιK ι hK k
  have hdet : IsUnit (u2 (ι k1)).det := Matrix.isUnit_det_of_left_inverse (second_cayley_block_compact_unitary ha)
  unfold rhoP
  rw [map_mul, vacuum_at_zero_mul_compact m e _ hb, vacuum_at_zero_inv_star ι hK m e k1, second_cayley_block_mul_compact _ hb, first_cayley_block_mul_compact _ hb,
    second_cayley_block_inv ι hK k1, first_cayley_block_inv ι hK k1, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet]
  simp only [star_mul', star_star, Matrix.mul_assoc]
  ring

theorem Hf_up (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p y : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (z : ℂ) :
    Hf m e ψ a b z (p * y) = lam m e z p * Hf m e ψ a b z y := by
  simp only [Hf]
  rw [← integral_const_mul]
  congr 1; funext t
  rw [show p * y * a * nU (herm t) * b = p * (y * a * nU (herm t) * b) by simp only [Matrix.mul_assoc],
    fz_up hp hp21 (inG_path hy ha hb t)]
  ring


include hK in
theorem tOp_formula (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (k1 : Kg) (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) (p * ι k1) =
      lam m e z p * fz m e 0 (ι k1) * tOp μ ι (rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹)) ψ a b (fz m e z) 1 := by
  unfold tOp
  have hs := integral_mul_left_eq_self (μ := μ) (fun k => rhoP ι m e Y k *
    ∫ t, fz m e z (p * ι k1 * ι k * a * nU (herm t) * b) * ψ t) k1⁻¹
  rw [← hs, mul_assoc, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext k
  have hι : ι k1 * ι (k1⁻¹ * k) = ι k := by
    rw [← map_mul, mul_inv_cancel_left]
  have hH := Hf_up m e ψ ha hb hp hp21 (ιK ι hK k).1 z
  unfold Hf at hH
  rw [rho_shift ι hK m e Y k1 k, Matrix.mul_assoc p (ι k1), hι, hH]
  simp only [Matrix.one_mul]
  ring

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
end
end

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rhoP_add {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (X Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (X + Y) k = rhoP ι m e X k + rhoP ι m e Y k := by
  simp only [rhoP, Matrix.mul_add, Matrix.add_mul, trace_add, mul_add, star_add]

theorem rhoP_smul {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (c • X) k = star c * rhoP ι m e X k := by
  simp only [rhoP, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, star_mul']; ring

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

def abelian₂ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  tOp μ ι (rhoP ι m e X) ψ a b (fz m e z) 1

theorem Lam_eq (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = ∫ k, rhoP ι m e X k * Hf m e ψ a b z (ι k) ∂μ := by
  simp only [abelian₂, tOp, Hf, one_mul]

include hι hK hψ hψc ha hb in
theorem continuous_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have h1 : Continuous (rhoP (⇑ι) m e X) := LoweringDerivative.continuous_rhoP (⇑ι) hι hG m e X
  have h2 := continuous_Hf m e hψ hψc ha hb
  have h3 : Continuous fun k : Kg => ((⟨ι k, hG k⟩ : Gs n), z) :=
    (Continuous.subtype_mk hι (fun k => hG k)).prodMk continuous_const
  have h4 : Continuous fun k : Kg => Hf m e ψ a b z (ι k) := by
    have h5 := h2.comp h3
    simp only [Function.comp_def] at h5
    exact h5
  exact h1.mul h4

include hι hK hψ hψc ha hb in
theorem integrable_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k)) μ := by
  exact (continuous_integrand ι hι hK m e hψ hψc ha hb z X).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

include hι hK hψ hψc ha hb in
theorem Lam_add (z : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (X + Y) = abelian₂ μ ι m e ψ a b z X + abelian₂ μ ι m e ψ a b z Y := by
  simp only [Lam_eq, rhoP_add, add_mul]
  exact integral_add (integrable_integrand μ ι hι hK m e hψ hψc ha hb z X)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z Y)

theorem Lam_smul (z c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (c • X) = star c * abelian₂ μ ι m e ψ a b z X := by
  simp only [Lam_eq, rhoP_smul, mul_assoc, integral_const_mul]

private theorem inK_fromBlocks_unitary_diag (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    InK (Matrix.fromBlocks U 0 0 U : M2 n) := by
  refine ⟨?_, ?_⟩
  · simp [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]
  · simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]

private theorem u1_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u1 (Matrix.fromBlocks U 0 0 U * y) = U * u1 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u1, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul]

private theorem u2_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u2 (Matrix.fromBlocks U 0 0 U * y) = U * u2 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u2, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

include hK ha hb in
theorem Lam_inv (z : ℂ) {U X : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hX : Xᴴ * X = 1) :
    abelian₂ μ ι m e ψ a b z (U * X * Uᴴ) = abelian₂ μ ι m e ψ a b z X := by
  obtain ⟨k0, hk0⟩ := (hK _).1 (inK_fromBlocks_unitary_diag U hU)
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have hpG : InG (Matrix.fromBlocks U 0 0 U : M2 n) := LoweringDerivative.inG_of_inK (inK_fromBlocks_unitary_diag U hU)
  have hp21 : Matrix.toBlocks₂₁ (Matrix.fromBlocks U 0 0 U : M2 n) = 0 :=
    Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  have hUi : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hd : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hU, Matrix.det_one]
  have hn : Complex.normSq U.det = 1 := by
    have h : (Complex.normSq U.det : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hd
    exact_mod_cast h
  have hl : ∀ w : ℂ, lam m e w (Matrix.fromBlocks U 0 0 U : M2 n) =
      (U.det * U.det) ^ e * U.det ^ (-(m : ℤ)) := by
    intro w
    simp only [lam, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_fromBlocks_zero₂₁, hn, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  have h1 : star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e = 1 := by
    rw [star_zpow₀, ← mul_zpow, star_mul',
      show star U.det * star U.det * (U.det * U.det) = (star U.det * U.det) * (star U.det * U.det) by ring,
      hd, one_mul, _root_.one_zpow]
  have h2 : star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ)) = 1 := by
    rw [star_zpow₀, ← mul_zpow, hd, _root_.one_zpow]
  have hlam : star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) *
      lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) = 1 := by
    rw [hl, hl]
    calc star ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ))) * ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ)))
        = (star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e) *
          (star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ))) := by
          rw [star_mul']
          ring
      _ = 1 := by rw [h1, h2, one_mul]
  have aux : ∀ A B C : ℂ, star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) * A * B *
      (lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) * C) = A * B * C := by
    intro A B C
    linear_combination (A * B * C) * hlam
  have key : ∀ k, rhoP ι m e (U * X * Uᴴ) (k0 * k) * Hf m e ψ a b z (ι (k0 * k)) =
      rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
    intro k
    have hm : (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k)) = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
      calc (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k))
          = (u2 (ι k))⁻¹ * (Uᴴ * U) * X * (Uᴴ * U) * u1 (ι k) := by
            simp only [Matrix.mul_assoc]
        _ = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
            rw [hU]
            simp only [Matrix.mul_one]
    simp only [rhoP]
    rw [map_mul, hk0, Hf_up m e ψ ha hb hpG hp21 (hG k) z, fz_up hpG hp21 (hG k) m e 0,
      u1_fromBlocks_diag_mul, u2_fromBlocks_diag_mul, Matrix.mul_inv_rev, hUi, hm]
    simp only [star_mul']
    exact aux _ _ _
  have hinv := integral_mul_left_eq_self (μ := μ)
    (fun k => rhoP ι m e (U * X * Uᴴ) k * Hf m e ψ a b z (ι k)) k0
  simp only [key] at hinv
  rw [Lam_eq, Lam_eq]
  exact hinv.symm

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
