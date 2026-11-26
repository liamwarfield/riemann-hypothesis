module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSumStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDuality
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDuality
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section Herm

variable {L : Type} [Field L] {N : ℕ}

def hermJ (σ : L →+* L) (x y : Fin N → L) : L := ∑ i, σ (x i) * y i.rev

theorem hermJ_add_left (σ : L →+* L) (x x' y : Fin N → L) :
    hermJ σ (x + x') y = hermJ σ x y + hermJ σ x' y := by
  simp only [hermJ, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hermJ_add_right (σ : L →+* L) (x y y' : Fin N → L) :
    hermJ σ x (y + y') = hermJ σ x y + hermJ σ x y' := by
  simp only [hermJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem map_hermJ {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x y : Fin N → L) :
    σ (hermJ σ x y) = hermJ σ y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermJ, map_sum, map_mul, hσσ]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, mul_comm]

theorem dotProduct_eq_neg_hermJ {σ : L →+* L} (r b w : Fin N → L) (h : ∀ j, r j = -σ (b j.rev)) :
    r ⬝ᵥ w = -hermJ σ b w := by
  rw [hermJ, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, h, neg_mul]

end Herm

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem hermJ_mulVec (g : GU σ N) (x y : Fin N → L) :
    hermJ σ (mat g *ᵥ x) (mat g *ᵥ y) = hermJ σ x y := by
  have hconj : ∀ i k : Fin N, σ (mat g i k) = mat g⁻¹ k.rev i.rev := fun i k => by
    rw [mat_inv_apply, Fin.rev_rev, Fin.rev_rev]
  have hinner : ∀ k l : Fin N, ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l = (1 : Matrix (Fin N) (Fin N) L) k.rev l := by
    intro k l
    rw [← mat_inv_mul g, Matrix.mul_apply]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  calc hermJ σ (mat g *ᵥ x) (mat g *ᵥ y)
      = ∑ k : Fin N, ∑ l : Fin N, σ (x k) * y l * ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hermJ, Matrix.mulVec, dotProduct, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k : Fin N, σ (x k) * y k.rev := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hinner, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]

theorem sigma_mem_intL {x : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (h : x ∈ intL L) : σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]
  exact h

theorem hermJ_int {ϖ : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hϖ : σ ϖ = ϖ) (e : ℕ) (x : Fin N → L)
    (h : ∀ i, ϖ ^ e * x i ∈ intL L) : ϖ ^ (2 * e) * hermJ σ x x ∈ intL L := by
  have hsum : ϖ ^ (2 * e) * hermJ σ x x = ∑ i, σ (ϖ ^ e * x i) * (ϖ ^ e * x i.rev) := by
    simp only [hermJ, Finset.mul_sum, map_mul, map_pow, hϖ]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (sigma_mem_intL hσ (h i)) (h i.rev)

end Unitary

theorem smallCorner_of_heis_dual : Heis → Dual → SmallCorner := by
  intro hH hD
  unfold SmallCorner
  intro L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  have hU' := hU
  unfold IsUnramInv at hU'
  obtain ⟨hσσ, hσv, hϖσ, hϖv, -⟩ := hU'

  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  have hrb : ∀ j, r j = -σ (b j.rev) := fun j => by
    rw [hb]
    simp only [Fin.rev_rev, map_neg, hσσ, neg_neg]
  obtain ⟨b₁, hb₁⟩ : ∃ x : Fin N → L, x = (C * V * mat g₀) *ᵥ b := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x : Fin N → L, x = (C * U) *ᵥ b := ⟨_, rfl⟩
  have hsplit : b₁ + b₂ = b := by
    have hCinv : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hF.2.2.2.2
    rw [hb₁, hb₂, ← Matrix.add_mulVec, add_comm, Matrix.mul_assoc, ← Matrix.mul_add, hCinv,
      Matrix.one_mulVec]
  obtain ⟨τ, hτint, hτ⟩ := exists_trace_one hU
  obtain ⟨s, hs⟩ : ∃ s : L, s = hermJ σ b₁ b₁ - hermJ σ b₂ b₂ := ⟨_, rfl⟩
  have hσs : σ s = s := by rw [hs, map_sub, map_hermJ hσσ, map_hermJ hσσ]
  have hrb₁ : r ⬝ᵥ b₁ = -hermJ σ b b₁ := dotProduct_eq_neg_hermJ r b b₁ hrb
  have hnorm : -∑ j, r j * σ (r j.rev) = -hermJ σ b b := by
    rw [← dotProduct_eq_neg_hermJ r b b hrb, hb]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have hc : r ⬝ᵥ b₁ + τ * s + σ (r ⬝ᵥ b₁ + τ * s) = -∑ j, r j * σ (r j.rev) := by
    rw [hnorm, hrb₁, map_add (f := _), map_mul, map_neg, map_hermJ hσσ, hσs, ← hsplit]
    simp only [hermJ_add_left, hermJ_add_right]
    linear_combination s * hτ + hs
  obtain ⟨hHrad, -, hHex⟩ := hH L ϖ σ q N hU
  obtain ⟨u, hu, hur, huc⟩ := hHex r (r ⬝ᵥ b₁ + τ * s) hc
  have hcol : colOf u = b := by
    funext i
    have hi := (hHrad u hu).1 i.rev
    rw [hur, Fin.rev_rev] at hi
    rw [hb]
    simp only [hi, map_neg, hσσ, neg_neg]
  obtain ⟨h₁, h₂⟩ := (hD L ϖ σ q N hU g₀ U V C hF r b (ϖ ^ e) hrb).1 hr
  refine ⟨u, hu, hur, ?_, ?_⟩
  · rw [hur]
    exact hr
  · rw [hur, hcol, huc, ← hb₁, add_sub_cancel_left]
    have hϖint : ϖ ∈ intL L := by
      change Valued.v ϖ ≤ 1
      rw [hϖv]
      exact WithZero.coe_le_one.mpr (by decide)
    have i₁ : ϖ ^ (2 * e) * hermJ σ b₁ b₁ ∈ intL L :=
      hermJ_int hσv hϖσ e b₁ (by rw [hb₁]; exact h₁)
    have hg : mat g₀ *ᵥ b₂ = (mat g₀ * C * U) *ᵥ b := by
      rw [hb₂, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have i₂ : ϖ ^ (2 * e) * hermJ σ b₂ b₂ ∈ intL L := by
      rw [← hermJ_mulVec g₀ b₂ b₂, hg]
      exact hermJ_int hσv hϖσ e _ h₂
    have hf : ϖ ^ f = ϖ ^ (f - 2 * e) * ϖ ^ (2 * e) := by rw [← pow_add, Nat.sub_add_cancel hef]
    have hsplit' : ϖ ^ f * (τ * s) =
        τ * ϖ ^ (f - 2 * e) * (ϖ ^ (2 * e) * hermJ σ b₁ b₁ - ϖ ^ (2 * e) * hermJ σ b₂ b₂) := by
      rw [hf, hs]
      ring
    rw [hsplit']
    exact Subring.mul_mem _ (Subring.mul_mem _ hτint (Subring.pow_mem _ hϖint _)) (Subring.sub_mem _ i₁ i₂)

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDualityStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_corner_of_heisenberg_duality : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.InertZeta.smallCorner_of_heis_dual | exact GlobalTheory.InertZeta.smallCorner_of_heis_dual | (intros; apply GlobalTheory.InertZeta.smallCorner_of_heis_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl

namespace GlobalTheory.FrameCompletion

section Basic

variable {L : Type} [Field L] {σ : L →+* L}

theorem conjT_add {m p : Type} (A B : Matrix m p L) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j; simp [cT]

theorem conjT_sub {m p : Type} (A B : Matrix m p L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT]

theorem conjT_neg {m p : Type} (A : Matrix m p L) : cT σ (-A) = -cT σ A := by
  ext i j; simp [cT]

theorem conjT_smul {m p : Type} (c : L) (A : Matrix m p L) : cT σ (c • A) = σ c • cT σ A := by
  ext i j; simp [cT]

theorem conjT_zero {m p : Type} : cT σ (0 : Matrix m p L) = 0 := by
  ext i j; simp [cT]

theorem conjT_conjT (hσσ : ∀ x, σ (σ x) = x) {m p : Type} (A : Matrix m p L) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hσσ]

theorem conjT_fromRows {m m' p : Type} (A : Matrix m p L) (B : Matrix m' p L) :
    cT σ (fromRows A B) = fromCols (cT σ A) (cT σ B) := by
  ext i (j | j) <;> simp [cT]

theorem conjT_fromCols {m p p' : Type} (A : Matrix m p L) (B : Matrix m p' L) :
    cT σ (fromCols A B) = fromRows (cT σ A) (cT σ B) := by
  ext (i | i) j <;> simp [cT]

theorem conjT_fromBlocks {m m' p p' : Type} (A : Matrix m p L) (B : Matrix m p' L) (C : Matrix m' p L)
    (D : Matrix m' p' L) : cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext (i | i) (j | j) <;> simp [cT]

theorem conjT_antiJ {n : ℕ} : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, antiJ, Matrix.transpose_apply, Matrix.map_apply]
  rw [add_comm j.val i.val]
  split_ifs <;> simp

theorem antiJ_mul_antiJ_mul [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {p : Type} (X : Matrix (Fin n) p L) : antiJ L n * (antiJ L n * X) = X := by
  rw [← Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

def gramQ (L : Type) [Field L] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L :=
  fromBlocks (antiJ L n) 0 0 (-antiJ L n)

theorem conjT_gramQ {n : ℕ} : cT σ (gramQ L n) = gramQ L n := by
  rw [gramQ, conjT_fromBlocks, conjT_antiJ, conjT_zero, conjT_neg, conjT_antiJ]

theorem pair_symm (hσσ : ∀ x, σ (σ x) = x) {n : ℕ} {κ μ : Type} (X : Matrix (Fin n ⊕ Fin n) κ L)
    (X' : Matrix (Fin n ⊕ Fin n) μ L) : cT σ (cT σ X * gramQ L n * X') = cT σ X' * gramQ L n * X := by
  simp only [cT_mul, conjT_conjT hσσ, conjT_gramQ, Matrix.mul_assoc]

theorem pair_fromRows {n : ℕ} {κ μ : Type} (C D : Matrix (Fin n) κ L) (C' D' : Matrix (Fin n) μ L) :
    cT σ (fromRows C D) * gramQ L n * fromRows C' D' =
      cT σ C * antiJ L n * C' - cT σ D * antiJ L n * D' := by
  rw [conjT_fromRows, gramQ, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]

theorem pair_comb {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (s t s' t' : L) :
    cT σ (s • X + t • W) * Q * (s' • X + t' • W) =
      (σ s * s') • (cT σ X * Q * X) + (σ s * t') • (cT σ X * Q * W) + (σ t * s') • (cT σ W * Q * X) +
        (σ t * t') • (cT σ W * Q * W) := by
  simp only [conjT_add, conjT_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

theorem pair_sub {ι κ : Type} [Fintype ι] [Fintype κ] (Q : Matrix ι ι L) (X W : Matrix ι κ L) (M : Matrix κ κ L)
    (c : L) : cT σ (X - c • (W * M)) * Q * (X - c • (W * M)) =
      cT σ X * Q * X - c • (cT σ X * Q * W * M) - σ c • (cT σ M * (cT σ W * Q * X)) +
        (σ c * c) • (cT σ M * (cT σ W * Q * W) * M) := by
  simp only [conjT_sub, conjT_smul, cT_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc]
  module

end Basic

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem isInt_smul {ι κ : Type} {c : L} {M : Matrix ι κ L} (hc : c ∈ intL L) (hM : IsInt M) : IsInt (c • M) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

theorem isInt_neg {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) : IsInt (-M) := fun i j => neg_mem (hM i j)

theorem isInt_sub {ι κ : Type} {M N : Matrix ι κ L} (hM : IsInt M) (hN : IsInt N) : IsInt (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem isInt_conjT (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) :
    IsInt (cT σ M) := fun i j => by
  show Valued.v (σ (M j i)) ≤ 1
  rw [hσ]
  exact hM j i

theorem isInt_fromRows {ι ι' κ : Type} {A : Matrix ι κ L} {B : Matrix ι' κ L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromRows A B) := by
  rintro (i | i) j
  exacts [hA i j, hB i j]

theorem isInt_fromCols {ι κ κ' : Type} {A : Matrix ι κ L} {B : Matrix ι κ' L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromCols A B) := by
  rintro i (j | j)
  exacts [hA i j, hB i j]

theorem isInt_submatrix {ι κ ι' κ' : Type} {M : Matrix ι κ L} (hM : IsInt M) (f : ι' → ι) (g : κ' → κ) :
    IsInt (M.submatrix f g) := fun i j => hM (f i) (g j)

theorem isInt_antiJ {n : ℕ} : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isInt_gramQ {n : ℕ} : IsInt (gramQ L n) := by
  rintro (i | i) (j | j)
  · exact isInt_antiJ i j
  · exact zero_mem _
  · exact zero_mem _
  · exact isInt_neg isInt_antiJ i j

end Int

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem exists_frame (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) (g U V C : Matrix (Fin n) (Fin n) L) (hg : cT σ g * antiJ L n * g = antiJ L n)
    (hUi : IsInt U) (hVi : IsInt V) (hCi : IsInt C) (hDi : IsInt (g * C)) (h5 : (U + V * g) * C = 1) :
    ∃ K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt K ∧ cT σ K * gramQ L n * K = gramQ L n ∧
      ∀ x : Fin n → L, K *ᵥ Sum.elim x x = Sum.elim (C *ᵥ x) ((g * C) *ᵥ x) := by
  set Q := gramQ L n with hQ
  set Y : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows C (g * C) with hY
  set Z : Matrix (Fin n ⊕ Fin n) (Fin n) L := fromRows (antiJ L n * cT σ U * antiJ L n) (-(antiJ L n * cT σ V * antiJ L n)) with hZ
  have hYY : cT σ Y * Q * Y = 0 := by
    rw [hY, hQ, pair_fromRows, cT_mul,
      show cT σ C * cT σ g * antiJ L n * (g * C) = cT σ C * (cT σ g * antiJ L n * g) * C by simp only [Matrix.mul_assoc], hg, sub_self]
  have hUC : cT σ C * cT σ U + cT σ (g * C) * cT σ V = 1 := by
    rw [← cT_mul, ← cT_mul, ← conjT_add, ← Matrix.mul_assoc V, ← Matrix.add_mul, h5, cT_one]
  have hYZ : cT σ Y * Q * Z = antiJ L n := by
    rw [hY, hZ, hQ, pair_fromRows]
    calc _ = (cT σ C * cT σ U + cT σ (g * C) * cT σ V) * antiJ L n := by
          simp only [Matrix.mul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.mul_assoc, antiJ_mul_antiJ_mul]
      _ = antiJ L n := by rw [hUC, Matrix.one_mul]
  have hZY : cT σ Z * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ, conjT_antiJ]
  set H := cT σ Z * Q * Z with hH
  have hHH : cT σ H = H := pair_symm hσσ Z Z
  set Z' := Z - τ • (Y * (antiJ L n * H)) with hZ'
  have hYZ' : cT σ Y * Q * Z' = antiJ L n := by
    rw [hZ', Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hYY, Matrix.zero_mul, smul_zero, sub_zero, hYZ]
  have hZ'Y : cT σ Z' * Q * Y = antiJ L n := by rw [← pair_symm hσσ, hYZ', conjT_antiJ]
  have hZ'Z' : cT σ Z' * Q * Z' = 0 := by
    rw [hZ', pair_sub, hYY, hZY, hYZ, ← hH, cT_mul, hHH, conjT_antiJ, antiJ_mul_antiJ_mul, Matrix.mul_zero,
      Matrix.zero_mul, smul_zero, add_zero, Matrix.mul_assoc, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.mul_one,
      sub_sub, ← add_smul, hτ1, one_smul, sub_self]
  set a := τ • Y + (1 : L) • Z' with ha
  set b := σ τ • Y + (-1 : L) • Z' with hb
  have hInt : IsInt Y ∧ IsInt Z' := by
    have hYi : IsInt Y := isInt_fromRows hCi hDi
    refine ⟨hYi, isInt_sub (isInt_fromRows ?_ ?_) (isInt_smul hτ (hYi.mul (isInt_antiJ.mul ?_)))⟩
    · exact (isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ
    · exact isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ)
    · have hZi : IsInt Z := isInt_fromRows ((isInt_antiJ.mul (isInt_conjT hσ hUi)).mul isInt_antiJ)
        (isInt_neg ((isInt_antiJ.mul (isInt_conjT hσ hVi)).mul isInt_antiJ))
      exact ((isInt_conjT hσ hZi).mul isInt_gramQ).mul hZi
  have hστ : σ τ ∈ intL L := by
    show Valued.v (σ τ) ≤ 1
    rw [hσ]
    exact hτ
  refine ⟨fromCols a b, isInt_fromCols ?_ ?_, ?_, fun x => ?_⟩
  · exact (isInt_smul hτ hInt.1).add (isInt_smul (one_mem _) hInt.2)
  · exact (isInt_smul hστ hInt.1).add (isInt_smul (neg_mem (one_mem _)) hInt.2)
  · rw [conjT_fromCols, fromRows_mul, fromRows_mul_fromCols, ha, hb, pair_comb, pair_comb, pair_comb, pair_comb,
      hYY, hYZ', hZ'Y, hZ'Z', hQ, gramQ]
    simp only [smul_zero, add_zero, zero_add, map_one, map_neg, hσσ, mul_one, one_mul, mul_neg, neg_mul, neg_smul,
      neg_neg]
    rw [← add_smul, add_comm (σ τ), hτ1, one_smul, neg_add_cancel, add_neg_cancel, ← neg_add, ← add_smul, hτ1, one_smul]
  · rw [fromCols_mulVec_sumElim, ← Matrix.add_mulVec, ha, hb,
      show τ • Y + (1 : L) • Z' + (σ τ • Y + (-1 : L) • Z') = (τ + σ τ) • Y by module, hτ1, one_smul, hY,
      fromRows_mulVec]

end Main

theorem completion : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hf
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  obtain ⟨hUi, hVi, hCi, hDi, h5⟩ := hf
  obtain ⟨K, hKi, hKQ, hKx⟩ := exists_frame hU.1 hU.2.1 hτ hτ1 (mat g) U V C g.2 hUi hVi hCi hDi h5
  set e := finSumFinEquiv (m := n) (n := n) with he
  set k := K.submatrix e.symm e.symm with hk
  have hQs : GlobalTheory.Doubling.dblGram e (antiJ L n) = (gramQ L n).submatrix e.symm e.symm := rfl
  have hkQ : cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = GlobalTheory.Doubling.dblGram e (antiJ L n) := by
    rw [hQs, hk, show cT σ (K.submatrix e.symm e.symm) = (cT σ K).submatrix e.symm e.symm from rfl,
      submatrix_mul_equiv, submatrix_mul_equiv, hKQ]
  have hQQ : GlobalTheory.Doubling.dblGram e (antiJ L n) * GlobalTheory.Doubling.dblGram e (antiJ L n) = 1 := by
    rw [GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat_mul, neg_mul_neg, GlobalTheory.UnitarySwap.antiJ_mul_self,
      GlobalTheory.Doubling.blkMat_one]
  have hinv : GlobalTheory.Doubling.dblGram e (antiJ L n) * cT σ k * GlobalTheory.Doubling.dblGram e (antiJ L n) * k = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ k), hkQ, hQQ]
  have hQi : IsInt (GlobalTheory.Doubling.dblGram e (antiJ L n)) := by
    rw [hQs]
    exact isInt_submatrix isInt_gramQ _ _
  have hki : IsInt k := isInt_submatrix hKi _ _
  obtain ⟨W, hW, hWk⟩ := P.cartan_exists_glint (intL L) k _ (mul_eq_one_comm.1 hinv) hki
    ((hQi.mul (isInt_conjT hU.2.1 hki)).mul hQi)
  refine ⟨W, ?_, hW, fun x => ?_⟩
  · show cT σ (W : Matrix (Fin (n + n)) (Fin (n + n)) L) * _ * (W : Matrix (Fin (n + n)) (Fin (n + n)) L) = _
    rw [hWk, hkQ]
  · rw [hWk, hk, GlobalTheory.Doubling.pairVec, GlobalTheory.Doubling.pairVec, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id, hKx]

end GlobalTheory.FrameCompletion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletionStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLattice_primitive_isotropic_frame_completion : Completion := by
  first | exact @GlobalTheory.FrameCompletion.completion | exact GlobalTheory.FrameCompletion.completion | (intros; apply GlobalTheory.FrameCompletion.completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeAddVectorDetValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeAddVectorDetValuation
noncomputable section

open Matrix

namespace GlobalTheory.InertZeta

theorem smul_mem_integral_submodule_of_valuation_le_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P :=
  P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  rcases he with rfl | ⟨i₀, hi₀⟩
  · refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact (by simpa using hρ i : Valued.v (ρ i) ≤ 1)
  · have h0 : ρ i₀ ≠ 0 := fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm
    refine ⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩
    · rw [Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]
    · apply le_antisymm
      · refine sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
        · by_cases hi : i = i₀
          · subst hi
            have hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j := by
              rw [Matrix.vecMul_eq_sum]; exact (Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm
            have : M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i -
                ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j := by
              rw [Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]
              rw [add_sub_assoc, ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_zero, add_zero]
              intro j hj
              rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]
            rw [this]
            have hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ)) := by rw [map_inv₀, hi₀, WithZero.exp_neg]
            refine Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))
            · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
            · rw [map_mul, hv]
              calc WithZero.exp (-(e : ℤ)) * Valued.v (ρ j) ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) :=
                    mul_le_mul' le_rfl (hρ j)
                _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
          · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i
            rwa [Matrix.updateRow_ne hi] at this
        · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀
          rwa [Matrix.updateRow_self] at this
      · refine rowLat_le.2 fun i => ?_
        by_cases hi : i = i₀
        · subst hi
          rw [Matrix.updateRow_self]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · rw [Matrix.updateRow_ne hi]
          exact Submodule.mem_sup_left (row_mem_rowLat _ _)

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeAddVectorDetValuationStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_add_vector_det_valuation : AddVec := by
  first | exact @GlobalTheory.InertZeta.addVec | exact GlobalTheory.InertZeta.addVec | (intros; apply GlobalTheory.InertZeta.addVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries
open GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta.LeviSum

theorem int_geom (β y₀ : ℂ) (hβ : β ≠ 0) (h1 : ‖y₀ * β‖ < 1) (h2 : ‖y₀ / β‖ < 1) :
    HasSum (fun a : ℤ => β ^ a * y₀ ^ a.natAbs) ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · have e : ∀ n : ℕ, β ^ (n : ℤ) * y₀ ^ (n : ℤ).natAbs = (y₀ * β) ^ n := fun n => by
      simp [zpow_natCast, mul_pow, mul_comm]
    simp only [e]
    exact hasSum_geometric_of_norm_lt_one h1
  · have e : ∀ n : ℕ, β ^ (-((n : ℤ) + 1)) * y₀ ^ (-((n : ℤ) + 1)).natAbs = y₀ / β * (y₀ / β) ^ n := fun n => by
      rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        show (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 by omega, div_pow]
      field_simp
      ring
    simp only [e]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left (y₀ / β)

theorem q_pow (q : ℂ) (hq : q ≠ 0) (N : ℕ) (a : ℤ) :
    q ^ ((2 * N + 2) * a.toNat) * q ^ (-a * ((N : ℤ) + 1)) = (q ^ (N + 1)) ^ a.natAbs := by
  have h : ((a.natAbs : ℕ) : ℤ) = 2 * (a.toNat : ℤ) - a := by omega
  rw [← zpow_natCast, ← zpow_add₀ hq, ← pow_mul, ← zpow_natCast]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, h]
  push_cast
  ring

theorem core (Y : Type) (q N : ℕ) (l : Y → ℕ) (ψ : Y → ℂ) (β X₀ Z₀ : ℂ) (hq : 1 ≤ q) (hβ : β ≠ 0)
    (hy : ‖(q : ℂ) ^ (N + 1) * X₀‖ < 1) (h1 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖⁻¹ < 1)
    (hZ : HasSum (fun b => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) Z₀) :
    HasSum (fun p : ℤ × Y => ((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X₀ ^ (p.1.natAbs + l p.2) *
      jFac q N X₀) * (β ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * ψ p.2))
      ((1 - X₀) * (1 + q * X₀) * ((1 - (q : ℂ) ^ (N + 1) * X₀ * β)⁻¹ * (1 - (q : ℂ) ^ (N + 1) * X₀ / β)⁻¹) * Z₀) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set y₀ := (q : ℂ) ^ (N + 1) * X₀ with hy₀
  have hA := int_geom β y₀ hβ (by rw [norm_mul]; exact h1) (by rw [norm_div, div_eq_mul_inv]; exact h2)
  have sA : Summable (fun a : ℤ => ‖β ^ a * y₀ ^ a.natAbs‖) := summable_norm_iff.mpr hA.summable
  have sB : Summable (fun b : Y => ‖((q : ℂ) ^ 2 * X₀) ^ l b * ψ b‖) := summable_norm_iff.mpr hZ.summable
  have sAB : Summable (fun p : ℤ × Y => (β ^ p.1 * y₀ ^ p.1.natAbs) * (((q : ℂ) ^ 2 * X₀) ^ l p.2 * ψ p.2)) :=
    summable_mul_of_summable_norm (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) sA sB
  have hprod := (HasSum.mul (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) hA hZ sAB).mul_right (jFac q N X₀)
  have n1 : 1 - y₀ * β ≠ 0 := fun h => by
    have e : ‖y₀ * β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul] at e; linarith
  have n2 : 1 - y₀ / β ≠ 0 := fun h => by
    have e : ‖y₀ / β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_div, div_eq_mul_inv] at e; linarith
  have hβy : β - y₀ ≠ 0 := fun h => n2 (by rw [← sub_eq_zero.mp h, div_self hβ, sub_self])
  have hβy' : -y₀ + β ≠ 0 := by rwa [neg_add_eq_sub]
  have n3 : 1 - y₀ ^ 2 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    have := congrArg norm h
    rw [norm_one, norm_pow] at this
    nlinarith [norm_nonneg y₀]
  have ev : ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) * Z₀ * jFac q N X₀ =
      (1 - X₀) * (1 + q * X₀) * ((1 - y₀ * β)⁻¹ * (1 - y₀ / β)⁻¹) * Z₀ := by
    simp only [jFac]
    rw [← hy₀]
    field_simp
    ring
  rw [← ev]
  convert hprod using 1
  funext p
  obtain ⟨a, b⟩ := p
  simp only
  rw [hy₀, mul_pow, ← q_pow (q : ℂ) hq0 N a, pow_add, pow_add, mul_pow, ← pow_mul]
  ring

end GlobalTheory.InertZeta.LeviSum

namespace GlobalTheory.InertZeta


open LeviSum in
theorem step : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hyα hyα' H hZ
  subst hy
  have hg := core Y q N l φ₀ α X Z hq hα hy1 hyα hyα' hZ
  have hfib : ∀ ab : ℤ × Y, HasSum (fun c => X ^ ℓ ab.1 ab.2 c *
      (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * X ^ (ab.1.natAbs + l ab.2) * jFac q N X) *
        (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2)) :=
    fun ab => (H X hy1 ab.1 ab.2).mul_right _

  have hXn : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ = ‖(q : ℂ) ^ (N + 1) * X‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hαn : ‖((‖α‖ : ℝ) : ℂ)‖ = ‖α‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hZn : Summable (fun b => ((q : ℂ) ^ 2 * ((‖X‖ : ℝ) : ℂ)) ^ l b * ((‖φ₀ b‖ : ℝ) : ℂ)) := by
    have := Complex.summable_ofReal.mpr (summable_norm_iff.mpr hZ.summable)
    convert this using 2 with b
    push_cast [norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have hgn := core Y q N l (fun b => ((‖φ₀ b‖ : ℝ) : ℂ)) ((‖α‖ : ℝ) : ℂ) ((‖X‖ : ℝ) : ℂ) _ hq
    (by exact_mod_cast norm_ne_zero_iff.mpr hα) (hXn ▸ hy1) (by rw [hXn, hαn]; exact hyα)
    (by rw [hXn, hαn]; exact hyα') hZn.hasSum
  have hfibn : ∀ ab : ℤ × Y, HasSum (fun c => ((‖X‖ : ℝ) : ℂ) ^ ℓ ab.1 ab.2 c *
      (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ)))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (ab.1.natAbs + l ab.2) *
        jFac q N ((‖X‖ : ℝ) : ℂ)) *
        (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ))) :=
    fun ab => (H _ (hXn ▸ hy1) ab.1 ab.2).mul_right _
  have hnorm : ∀ p : (ℤ × Y) × C,
      ((‖X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)‖ : ℝ) : ℂ) =
      ((‖X‖ : ℝ) : ℂ) ^ ℓ p.1.1 p.1.2 p.2 *
        (((‖α‖ : ℝ) : ℂ) ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * ((‖φ₀ p.1.2‖ : ℝ) : ℂ)) := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_zpow, norm_zpow, Complex.norm_natCast]
    push_cast
    rfl
  have hsum : Summable (fun p : (ℤ × Y) × C =>
      X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)) := by
    rw [← summable_norm_iff, summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun ab => ?_, ?_⟩
    · rw [← Complex.summable_ofReal]
      exact (funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab).summable
    · rw [← Complex.summable_ofReal]
      refine hgn.summable.congr fun ab => ?_
      rw [Complex.ofReal_tsum]
      exact ((funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab)).tsum_eq.symm
  rw [hg.unique (hsum.hasSum.prod_fiberwise hfib)]
  exact hsum.hasSum

end GlobalTheory.InertZeta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeriesStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_summation_geometric_series : Step := by
  first | exact @GlobalTheory.InertZeta.step | exact GlobalTheory.InertZeta.step | (intros; apply GlobalTheory.InertZeta.step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPoints
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPointsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_rank_le_one_integral_points : SmallRank := by
  first | exact @GlobalTheory.InertZeta.smallRank | exact GlobalTheory.InertZeta.smallRank | (intros; apply GlobalTheory.InertZeta.smallRank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixLengthExistsOfElementaryDivisors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixLengthExistsOfElementaryDivisors
open GlobalTheory.InertZeta

noncomputable section
open Matrix Formalism.UG

namespace GlobalTheory.InertZeta

theorem prod_exp_eq {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]

theorem isInt_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hf i
  · exact zero_mem _

theorem hasLen_diagonal_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L := fun m => by
    show Valued.v (ϖ ^ m) ≤ 1
    rw [map_pow, hϖ]
    exact pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m
  refine ⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1),
    Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    have : ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]
      congr 1
      omega
    rw [this]; exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 ≤ d i
    · simp [h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]
    · simp only [h, if_false, zero_mul, zero_add, one_mul]
      rw [← zpow_natCast, ← zpow_add₀ h0]
      rw [show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]
    congr 1
    push_cast
    simp

theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.InertZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixLengthExistsOfElementaryDivisorsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLengthExists_of_elementaryDivisors : Smith → FracExists := by
  first | exact @GlobalTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.InertZeta.fracExists_of_smith <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {q n : ℕ}

theorem v_det_mat (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) : Valued.v (mat g).det = 1 := by
  have h : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have h1 := congrArg (fun M => Valued.v (det M)) h
  have hJ : IsInt (antiJ L n) := fun i j => by
    unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  simp only [det_mul, map_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσ,
    v_det_eq_one hJ hJ GlobalTheory.UnitarySwap.antiJ_mul_self, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, h1])

theorem secVal_pow {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ) (k : ℕ) :
    secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = varX q n (χ ϖ) s ^ k := by
  have h := P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val, varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem section_eq (hC : Completion) {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ}
    {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n χ s Φ) (g : GU σ n) {l : ℕ} (h : HasLen (mat g) l) :
    Φ (io1 σ n g) = varX q n (χ ϖ) s ^ l := by
  obtain ⟨U, V, C, hfr, hdet⟩ := h
  obtain ⟨k, hk, hk', hx⟩ := hC L ϖ σ q n hU g U V C hfr
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hK : (⟨k, hk⟩ : GD σ n) ∈ KD σ n := ⟨hk, hk'⟩
  have hp : ∀ x : Fin n → L, ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv ((mat g * C) *ᵥ x) ((mat g * C) *ᵥ x) := fun x => by
    change (blkMat finSumFinEquiv (mat g) 1 * k.1) *ᵥ _ = _
    rw [← mulVec_mulVec, hx, blkMat_mulVec, mulVec_mulVec, one_mulVec]
  have hP : io1 σ n g * ⟨k, hk⟩ ∈ PD σ n := mem_siegelOf.2 (keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
    rw [hp, pairVec_mem_diagSub])
  have hlev : leviMat finSumFinEquiv ((GD σ n).subtype (io1 σ n g * ⟨k, hk⟩)).1 = mat g * C := by
    refine Matrix.ext_of_mulVec_single fun j => funext fun i => ?_
    have := congrFun ((mem_siegelOf.1 hP).mulVec_diag (Pi.single j 1)) (finSumFinEquiv (.inl i))
    rw [hp, pairVec_inl, pairVec_inl] at this
    exact this.symm
  have h1 := hΦ ⟨_, hP⟩ _ (inv_mem hK)
  rw [mul_inv_cancel_right] at h1
  have h2 : Valued.v ((aD σ n ⟨_, hP⟩ * (ϖ ^ l)⁻¹ : Lˣ) : L) = 1 := by
    have hϖ : Valued.v (ϖ : L) = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
    rw [Units.val_mul, val_aOf, hlev, det_mul, map_mul, map_mul, v_det_mat hU.2.1, hdet, one_mul,
      Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow, hϖ, ← WithZero.exp_nsmul,
      ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  rw [h1, ← inv_mul_cancel_right (aD σ n ⟨_, hP⟩) (ϖ ^ l), secVal_mul hq, secVal_unit q hχ _ h2, one_mul, secVal_pow hU]

theorem closedForm_eq {q : ℕ} (hq : q ≠ 0) (n m : ℕ) (ε s : ℂ) (α : Fin (n / 2) → ℂˣ) (hε : ε = (-1) ^ m) :
    closedForm q n (varX q n ε s) (varY q ε s) α = stdL q n α ε (s + 1 / 2) / dFac q n m s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have h1 : ε * ((q ^ 2 : ℕ) : ℂ) ^ (-(s + 1 / 2)) = varY q ε s := by
    rw [varY, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    congr 2
    push_cast
    ring
  have h2 : (dFac q n m s)⁻¹ = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * varX q n ε s) := by
    rw [dFac, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [etaL, inv_inv, varX, hε, show -(2 * s + n - j) = (j : ℂ) + -(2 * s + n) by ring, Complex.cpow_add _ _ hq0,
      Complex.cpow_natCast, neg_pow (q : ℂ), pow_add]
    ring
  rw [div_eq_mul_inv, h2, stdL, h1, closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm (varY q ε s)]
  rcases Nat.even_or_odd n with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

theorem unramDoublingInert : UnramDoublingInert := by
  intro L _ _ _ ϖ σ q n hU _ _ μ _ hμ χ hχ s Φ hΦ α w hw
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hF : FracExists := T.matrixLengthExists_of_elementaryDivisors T.elementaryDivisors_exist_discretelyValued
  have hsec : (fun g => Φ (io1 σ n g) * w g) = fun g => varX q n (χ ϖ) s ^ len (mat g) * w g := funext fun g => by
    rw [section_eq T.doubledLattice_primitive_isotropic_frame_completion hU hχ hΦ g (hF L ϖ n hU.2.2.2.1 _ (det_mat_ne_zero g))]
  have hint : ∀ Z, HasSum (fun x : GU σ n ⧸ KU σ n => varX q n (χ ϖ) s ^ len (mat x.out) * w x.out) Z →
      Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = Z := fun Z hZ => by
    rw [hsec]
    refine T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1 hμ _ Z (fun g k hk => ?_) hZ
    have h1 := hw.1 1 ⟨k, hk⟩ g
    have h2 := len_mat_mul (one_mem _) hk g
    simp only [OneMemClass.coe_one, one_mul] at h1 h2
    rw [h1, h2]
  refine ⟨fun hD => ?_, fun hn => hint 1 (hasSum_small T.unitary_rank_le_one_integral_points hU hn (fun g => varX q n (χ ϖ) s ^ len (mat g) * w g)
    fun k hk => ?_)⟩
  · obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ))
      fun i => (α i).ne_zero
    have h2 := hasSum_spherical hF (T.leviRadicalProductLength_of_lattice_steps T.lattice_add_vector_det_valuation T.dual_inter_eq_sum' T.blockTriangular_row_lattice_triangular_basis T.unitary_heisenberg_radical_coordinates)
      (T.smallRadicalCosetCount_of_heisenberg T.unitary_heisenberg_radical_coordinates (T.integralLatticeInverseIndex_of_elementaryDivisors T.elementaryDivisors_exist_discretelyValued) T.traceZero_integers_index_in_uniformizer_multiples) (T.small_corner_of_heisenberg_duality T.unitary_heisenberg_radical_coordinates T.dual_inter_eq_sum') T.length_count_generating_series_formula (T.unitaryIwasawaCosetSurj_of_leviElementExists T.exists_unitary_block_diagonal_levi_element)
      T.unitary_iwasawa_cells_disjoint T.exists_unitary_block_diagonal_levi_element (T.sphericalInductionTransitivity_of_leviExists T.exists_unitary_block_diagonal_levi_element) T.unitary_rank_le_one_integral_points T.unitary_levi_summation_geometric_series hU (n / 2) n (by omega) (by omega)
      (fun i => (α i : ℂ)) (varX q n (χ ϖ) s) (varY q (χ ϖ) s) φ (fun i => (α i).ne_zero) (by
        rw [varX, varY, neg_add, neg_add, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one,
          Complex.cpow_neg _ (n : ℂ), Complex.cpow_natCast]
        field_simp) hD.1 hD.2 hφ h1
    have h3 := hint _ (T.biInvariant_replace_same_double_coset_sums _ (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) (fun g => varX q n (χ ϖ) s ^ len (mat g)) w φ _
      (fun a b g => by simp only [len_mat_mul a.2 b.2]) hw.1 (fun g => by
        rw [hw.2.2 _ (Final.DosetIndMem _ _ ℂ g), Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
          (fun i => (α i).ne_zero) _ (Final.DosetIndMem _ _ ℂ g) φ hφ, Pi.smul_apply, h1, smul_eq_mul, mul_one]) h2)
    exact ⟨h3.1, h3.2, fun m hm => h3.2.trans (closedForm_eq hq n m _ s α hm)⟩
  · have h1 := hw.1 1 ⟨k, hk⟩ 1
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [len_of_mem hk, h1, hw.2.1, pow_zero, mul_one]

end GlobalTheory.InertZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlaceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedDoublingIntegral_inert_place : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert := by
  first | exact @GlobalTheory.InertZeta.unramDoublingInert | exact GlobalTheory.InertZeta.unramDoublingInert | (intros; apply GlobalTheory.InertZeta.unramDoublingInert <;> assumption)
end
