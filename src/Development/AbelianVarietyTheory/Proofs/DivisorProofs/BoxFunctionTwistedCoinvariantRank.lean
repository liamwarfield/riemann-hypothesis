module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrix
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def rowOpMat (i₀ : A) (w : A → k) : Matrix A A k :=
  replicateCol Unit (Pi.single i₀ (1 : k)) * replicateRow Unit w

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowOpMat_apply (i₀ : A) (w : A → k) (i a : A) : rowOpMat i₀ w i a = if i = i₀ then w a else 0 := by
  by_cases h : i = i₀
  · subst h; simp [rowOpMat, Matrix.mul_apply]
  · simp [rowOpMat, Matrix.mul_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowOpMat_mul_self (i₀ : A) (w : A → k) (hw : w i₀ = 0) : rowOpMat i₀ w * rowOpMat i₀ w = 0 := by
  ext i j
  simp [Matrix.mul_apply, rowOpMat_apply, hw]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in
theorem rowOpMat_mul_apply (i₀ : A) (w : A → k) (X : Matrix A D k) (i : A) (j : D) :
    (rowOpMat i₀ w * X) i j = if i = i₀ then ∑ a, w a * X a j else 0 := by
  by_cases h : i = i₀
  · simp [Matrix.mul_apply, rowOpMat_apply, h]
  · simp [Matrix.mul_apply, rowOpMat_apply, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_one_add_rowOpMat (i₀ : A) (w : A → k) (hw : w i₀ = 0) : (1 + rowOpMat i₀ w).det = 1 := by
  rw [rowOpMat, det_one_add_replicateCol_mul_replicateRow]
  simp [hw]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : GL A k :=
  ⟨1 + rowOpMat i₀ w, 1 - rowOpMat i₀ w,
    by simp [add_mul, mul_sub, rowOpMat_mul_self i₀ w hw],
    by simp [sub_mul, mul_add, rowOpMat_mul_self i₀ w hw]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem gdet_unipRowGL (i₀ : A) (w : A → k) (hw : w i₀ = 0) : gdet (unipRowGL i₀ w hw) = 1 :=
  Units.ext (det_one_add_rowOpMat i₀ w hw)

theorem valuation_rowSum_le (i₀ : A) (w : A → k) (hw0 : w i₀ = 0) (hw : ∀ a, valuation k (w a) ≤ 1)
    (Z : A → k) (b : ValueGroupWithZero k) (hZ : ∀ a, a ≠ i₀ → valuation k (Z a) ≤ b) :
    valuation k (∑ a, w a * Z a) ≤ b := by
  refine Valuation.map_sum_le _ fun a _ => ?_
  by_cases ha : a = i₀
  · subst ha; simp [hw0]
  · rw [map_mul]
    exact (mul_le_mul' (hw a) (hZ a ha)).trans (by rw [one_mul])

theorem omA_unipRowGL_boxFn (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (i₀ : A) (w : A → k) (hw0 : w i₀ = 0)
    (hw : ∀ a, valuation k (w a) ≤ 1) (C : Matrix A D k) (m : ℕ) :
    omA ν β (unipRowGL i₀ w hw0) 1 (boxFn ϖ C (fun _ => m)) =
      boxFn ϖ (updateRow C i₀ (C i₀ + w ᵥ* C)) (fun _ => m) := by
  funext X
  rw [omA_one_apply, gdet_unipRowGL]
  simp only [map_one, inv_one, Units.val_one, apow_one, one_mul]
  have hinv : ((unipRowGL i₀ w hw0)⁻¹).val = 1 - rowOpMat i₀ w := rfl
  rw [hinv]
  set C' := updateRow C i₀ (C i₀ + w ᵥ* C)
  have hT : ∀ i j, ((1 - rowOpMat i₀ w : Matrix A A k) * X : Matrix A D k) i j - C i j =
      (X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) := by
    intro i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, rowOpMat_mul_apply]
    by_cases hi : i = i₀
    · subst hi
      simp only [C', updateRow_self, if_true, Pi.add_apply, vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib]
      ring
    · simp [C', hi]
  have hrow : ∀ a, a ≠ i₀ → ∀ j, X a j - C' a j = X a j - C a j := fun a ha j => by simp [C', ha]
  have hbox : (1 - rowOpMat i₀ w) * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ C' (fun _ => m) := by
    simp only [box, Set.mem_setOf_eq]
    constructor
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hT, if_neg ha, sub_zero, hrow a ha] at this
      have := h i j
      rw [hT] at this
      rw [show X i j - C' i j = ((X i j - C' i j) - (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0)) +
        (if i = i₀ then ∑ a, w a * (X a j - C a j) else 0) by ring]
      refine Valuation.map_add_le _ this ?_
      split_ifs
      · exact hS
      · simp
    · intro h i j
      have hS : valuation k (∑ a, w a * (X a j - C a j)) ≤ valuation k ((ϖ ^ m : kˣ) : k) :=
        valuation_rowSum_le i₀ w hw0 hw _ _ fun a ha => by
          have := h a j
          rwa [hrow a ha] at this
      rw [hT]
      refine Valuation.map_sub_le _ (h i j) ?_
      split_ifs
      · exact hS
      · simp
  unfold boxFn
  by_cases hX : X ∈ box ϖ C' (fun _ => m)
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (hbox.2 hX)]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX (hbox.1 h))]
end GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (t : Fin r → k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → (∀ l, valuation k (t l) ≤ valuation k ((ϖ ^ c : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ (C i₀ + t ᵥ* (H * C))) (fun _ => m) - GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ r c m C H t hH0 hH ht
  have hw0 : (t ᵥ* H) i₀ = 0 := by simp [vecMul, dotProduct, hH0]
  have hw : ∀ a, valuation k ((t ᵥ* H) a) ≤ 1 := fun a => by
    show valuation k (∑ l, t l * H l a) ≤ 1
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    refine (mul_le_mul' (ht l) (hH l a)).trans (le_of_eq ?_)
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← vecMul_vecMul, ← GlobalTheory.RankCoinv.omA_unipRowGL_boxFn ν β ϖ i₀ (t ᵥ* H) hw0 hw C m]
  exact GlobalTheory.RankCoinv.sub_mem_twistSpan ν β _ (GlobalTheory.RankCoinv.boxFn_mem_SB ϖ C _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrixStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_action_bounded_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (t : Fin r → k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → (∀ l, valuation k (t l) ≤ valuation k ((ϖ ^ c : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ (C i₀ + t ᵥ* (H * C))) (fun _ => m) - GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan | exact GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan | (intros; apply GlobalTheory.RankCoinv.boxFn_unip_row_sub_mem_twistSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
open ValuativeRel Matrix

namespace GlobalTheory

theorem rows_mem_span_of_isUnit_mul (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K)
    (Q : Matrix D (Fin r) K) (hX : X.rank ≤ r) (hU : IsUnit (H * X * Q)) :
    ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  intro i
  have hle : Submodule.span K (Set.range (H * X)) ≤ Submodule.span K (Set.range X) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (H * X) j = ∑ a, H j a • X a := by
      ext d; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : r ≤ (H * X).rank := by
    have := Matrix.rank_mul_le_left (H * X) Q
    rw [Matrix.rank_of_isUnit _ hU] at this
    simpa using this
  have heq : Submodule.span K (Set.range (H * X)) = Submodule.span K (Set.range X) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have e1 : X.rank = Module.finrank K (Submodule.span K (Set.range X)) :=
      Matrix.rank_eq_finrank_span_row X
    have e2 : (H * X).rank = Module.finrank K (Submodule.span K (Set.range (H * X))) :=
      Matrix.rank_eq_finrank_span_row (H * X)
    omega
  have hi : X i ∈ Submodule.span K (Set.range (H * X)) := heq ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hi
  refine ⟨c, ?_⟩
  rw [← hc]
  ext d
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalFormStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_in_span_of_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K) (Q : Matrix D (Fin r) K), X.rank ≤ r → IsUnit (H * X * Q) → ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  first | exact @GlobalTheory.rows_mem_span_of_isUnit_mul | exact GlobalTheory.rows_mem_span_of_isUnit_mul | (intros; apply GlobalTheory.rows_mem_span_of_isUnit_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuation
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_of_add_vecMul {r : ℕ} {u t : ValueGroupWithZero k} (hu : u < 1) (s : Fin r → k)
    (E : Matrix (Fin r) (Fin r) k) (hE : ∀ l j, valuation k (E l j) ≤ u)
    (hw : ∀ l, valuation k ((s + s ᵥ* E) l) ≤ t) (l : Fin r) : valuation k (s l) ≤ t := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨l₁, -, hl₁⟩ := Finset.exists_max_image Finset.univ (fun j => valuation k (s j)) ⟨l, Finset.mem_univ _⟩
  have hM : t < valuation k (s l₁) := hlt.trans_le (hl₁ l (Finset.mem_univ _))
  have hM0 : 0 < valuation k (s l₁) := lt_of_le_of_lt zero_le' hM
  have h1 : valuation k ((s ᵥ* E) l₁) ≤ valuation k (s l₁) * u := by
    simp only [Matrix.vecMul, dotProduct]
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hl₁ j (Finset.mem_univ _)) (hE j l₁)
  have h3 := Valuation.map_sub_le (valuation k) ((hw l₁).trans (le_max_left t (valuation k (s l₁) * u)))
    (h1.trans (le_max_right _ _))
  rw [Pi.add_apply, add_sub_cancel_right] at h3
  have h4 : valuation k (s l₁) * u < valuation k (s l₁) := mul_lt_of_lt_one_right hM0 hu
  rcases le_max_iff.1 h3 with h | h
  · exact absurd h (not_le.2 hM)
  · exact absurd h (not_le.2 h4)

theorem val_pow (ϖ : kˣ) (n : ℕ) : valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

theorem mem_max_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ 1 ↔ valuation k (x : k) ≤ valuation k (ϖ : k) := by
  rw [pow_one, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  exact Iff.rfl

variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]


omit [Fintype A] [Fintype D] [DecidableEq D] in
theorem mem_box_update {ϖ : kˣ} {C X : Matrix A D k} {i₀ : A} {m : ℕ} (hC : ∀ j, C i₀ j = 0) :
    X ∈ box ϖ C (Function.update (fun _ => m) i₀ (m - 1)) ↔
      (∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m) ∧
        ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1) := by
  simp only [box, Set.mem_setOf_eq, val_pow]
  constructor
  · intro h
    exact ⟨fun i hi j => by simpa [Function.update_of_ne hi] using h i j, fun j => by simpa [hC] using h i₀ j⟩
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : i = i₀
    · subst hi; simpa [hC] using h2 j
    · simpa [Function.update_of_ne hi] using h1 i hi j


omit [Fintype A] [Fintype D] [DecidableEq D] in
theorem mem_box_updateRow {ϖ : kˣ} {C X : Matrix A D k} {i₀ : A} {m : ℕ} (R : D → k) :
    X ∈ box ϖ (C.updateRow i₀ R) (fun _ => m) ↔
      (∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m) ∧
        ∀ j, valuation k (X i₀ j - R j) ≤ valuation k (ϖ : k) ^ m := by
  simp only [box, Set.mem_setOf_eq, val_pow]
  constructor
  · intro h
    exact ⟨fun i hi j => by simpa [updateRow_ne hi] using h i j, fun j => by simpa using h i₀ j⟩
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : i = i₀
    · subst hi; simpa using h2 j
    · simpa [updateRow_ne hi] using h1 i hi j

end GlobalTheory.CountTranslates

namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type} [Fintype D] [DecidableEq D]

def shiftRow (ϖ : kˣ) (m : ℕ) {r : ℕ} (b : Fin r → Res k 1) : Fin r → k :=
  fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)

theorem inv_pow_mul_pow_le {u : ValueGroupWithZero k} (hu : u < 1) (hu0 : u ≠ 0) {c m : ℕ} (hcm : c + 1 ≤ m) :
    (u ^ c)⁻¹ * u ^ m ≤ u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = c + 1 + n := ⟨m - (c + 1), by omega⟩
  rw [pow_add, pow_succ, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hu0)]
  exact mul_le_of_le_one_right' (pow_le_one' hu.le n)


omit [DecidableEq D] in
theorem val_shiftRow_le (ϖ : kˣ) {r m : ℕ} (Y : Matrix (Fin r) D k) (hY : ∀ l j, Y l j ∈ 𝒪[k])
    (b : Fin r → Res k 1) (j : D) :
    valuation k ((shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ (m - 1) := by
  simp only [Matrix.vecMul, dotProduct, shiftRow]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul, map_pow]
  calc _ ≤ valuation k (ϖ : k) ^ (m - 1) * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 (Quotient.out (b l)).2))
          ((Valuation.mem_integer_iff _ _).1 (hY l j))
    _ = _ := by rw [mul_one, mul_one]


omit [DecidableEq D] in
theorem shiftRow_unique {ϖ : kˣ} (hϖ : IsUnif ϖ) {r m : ℕ} (hm : 1 ≤ m) (Y : Matrix (Fin r) D k)
    (Q : Matrix D (Fin r) k) (hQ : ∀ j l, Q j l ∈ 𝒪[k]) (hYQ : Y * Q = 1) (x : D → k)
    (b b' : Fin r → Res k 1)
    (hb : ∀ j, valuation k (x j - (shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m)
    (hb' : ∀ j, valuation k (x j - (shiftRow ϖ m b' ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m) :
    b = b' := by
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  let δ : Fin r → k := fun l =>
    (ϖ : k) ^ (m - 1) * (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k))
  have hδ : δ ᵥ* Y = shiftRow ϖ m b ᵥ* Y - shiftRow ϖ m b' ᵥ* Y := by
    rw [← Matrix.sub_vecMul]; congr 1; funext l; simp [δ, shiftRow, mul_sub]
  have h1 : ∀ j, valuation k ((δ ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m := fun j => by
    have := Valuation.map_sub_le (valuation k) (hb' j) (hb j)
    rwa [sub_sub_sub_cancel_left, ← Pi.sub_apply, ← hδ] at this
  have h2 : δ = (δ ᵥ* Y) ᵥ* Q := by rw [Matrix.vecMul_vecMul, hYQ, Matrix.vecMul_one]
  have h3 : ∀ l, valuation k (δ l) ≤ valuation k (ϖ : k) ^ m := fun l => by
    rw [h2]
    show valuation k (∑ j, (δ ᵥ* Y) j * Q j l) ≤ _
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    exact (mul_le_mul' (h1 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])
  funext l
  have h4 : valuation k (((Quotient.out (b l) : 𝒪[k]) : k) - ((Quotient.out (b' l) : 𝒪[k]) : k)) ≤
      valuation k (ϖ : k) := by
    have h5 := h3 l
    have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
      rw [← pow_succ]; congr 1; omega
    simp only [δ, map_mul, map_pow] at h5
    rw [hm'] at h5
    exact (mul_le_mul_iff_right₀ (zero_lt_iff.2 (pow_ne_zero _ hu0))).1 h5
  rw [← Ideal.Quotient.mk_out (b l), ← Ideal.Quotient.mk_out (b' l)]
  exact Ideal.Quotient.eq.2 ((mem_max_iff hϖ _).2 h4)


omit [DecidableEq D] in
theorem shiftRow_exists {ϖ : kˣ} (hϖ : IsUnif ϖ) {r c m : ℕ} (hcm : c + 1 ≤ m) (Y Z : Matrix (Fin r) D k)
    (hY : ∀ l j, Y l j ∈ 𝒪[k])
    (hZ : ∀ l j, valuation k (Z l j) ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m)
    (s : Fin r → k) (hs : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1)) :
    ∃ b : Fin r → Res k 1, ∀ j,
      valuation k ((s ᵥ* (Y + Z)) j - (shiftRow ϖ m b ᵥ* Y) j) ≤ valuation k (ϖ : k) ^ m := by
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hp0 : (ϖ : k) ^ (m - 1) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have hvp : 0 < valuation k (ϖ : k) ^ (m - 1) := zero_lt_iff.2 (pow_ne_zero _ hu0)
  have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
    rw [← pow_succ]; congr 1; omega
  have htt : ∀ l, ((ϖ : k) ^ (m - 1))⁻¹ * s l ∈ 𝒪[k] := fun l => by
    rw [Valuation.mem_integer_iff, map_mul, map_inv₀, map_pow, inv_mul_le_iff₀ hvp, mul_one]; exact hs l
  let b₀ : Fin r → Res k 1 := fun l => Ideal.Quotient.mk _ ⟨_, htt l⟩
  have hb : ∀ l, valuation k (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l) ≤
      valuation k (ϖ : k) :=
    fun l => (mem_max_iff hϖ _).1 (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (b₀ l)))
  refine ⟨b₀, fun j => ?_⟩
  have e : (s ᵥ* (Y + Z)) j - (shiftRow ϖ m b₀ ᵥ* Y) j = ((s - shiftRow ϖ m b₀) ᵥ* Y) j + (s ᵥ* Z) j := by
    rw [Matrix.vecMul_add, Matrix.sub_vecMul]; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  refine Valuation.map_add_le _ ?_ ?_
  · show valuation k (∑ l, (s - shiftRow ϖ m b₀) l * Y l j) ≤ _
    refine Valuation.map_sum_le _ fun l _ => ?_
    have e2 : (s - shiftRow ϖ m b₀) l = -((ϖ : k) ^ (m - 1) *
        (((Quotient.out (b₀ l) : 𝒪[k]) : k) - ((ϖ : k) ^ (m - 1))⁻¹ * s l)) := by
      simp only [Pi.sub_apply, shiftRow]; rw [mul_sub, mul_inv_cancel_left₀ hp0]; ring
    rw [e2, map_mul, Valuation.map_neg, map_mul, map_pow, hm']
    exact (mul_le_mul' (mul_le_mul' le_rfl (hb l)) ((Valuation.mem_integer_iff _ _).1 (hY l j))).trans
      (by rw [mul_one])
  · show valuation k (∑ l, s l * Z l j) ≤ _
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, hm']
    exact mul_le_mul' (hs l) ((hZ l j).trans (inv_pow_mul_pow_le hu hu0 hcm))

end GlobalTheory.CountTranslates

namespace GlobalTheory.CountTranslates
open GlobalTheory.SplitFlip GlobalTheory.RankCoinv

theorem boxFn_sub_sum_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) - ∑ b : Fin r → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hY hQ hYQ hC0
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hm' : valuation k (ϖ : k) ^ m = valuation k (ϖ : k) ^ (m - 1) * valuation k (ϖ : k) := by
    rw [← pow_succ]; congr 1; omega
  have hmm : valuation k (ϖ : k) ^ m ≤ valuation k (ϖ : k) ^ (m - 1) := by
    rw [hm']; exact mul_le_of_le_one_right' hu.le
  have hHv' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k) ^ c)⁻¹ := fun l i => by
    have := hHv l i
    rwa [Units.val_inv_eq_inv_val, map_inv₀, val_pow] at this
  rw [mem_lowRank]
  refine ⟨sub_mem (boxFn_mem_SB _ _ _) (Submodule.sum_mem _ fun b _ => boxFn_mem_SB _ _ _), fun X hX => ?_⟩
  have hXr : X.rank ≤ r := Nat.lt_succ_iff.1 hX
  simp only [Pi.sub_apply, Finset.sum_apply, boxFn]
  rw [sub_eq_zero]
  change _ = ∑ b : Fin r → Res k 1, (box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) fun _ => m).indicator 1 X
  by_cases hrows : ∀ i, i ≠ i₀ → ∀ j, valuation k (X i j - C i j) ≤ valuation k (ϖ : k) ^ m
  · by_cases hi0 : ∀ j, valuation k (X i₀ j) ≤ valuation k (ϖ : k) ^ (m - 1)
    · let E : Matrix (Fin r) (Fin r) k := H * (X - C) * Q
      have hHXC : ∀ l j, valuation k ((H * (X - C)) l j) ≤
          (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m := by
        intro l j
        rw [Matrix.mul_apply]
        refine Valuation.map_sum_le _ fun i _ => ?_
        by_cases hi : i = i₀
        · subst hi; simp [hH0]
        · rw [map_mul]; exact mul_le_mul' (hHv' l i) (by simpa [Matrix.sub_apply] using hrows i hi j)
      have hE : ∀ l j, valuation k (E l j) ≤ valuation k (ϖ : k) := by
        intro l j
        refine (?_ : _ ≤ (valuation k (ϖ : k) ^ c)⁻¹ * valuation k (ϖ : k) ^ m).trans
          (inv_pow_mul_pow_le hu hu0 hcm)
        show valuation k (∑ a, (H * (X - C)) l a * Q a j) ≤ _
        refine Valuation.map_sum_le _ fun a _ => ?_
        rw [map_mul]
        exact (mul_le_mul' (hHXC l a) ((Valuation.mem_integer_iff _ _).1 (hQ a j))).trans (by rw [mul_one])
      have hHXQ : H * X * Q = 1 + E := by
        simp only [E, Matrix.mul_sub, Matrix.sub_mul, hYQ]; abel
      have hunit : IsUnit (H * X * Q) := by
        rw [← vecMul_injective_iff_isUnit]
        intro s s' hss
        have h0 : (s - s') + (s - s') ᵥ* E = 0 := by
          have : (s - s') ᵥ* (H * X * Q) = 0 := by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hss
          rwa [hHXQ, Matrix.vecMul_add, Matrix.vecMul_one] at this
        funext l
        have := val_le_of_add_vecMul hu (s - s') E hE (t := 0) (fun l => by rw [h0]; simp) l
        exact sub_eq_zero.1 ((Valuation.zero_iff _).1 (le_zero_iff.1 this))
      obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X H Q hXr hunit i₀
      have hsv : ∀ l, valuation k (s l) ≤ valuation k (ϖ : k) ^ (m - 1) := by
        refine val_le_of_add_vecMul hu s E hE fun l => ?_
        have e : s + s ᵥ* E = X i₀ ᵥ* Q := by
          rw [hs, Matrix.vecMul_vecMul, hHXQ, Matrix.vecMul_add, Matrix.vecMul_one]
        rw [e]
        show valuation k (∑ j, X i₀ j * Q j l) ≤ _
        refine Valuation.map_sum_le _ fun j _ => ?_
        rw [map_mul]
        exact (mul_le_mul' (hi0 j) ((Valuation.mem_integer_iff _ _).1 (hQ j l))).trans (by rw [mul_one])
      have hXs : X i₀ = s ᵥ* (H * C + H * (X - C)) := by
        rw [hs]; congr 1; rw [Matrix.mul_sub]; abel
      obtain ⟨b₀, hb₀⟩ := shiftRow_exists hϖ hcm (H * C) (H * (X - C)) hY hHXC s hsv
      rw [← hXs] at hb₀
      have hmem : ∀ b, X ∈ box ϖ (C.updateRow i₀ (shiftRow ϖ m b ᵥ* (H * C))) (fun _ => m) ↔ b = b₀ := fun b =>
        ⟨fun h => shiftRow_unique hϖ (by omega) (H * C) Q hQ hYQ (X i₀) b b₀ ((mem_box_updateRow _).1 h).2 hb₀,
          fun h => h ▸ (mem_box_updateRow _).2 ⟨hrows, hb₀⟩⟩
      rw [Set.indicator_of_mem ((mem_box_update hC0).2 ⟨hrows, hi0⟩), Finset.sum_eq_single b₀
        (fun b _ hb => Set.indicator_of_notMem (fun h => hb ((hmem b).1 h)) _) (by simp),
        Set.indicator_of_mem ((hmem b₀).2 rfl)]
    · rw [Set.indicator_of_notMem (fun h => hi0 ((mem_box_update hC0).1 h).2)]
      refine (Finset.sum_eq_zero fun b _ => Set.indicator_of_notMem (fun h => hi0 fun j => ?_) _).symm
      have h2 := ((mem_box_updateRow _).1 h).2 j
      rw [← sub_add_cancel (X i₀ j) ((shiftRow ϖ m b ᵥ* (H * C)) j)]
      exact Valuation.map_add_le _ (h2.trans hmm) (val_shiftRow_le ϖ (H * C) hY b j)
  · rw [Set.indicator_of_notMem (fun h => hrows ((mem_box_update hC0).1 h).1)]
    exact (Finset.sum_eq_zero fun b _ =>
      Set.indicator_of_notMem (fun h => hrows ((mem_box_updateRow _).1 h).1) _).symm

end GlobalTheory.CountTranslates
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuationStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_box_bounded_valuation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) - ∑ b : Fin r → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) := by
  first | exact @GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank | exact GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank | (intros; apply GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalAction
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem omA_diag_boxFn_succ :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ ν β i₀ C hC m n
  have hdet : GlobalTheory.SplitFlip.gdet (GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ)) = ϖ := by
    rw [GlobalTheory.SplitFlip.gdet, GlobalTheory.SplitFlip.det_diagGL, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hinv : ((GlobalTheory.SplitFlip.diagGL (Function.update (1 : A → kˣ) i₀ ϖ))⁻¹).val =
      diagonal fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k) := rfl
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have key : ∀ X : Matrix A D k,
      (diagonal (fun i => (((Function.update (1 : A → kˣ) i₀ ϖ i)⁻¹ : kˣ) : k)) * X) ∈
        box ϖ C (Function.update (fun _ => m) i₀ n) ↔ X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
    intro X
    simp only [box, Set.mem_setOf_eq, diagonal_mul]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, hC, sub_zero, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        pow_succ, Units.val_mul, map_mul, map_inv₀, map_pow]
      rw [inv_mul_le_iff₀ h0, mul_comm (valuation k (ϖ : k))]
    · simp [Function.update_of_ne hi]
  funext X
  rw [GlobalTheory.RankCoinv.omA_one_apply, hdet, Pi.smul_apply, smul_eq_mul, hinv]
  congr 1
  unfold boxFn
  by_cases hX : X ∈ box ϖ C (Function.update (fun _ => m) i₀ (n + 1))
  · rw [Set.indicator_of_mem ((key X).2 hX), Set.indicator_of_mem hX]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hX ((key X).1 h)), Set.indicator_of_notMem hX]

end GlobalTheory.RankCoinv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalActionStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_diagonal_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (i₀ : A) (C : Matrix A D k), (∀ j, C i₀ j = 0) → ∀ m n : ℕ, GlobalTheory.SplitFlip.omA ν β (GlobalTheory.SplitFlip.diagGL (Function.update 1 i₀ ϖ)) 1 (GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ n)) = ((((ν ϖ)⁻¹ : ℂˣ) : ℂ) * GlobalTheory.SplitFlip.apow ϖ (-(Fintype.card D : ℂ) / 2)) • GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (n + 1)) := by
  first | exact @GlobalTheory.RankCoinv.omA_diag_boxFn_succ | exact GlobalTheory.RankCoinv.omA_diag_boxFn_succ | (intros; apply GlobalTheory.RankCoinv.omA_diag_boxFn_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariant
open ValuativeRel Matrix

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hν1 i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0
  set g : Matrix A D k → ℂ := boxFn ϖ C (fun _ => m) with hg
  set g' : Matrix A D k → ℂ := boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) with hg'
  set lam : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) * apow ϖ (-(Fintype.card D : ℂ) / 2) with hlam
  set N : ℕ := Fintype.card (Fin r → GlobalTheory.SplitFlip.Res k 1) with hN
  let F : (Fin r → GlobalTheory.SplitFlip.Res k 1) → Matrix A D k → ℂ := fun b => boxFn ϖ (Matrix.updateRow C i₀
    ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m)

  have hz := GlobalTheory.T.box_function_diagonal_action k A D ϖ ν β i₀ C hC0 m (m - 1)
  have hupd : Function.update (fun _ : A => m) i₀ m = fun _ => m := Function.update_eq_self _ _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hupd] at hz
  have h3 : lam • g - g' ∈ twistSpan ν β := by
    rw [hlam, hg, ← hz]; exact sub_mem_twistSpan ν β _ (boxFn_mem_SB _ _ _)

  have h1 : g' - ∑ b, F b ∈ lowRank (r + 1) :=
    GlobalTheory.T.integral_box_bounded_valuation k A D ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0

  have hv1 : valuation k (ϖ : k) ≤ 1 := by rw [hϖ]; exact (uniformizer_lt_one (R := k)).le
  have h2 : ∀ b, F b - g ∈ twistSpan ν β := by
    intro b
    have ht : ∀ l, valuation k ((ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
      intro l
      have hout : valuation k ((Quotient.out (b l) : 𝒪[k]) : k) ≤ 1 := (Quotient.out (b l)).2
      rw [map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
      exact (mul_le_of_le_one_right' hout).trans (pow_le_pow_right_of_le_one' hv1 (by omega))
    have hu := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C H _ hH0 hHv ht
    have hrow : C i₀ = 0 := funext hC0
    rw [hrow, zero_add] at hu
    exact hu

  have key : (lam - (N : ℂ)) • g ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    have e : (lam - (N : ℂ)) • g = (g' - ∑ b, F b) + ∑ b, (F b - g) + (lam • g - g') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, sub_smul, Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    exact add_mem (add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun b _ => h2 b))) (Submodule.mem_sup_right h3)

  have hne : lam - (N : ℂ) ≠ 0 := by
    intro h
    have hl : lam = N := sub_eq_zero.1 h
    set a : ℝ := nabs k ϖ ^ (-(Fintype.card D : ℝ) / 2) with ha_def
    have hapos : 0 < a := Real.rpow_pos_of_pos (nabs_pos ϖ) _
    have ha : apow ϖ (-(Fintype.card D : ℂ) / 2) = (a : ℂ) := by
      rw [apow, ha_def, Complex.ofReal_cpow (nabs_pos ϖ).le]
      push_cast; ring_nf
    set u : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) with hu_def
    have hua : u * a = N := by rw [← ha]; exact hl
    have hu : u = ((N / a : ℝ) : ℂ) := by
      have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hapos.ne'
      rw [Complex.ofReal_div, Complex.ofReal_natCast, ← hua, mul_div_cancel_right₀ _ ha0]
    have hnorm : ‖u‖ = 1 := by
      rw [hu_def, Units.val_inv_eq_inv_val, norm_inv, hν, inv_one]
    rw [hu, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hapos.le)] at hnorm
    have hu1 : u = 1 := by rw [hu, hnorm]; simp
    apply hν1
    have : (ν ϖ)⁻¹ = 1 := Units.ext (by simpa [hu_def] using hu1)
    exact inv_eq_one.1 this
  exact (Submodule.smul_mem_iff _ hne).1 key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row | exact GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row | (intros; apply GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRank
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv.Recentre

variable {k : Type} [Field k] [ValuativeRel k]

theorem vecMul_bound {r : ℕ} (E : Matrix (Fin r) (Fin r) k) (δ b : ValueGroupWithZero k)
    (hδ : δ < 1) (hE : ∀ l l', valuation k (E l l') ≤ δ) (s w : Fin r → k)
    (hw : ∀ l, valuation k (w l) ≤ b) (hs : s ᵥ* (1 + E) = w) : ∀ l, valuation k (s l) ≤ b := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · intro l; exact isEmptyElim l
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty
  have key : s l₀ = w l₀ - ∑ l, s l * E l l₀ := by
    have := congrFun hs l₀
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this
    rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ := by
    apply Valuation.map_sum_le
    intro l _
    rw [map_mul]
    exact mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)
  have hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ) := by
    calc valuation k (s l₀) = valuation k (w l₀ - ∑ l, s l * E l l₀) := by rw [← key]
      _ ≤ max (valuation k (w l₀)) (valuation k (∑ l, s l * E l l₀)) := Valuation.map_sub _ _ _
      _ ≤ max b (valuation k (s l₀) * δ) := max_le_max (hw l₀) hsum
  have hμb : valuation k (s l₀) ≤ b := by
    rcases le_max_iff.1 hμ with h | h
    · exact h
    · by_cases h0 : valuation k (s l₀) = 0
      · rw [h0]; exact zero_le'
      · exfalso
        have h2 := mul_le_mul_left h (valuation k (s l₀))⁻¹
        rw [mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
        exact absurd hδ (not_lt.2 h2)
  exact fun l => (hl₀ l (Finset.mem_univ _)).trans hμb

end GlobalTheory.RankCoinv.Recentre

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀
  classical
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hv0 : valuation k (ϖ : k) ≠ 0 := by simp
  have vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n := by intro n; simp
  have vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹ := by simp
  by_cases hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r
  swap
  · apply Submodule.mem_sup_left
    refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩
    unfold GlobalTheory.RankCoinv.boxFn
    apply Set.indicator_of_notMem
    intro hYb; exact hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩
  obtain ⟨X₂, hX₂, hrk⟩ := hex
  set u := valuation k (ϖ : k) with hu
  have hQ' : ∀ j l, valuation k (Q j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)
  have hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m := fun i j => by
    rw [Matrix.sub_apply, ← vpow]; exact hX₂ i j
  have hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹ := fun l i => (hH l i).trans_eq vinv
  have hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m := fun l j => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro i _; rw [map_mul]
    exact mul_le_mul' (hHb l i) (hD i j)
  have hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m := fun l l' => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ (u ^ c)⁻¹ * u ^ m * 1 := mul_le_mul' (hHD l j) (hQ' j l')
      _ = _ := mul_one _
  have hm1 : u ^ m ≤ u ^ (c + 1) := pow_le_pow_right_of_le_one' hlt.le hcm
  have hδ : (u ^ c)⁻¹ * u ^ m < 1 := by
    calc (u ^ c)⁻¹ * u ^ m ≤ (u ^ c)⁻¹ * u ^ (c + 1) := mul_le_mul' le_rfl hm1
      _ = u := by rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ < 1 := hlt
  have hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hHCQ]; abel
  have hunit : IsUnit (H * X₂ * Q) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro a a' haa
    have h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0 := by
      rw [← hM, Matrix.sub_vecMul]; exact sub_eq_zero.2 haa
    funext l
    have h1 := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l
    have h2 : (a - a') l = 0 := (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    exact sub_eq_zero.1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀
  have hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← hs]
  have hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1) := fun j => by
    have h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1) := ((hX₂ i₀ j).trans_eq (vpow m)).trans hm1
    have h2 : valuation k (C i₀ j) ≤ u ^ (c + 1) := (hCi₀ j).trans_eq (vpow _)
    calc valuation k (X₂ i₀ j) = valuation k ((X₂ i₀ j - C i₀ j) + C i₀ j) := by rw [sub_add_cancel]
      _ ≤ _ := Valuation.map_add_le _ h1 h2
  have hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1) := fun l => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * 1 := mul_le_mul' (hX₂i₀ j) (hQ' j l)
      _ = _ := mul_one _
  have hsb := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw
  have hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m := fun j => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro l _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * ((u ^ c)⁻¹ * u ^ m) := mul_le_mul' (hsb l) (hHD l j)
      _ = u * u ^ m := by
        rw [pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _
      _ = u ^ m := one_mul _
  set C' := Matrix.updateRow C i₀ 0 with hC'
  have hHC' : H * C' = H * C := by
    ext l j
    simp only [Matrix.mul_apply, C', Matrix.updateRow_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · subst h; simp [hHi₀]
    · rfl
  have hcore := GlobalTheory.T.box_function_twisted_coinvariant k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm
    (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])
  have hstep := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C' H s hHi₀ hH
    (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))
  have e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C)) := by
    rw [Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]
  have hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) =
      Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C))) := by
    rw [hHC', e1]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]
  have hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m) := by
    rw [hC'']
    intro i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self]
      calc valuation k ((X₂ i - s ᵥ* (H * (X₂ - C))) j - C i j)
          = valuation k ((X₂ i j - C i j) - (s ᵥ* (H * (X₂ - C))) j) := by
            congr 1; rw [Pi.sub_apply]; ring
        _ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) :=
            Valuation.map_sub _ _ _
        _ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)
        _ = _ := (vpow m).symm
    · rw [Matrix.updateRow_ne hi]; simp
  rw [GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem] at hstep
  rw [← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRankStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_function_twisted_coinvariant_rank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row | exact GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row | (intros; apply GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row <;> assumption)
end
