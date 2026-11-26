module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfNormalizesSymmetricLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneWithResiduesAtSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryScalarMulIntegralLocalToGlobal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinRangeGLEqTopMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinRangeGLEqTopMatrix
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem adjoin_range_GL_eq_top (R : Type) [CommRing R] (n : ℕ) :
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  set S := Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ)
  have hoff : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1:R) ∈ S := by
    intro i j hij
    have hu : IsUnit (Matrix.transvection i j (1:R)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)
    have hmem : Matrix.transvection i j (1:R) ∈ S :=
      Algebra.subset_adjoin ⟨hu.unit, Set.mem_univ _, rfl⟩
    have : Matrix.single i j (1:R) = Matrix.transvection i j 1 - 1 := by
      simp [Matrix.transvection]
    rw [this]; exact S.sub_mem hmem S.one_mem
  have hall : ∀ i j : Fin n, Matrix.single i j (1:R) ∈ S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases h : ∃ k, k ≠ i
      · obtain ⟨k, hk⟩ := h
        have : Matrix.single i i (1:R) = Matrix.single i k 1 * Matrix.single k i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [this]; exact S.mul_mem (hoff _ _ (Ne.symm hk)) (hoff _ _ hk)
      · push_neg at h
        have : Matrix.single i i (1:R) = 1 := by
          ext a b
          rw [h a, h b]; simp
        rw [this]; exact S.one_mem
    · exact hoff i j hij
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Matrix.single i j 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]; exact S.smul_mem (hall i j) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdjoinRangeGLEqTopMatrixStatement
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_range_GL_eq_top_matrix : ∀ (R : Type) [CommRing R] (n : ℕ), Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  first | exact @GlobalTheory.adjoin_range_GL_eq_top | exact GlobalTheory.adjoin_range_GL_eq_top | (intros; apply GlobalTheory.adjoin_range_GL_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPattern
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPattern
noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.SymNorm

variable {k : Type} [Field k] {n : ℕ}

def Prec (ρ κ i j : ℕ) : Prop := i < j ∧ ¬(ρ ≤ i ∧ i < ρ + κ ∧ j = ρ + κ)

def ht (ρ κ i : ℕ) : ℕ := if i < ρ + κ then i else if i = ρ + κ then ρ else i - 1

def dp (n ρ κ i : ℕ) : ℕ := if i < ρ + κ then n - 2 - i else if i = ρ + κ then ρ else n - 1 - i

theorem ht_lt {ρ κ i j : ℕ} (hκ : 1 ≤ κ) (h : Prec ρ κ i j) : ht ρ κ i + 1 ≤ ht ρ κ j := by
  unfold Prec at h; unfold ht; split_ifs <;> omega

theorem dp_lt {n ρ κ i j : ℕ} (hn : n = 2 * ρ + κ + 1) (hκ : 1 ≤ κ) (hj : j < n) (h : Prec ρ κ i j) : dp n ρ κ j + 1 ≤ dp n ρ κ i := by
  unfold Prec at h; unfold dp; split_ifs <;> (try rw [Nat.sub_sub, Nat.sub_sub]) <;> omega

theorem exists_succ {ρ κ : ℕ} (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (a : Fin n) (ha : 1 ≤ dp n ρ κ a.val) :
    ∃ q : Fin n, Prec ρ κ a.val q.val ∧ dp n ρ κ a.val ≤ dp n ρ κ q.val + 1 := by
  by_cases h : a.val + 1 = ρ + κ
  · refine ⟨⟨ρ + κ + 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, dp, Fin.val_mk] at *; split_ifs at * <;> omega)
  · have : a.val + 1 < n := by unfold dp at ha; split_ifs at ha <;> omega
    refine ⟨⟨a.val + 1, this⟩, ?_, ?_⟩
    all_goals (simp only [Prec, dp, Fin.val_mk] at *; split_ifs at * <;> omega)

theorem exists_pred {ρ κ : ℕ} (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (a : Fin n) (ha : 1 ≤ ht ρ κ a.val) :
    ∃ c : Fin n, Prec ρ κ c.val a.val ∧ ht ρ κ a.val ≤ ht ρ κ c.val + 1 := by
  have := a.2
  by_cases h : a.val = ρ + κ
  · refine ⟨⟨ρ - 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, ht, Fin.val_mk] at *; split_ifs at * <;> omega)
  by_cases h' : a.val = ρ + κ + 1
  · refine ⟨⟨ρ + κ - 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, ht, Fin.val_mk] at *; split_ifs at * <;> omega)
  · have : 1 ≤ a.val := by unfold ht at ha; split_ifs at ha <;> omega
    refine ⟨⟨a.val - 1, by omega⟩, ?_, ?_⟩
    all_goals (simp only [Prec, ht, Fin.val_mk] at *; split_ifs at * <;> omega)

theorem allowed_of {ρ κ i a : ℕ} (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hi : i < n) (ha : a < n)
    (h1 : dp n ρ κ a ≤ dp n ρ κ i) (h2 : ht ρ κ i ≤ ht ρ κ a) :
    i = a ∨ Prec ρ κ i a ∨ (i = ρ ∧ a = ρ + κ) ∨ (i = ρ + κ ∧ a + 1 = ρ + κ) := by
  unfold Prec; unfold dp at h1; unfold ht at h2; split_ifs at h1 h2 <;> omega

section Pattern

variable {ρ κ : ℕ} {X Y : Matrix (Fin n) (Fin n) k}

theorem step_up (hYX : Y * X = 1)
    (hP : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → X i p * Y q j = 0)
    {i p q : Fin n} (hip : X i p ≠ 0) (hpq : Prec ρ κ p q) : ∃ j : Fin n, Prec ρ κ i j ∧ X j q ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 : (Y * X) q q = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : Prec ρ κ i j
    · rw [hc j hj, mul_zero]
    · rw [(mul_eq_zero.1 (hP p q hpq i j hj)).resolve_left hip, zero_mul]
  rw [hYX, one_apply_eq] at h0
  exact one_ne_zero h0

theorem step_down (hXY : X * Y = 1)
    (hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → Y i p * X q j = 0)
    {i a c : Fin n} (hia : X i a ≠ 0) (hci : Prec ρ κ c i) : ∃ j : Fin n, Prec ρ κ j a ∧ X c j ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h0 : (X * Y) c c = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : Prec ρ κ j a
    · rw [hc j hj, zero_mul]
    · rw [(mul_eq_zero.1 (hP' c i hci j a hj)).resolve_right hia, mul_zero]
  rw [hXY, one_apply_eq] at h0
  exact one_ne_zero h0

theorem dp_le (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hYX : Y * X = 1)
    (hP : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → X i p * Y q j = 0) :
    ∀ d : ℕ, ∀ i a : Fin n, X i a ≠ 0 → d ≤ dp n ρ κ a → d ≤ dp n ρ κ i := by
  intro d
  induction d with
  | zero => intros; exact Nat.zero_le _
  | succ d ih =>
    intro i a hia hd
    obtain ⟨q, haq, hq⟩ := exists_succ hn hρ a (by omega)
    obtain ⟨j, hij, hjq⟩ := step_up hYX hP hia haq
    have h1 := ih j q hjq (by omega)
    have h2 := dp_lt hn (by omega) j.2 hij
    omega

theorem ht_le (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hXY : X * Y = 1)
    (hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → Y i p * X q j = 0) :
    ∀ d : ℕ, ∀ i a : Fin n, X i a ≠ 0 → d ≤ ht ρ κ i → d ≤ ht ρ κ a := by
  intro d
  induction d with
  | zero => intros; exact Nat.zero_le _
  | succ d ih =>
    intro i a hia hd
    obtain ⟨c, hci, hc⟩ := exists_pred hn hρ hκ i (by omega)
    obtain ⟨j, hja, hcj⟩ := step_down hXY hP' hia hci
    have h1 := ih c j hcj (by omega)
    have h2 := ht_lt (by omega) hja
    omega

theorem pattern (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ) (hXY : X * Y = 1) (hYX : Y * X = 1)
    (hP : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → X i p * Y q j = 0)
    (hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j → Y i p * X q j = 0)
    (i a : Fin n) (h : X i a ≠ 0) :
    i.val = a.val ∨ Prec ρ κ i a ∨ (i.val = ρ ∧ a.val = ρ + κ) ∨ (i.val = ρ + κ ∧ a.val + 1 = ρ + κ) :=
  allowed_of hn hρ hκ i.2 a.2 (dp_le hn hρ hκ hYX hP _ i a h le_rfl) (ht_le hn hρ hκ hXY hP' _ i a h le_rfl)

end Pattern

section Conj

theorem mul_single_mul' (X Y : Matrix (Fin n) (Fin n) k) (p q i j : Fin n) (s : k) :
    (X * single p q s * Y) i j = X i p * s * Y q j := by
  have h1 : X * single p q s = Matrix.of fun i x => if x = q then X i p * s else 0 := by
    ext i x
    rw [Matrix.mul_apply, Matrix.of_apply]
    by_cases hx : x = q
    · subst hx
      rw [if_pos rfl, Finset.sum_eq_single p]
      · simp [Matrix.single_apply]
      · intro y _ hy; simp [Matrix.single_apply, Ne.symm hy]
      · simp
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun y _ => by simp [Matrix.single_apply, Ne.symm hx]
  rw [h1, Matrix.mul_apply, Finset.sum_eq_single q]
  · simp [mul_assoc]
  · intro y _ hy; simp [hy]
  · simp

def elemU (p q : Fin n) (hpq : p ≠ q) (s : k) : GL (Fin n) k :=
  have hEE : single p q s * single p q s = 0 := by simp [hpq.symm]
  ⟨1 + single p q s, 1 - single p q s,
    by rw [add_mul, one_mul, mul_sub, hEE, sub_zero, mul_one, sub_add_cancel],
    by rw [sub_mul, one_mul, mul_add, hEE, add_zero, mul_one, add_sub_cancel_right]⟩

theorem elemU_apply (p q : Fin n) (hpq : p ≠ q) (s : k) (i j : Fin n) :
    ((elemU p q hpq s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (1 : Matrix (Fin n) (Fin n) k) i j + single p q s i j := rfl

theorem elemU_mem {ρ κ : ℕ} {p q : Fin n} (h : Prec ρ κ p q) (hpq : p ≠ q) (s : k) :
    elemU p q hpq s ∈ unipSym k n ρ κ := by
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
  · have hij' : j.val < i.val := hij
    rw [elemU_apply, one_apply_ne (fun e => by rw [e] at hij'; omega), single_apply, if_neg, zero_add]
    rintro ⟨rfl, rfl⟩; unfold Prec at h; omega
  · rw [elemU_apply, one_apply_eq, single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩; exact hpq rfl
  · rw [elemU_apply, one_apply_ne (fun e => by rw [e] at h1; omega), single_apply, if_neg, zero_add]
    rintro ⟨rfl, rfl⟩; unfold Prec at h; omega

theorem conj_elemU_apply (M : GL (Fin n) k) (p q : Fin n) (hpq : p ≠ q) (s : k) (i j : Fin n) :
    ((M * elemU p q hpq s * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (1 : Matrix (Fin n) (Fin n) k) i j +
        (M : Matrix (Fin n) (Fin n) k) i p * s * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) q j := by
  have : ((M * elemU p q hpq s * M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + (M : Matrix (Fin n) (Fin n) k) * single p q s * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [Units.val_mul, Units.val_mul]
    show (M : Matrix (Fin n) (Fin n) k) * (1 + single p q s) * _ = _
    rw [mul_add, mul_one, add_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [this, Matrix.add_apply, mul_single_mul']

theorem unipSym_entry {ρ κ : ℕ} {g : GL (Fin n) k} (hg : g ∈ unipSym k n ρ κ) {i j : Fin n} (h : ¬ Prec ρ κ i j) :
    (g : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  rcases lt_trichotomy i.val j.val with h1 | h1 | h1
  · have h3 : ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ := by
      by_contra hc; exact h ⟨h1, hc⟩
    rw [hg.2 i j h3.1 h3.2.1 h3.2.2, one_apply_ne (fun e => by rw [e] at h1; omega)]
  · have := Fin.ext h1; subst this; rw [hg.1.2 i, one_apply_eq]
  · rw [hg.1.1 (show j.val < i.val from h1), one_apply_ne (fun e => by rw [e] at h1; omega)]

theorem apply_mul_inv_apply_eq_zero_of_normalizes {ρ κ : ℕ} (M : GL (Fin n) k) (hM : ∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ) :
    ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j →
      (M : Matrix (Fin n) (Fin n) k) i p * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) q j = 0 := by
  intro p q hpq i j hij
  have hne : p ≠ q := fun e => by rw [e] at hpq; exact lt_irrefl _ hpq.1
  have h := unipSym_entry (hM _ (elemU_mem hpq hne 1)) hij
  rw [conj_elemU_apply, mul_one] at h
  simpa using h

def esum (ρ κ : ℕ) (a : Fin n → Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) (p q : Fin n) : k :=
  ∑ i, ∑ j, if symEdge ρ κ i j then a i j * (X i p * Y q j) else 0

theorem edgeVal_conj {ρ κ : ℕ} (a : Fin n → Fin n → k) (M : GL (Fin n) k) (p q : Fin n) (hpq : p ≠ q) (s : k) :
    edgeVal ρ κ a (M * elemU p q hpq s * M⁻¹) =
      s * esum ρ κ a (M : Matrix (Fin n) (Fin n) k) ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q := by
  unfold edgeVal esum
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with he
  · have hij : i ≠ j := fun e => by unfold symEdge at he; rw [e] at he; omega
    rw [conj_elemU_apply, one_apply_ne hij, zero_add]; ring
  · rw [mul_zero]

theorem esum_single {ρ κ : ℕ} (a : Fin n → Fin n → k) (X Y : Matrix (Fin n) (Fin n) k) (p q i0 j0 : Fin n)
    (hz : ∀ i j : Fin n, symEdge ρ κ i j → X i p * Y q j ≠ 0 → i = i0 ∧ j = j0) :
    esum ρ κ a X Y p q = if symEdge ρ κ i0 j0 then a i0 j0 * (X i0 p * Y q j0) else 0 := by
  unfold esum
  rw [Finset.sum_eq_single i0, Finset.sum_eq_single j0]
  · intro j _ hj
    split_ifs with he
    · rcases eq_or_ne (X i0 p * Y q j) 0 with h | h
      · rw [h, mul_zero]
      · exact absurd (hz _ _ he h).2 hj
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with he
    · rcases eq_or_ne (X i p * Y q j) 0 with h | h
      · rw [h, mul_zero]
      · exact absurd (hz _ _ he h).1 hi
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem char_cancel (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {A B : k} (h : ∀ s : k, ψ (s * A) = ψ (s * B)) : A = B := by
  by_contra hne
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 hψ
  have hAB : A - B ≠ 0 := sub_ne_zero.2 hne
  have e : x / (A - B) * A = x / (A - B) * B + x := by field_simp; ring
  have h1 := h (x / (A - B))
  rw [e, AddChar.map_add_eq_mul] at h1
  have h0 : ψ (x / (A - B) * B) ≠ 0 := fun h0 => by
    have := AddChar.map_add_eq_mul ψ (x / (A - B) * B) (-(x / (A - B) * B))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  exact hx (mul_left_cancel₀ h0 (by rw [mul_one]; exact h1))

theorem hC_of {ρ κ : ℕ} (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : Fin n → Fin n → k) (M : GL (Fin n) k)
    (hM : ∀ h ∈ unipSym k n ρ κ, ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h))
    (p q : Fin n) (hpq : Prec ρ κ p q) :
    esum ρ κ a (M : Matrix (Fin n) (Fin n) k) ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      if symEdge ρ κ p q then a p q else 0 := by
  have hne : p ≠ q := fun e => by rw [e] at hpq; exact lt_irrefl _ hpq.1
  have e1 : ∀ s, edgeVal ρ κ a (elemU p q hne s) = s * esum ρ κ a 1 1 p q := fun s => by
    have := edgeVal_conj (ρ := ρ) (κ := κ) a (1 : GL (Fin n) k) p q hne s
    rwa [one_mul, inv_one, mul_one, Units.val_one] at this
  have key : esum ρ κ a (M : Matrix (Fin n) (Fin n) k) ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) p q =
      esum ρ κ a 1 1 p q := char_cancel ψ hψ fun s => by
    rw [← edgeVal_conj (ρ := ρ) (κ := κ) a M p q hne s, ← e1]; exact hM _ (elemU_mem hpq hne s)
  rw [key, esum_single a 1 1 p q p q]
  · simp
  · intro i j _ h
    constructor
    · by_contra hc; apply h; rw [one_apply_ne hc, zero_mul]
    · by_contra hc; apply h; rw [one_apply_ne (Ne.symm hc), mul_zero]

end Conj

theorem normaliser_unipSym_char : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → 2 ≤ κ →
    ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) →
    ∀ M : GL (Fin n) k, (∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ ∧
      ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h)) →
    (∀ h ∈ unipSym k n ρ κ, M⁻¹ * h * M ∈ unipSym k n ρ κ) →
    ∃ s c : kˣ, ∃ h ∈ unipSym k n ρ κ,
      (M : Matrix (Fin n) (Fin n) k) = midDiag n ρ κ (s : k) (c : k) * (h : Matrix (Fin n) (Fin n) k) := by
  intro k _ n ρ κ hn hρ hκ ψ hψ a ha M hM hM'
  have hXY : (M : Matrix (Fin n) (Fin n) k) * ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYX : ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (M : Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hP := apply_mul_inv_apply_eq_zero_of_normalizes M (fun h hh => (hM h hh).1)
  have hP' : ∀ p q : Fin n, Prec ρ κ p q → ∀ i j : Fin n, ¬ Prec ρ κ i j →
      ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i p * (M : Matrix (Fin n) (Fin n) k) q j = 0 := by
    have := apply_mul_inv_apply_eq_zero_of_normalizes M⁻¹ (fun h hh => by rw [inv_inv]; exact hM' h hh)
    simpa only [inv_inv] using this
  have hC := hC_of ψ hψ a M (fun h hh => (hM h hh).2)
  obtain ⟨X, hX⟩ : ∃ X, X = (M : Matrix (Fin n) (Fin n) k) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ((M⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := ⟨_, rfl⟩
  rw [← hX, ← hY] at hXY hYX hP hP' hC
  rw [← hX]
  have patX := pattern hn hρ hκ hXY hYX hP hP'
  have patY := pattern hn hρ hκ hYX hXY hP' hP
  have diag : ∀ b : Fin n, X b b * Y b b = 1 := by
    intro b
    have h := congrFun (congrFun hXY b) b
    rw [Matrix.mul_apply, Finset.sum_eq_single b, one_apply_eq] at h
    · exact h
    · intro j _ hj
      rcases eq_or_ne (X b j) 0 with h1 | h1
      · rw [h1, zero_mul]
      rcases eq_or_ne (Y j b) 0 with h2 | h2
      · rw [h2, mul_zero]
      exfalso
      have e1 := patX b j h1
      have e2 := patY j b h2
      have : j.val ≠ b.val := fun e => hj (Fin.ext e)
      unfold Prec at e1 e2; omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have hX0 : ∀ b, X b b ≠ 0 := fun b => left_ne_zero_of_mul_eq_one (diag b)
  have hY0 : ∀ b, Y b b ≠ 0 := fun b => right_ne_zero_of_mul_eq_one (diag b)
  obtain ⟨tF, htF⟩ : ∃ x : Fin n, x.val = ρ + κ := ⟨⟨ρ + κ, by omega⟩, rfl⟩
  obtain ⟨tmF, htmF⟩ : ∃ x : Fin n, x.val = ρ + κ - 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨tpF, htpF⟩ : ∃ x : Fin n, x.val = ρ + κ + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨rF, hrF⟩ : ∃ x : Fin n, x.val = ρ := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨rmF, hrmF⟩ : ∃ x : Fin n, x.val = ρ - 1 := ⟨⟨_, by omega⟩, rfl⟩

  have S1 : X tF tmF = 0 := by
    have h := hC tmF tpF (by unfold Prec; omega)
    rw [esum_single a X Y tmF tpF tF tpF (fun i j he hne => by
      have e1 := patX i tmF (left_ne_zero_of_mul hne)
      have e2 := patY tpF j (right_ne_zero_of_mul hne)
      unfold symEdge at he; unfold Prec at e1 e2
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩),
      if_pos (by unfold symEdge; omega), if_neg (by unfold symEdge; omega)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (ha _ _ (by unfold symEdge; omega))
    · exact (mul_eq_zero.1 h).resolve_right (hY0 tpF)

  have S2 : Y rF tF = 0 := by
    have h := hC rmF rF (by unfold Prec; omega)
    rw [esum_single a X Y rmF rF rmF tF (fun i j he hne => by
      have e1 := patX i rmF (left_ne_zero_of_mul hne)
      have e2 := patY rF j (right_ne_zero_of_mul hne)
      unfold symEdge at he; unfold Prec at e1 e2
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩),
      if_pos (by unfold symEdge; omega), if_neg (by unfold symEdge; omega)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (ha _ _ (by unfold symEdge; omega))
    · exact (mul_eq_zero.1 h).resolve_left (hX0 rmF)
  have S3 : Y tF tmF = 0 := by
    have h := congrFun (congrFun hYX tF) tmF
    rw [Matrix.mul_apply, Finset.sum_eq_single tmF, one_apply_ne (fun e => by rw [e] at htF; omega)] at h
    · exact (mul_eq_zero.1 h).resolve_right (hX0 tmF)
    · intro j _ hj
      rcases eq_or_ne (Y tF j) 0 with h1 | h1
      · rw [h1, zero_mul]
      rcases eq_or_ne (X j tmF) 0 with h2 | h2
      · rw [h2, mul_zero]
      exfalso
      by_cases hjt : j = tF
      · rw [hjt] at h2; exact h2 S1
      have e1 := patY tF j h1
      have e2 := patX j tmF h2
      have : j.val ≠ tmF.val := fun e => hj (Fin.ext e)
      have : j.val ≠ tF.val := fun e => hjt (Fin.ext e)
      unfold Prec at e1 e2; omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have S4 : X rF tF = 0 := by
    have h := congrFun (congrFun hXY rF) tF
    rw [Matrix.mul_apply, Finset.sum_eq_single tF, one_apply_ne (fun e => by rw [e] at hrF; omega)] at h
    · exact (mul_eq_zero.1 h).resolve_right (hY0 tF)
    · intro j _ hj
      rcases eq_or_ne (X rF j) 0 with h1 | h1
      · rw [h1, zero_mul]
      rcases eq_or_ne (Y j tF) 0 with h2 | h2
      · rw [h2, mul_zero]
      exfalso
      by_cases hjr : j = rF
      · rw [hjr] at h2; exact h2 S2
      have e1 := patX rF j h1
      have e2 := patY j tF h2
      have : j.val ≠ tF.val := fun e => hj (Fin.ext e)
      have : j.val ≠ rF.val := fun e => hjr (Fin.ext e)
      unfold Prec at e1 e2; omega
    · intro h; exact absurd (Finset.mem_univ _) h
  have patX' : ∀ i b : Fin n, X i b ≠ 0 → i.val = b.val ∨ Prec ρ κ i b := by
    intro i b h
    rcases patX i b h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; apply h
      rw [show i = rF from Fin.ext (by omega), show b = tF from Fin.ext (by omega)]; exact S4
    · exfalso; apply h
      rw [show i = tF from Fin.ext (by omega), show b = tmF from Fin.ext (by omega)]; exact S1
  have patY' : ∀ i b : Fin n, Y i b ≠ 0 → i.val = b.val ∨ Prec ρ κ i b := by
    intro i b h
    rcases patY i b h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; apply h
      rw [show i = rF from Fin.ext (by omega), show b = tF from Fin.ext (by omega)]; exact S2
    · exfalso; apply h
      rw [show i = tF from Fin.ext (by omega), show b = tmF from Fin.ext (by omega)]; exact S3

  have S5 : ∀ p q : Fin n, symEdge ρ κ p q → X p p = X q q := by
    intro p q he
    have hpq : Prec ρ κ p q := by unfold symEdge at he; unfold Prec; omega
    have h := hC p q hpq
    rw [esum_single a X Y p q p q (fun i j he' hne => by
      have e1 := patX' i p (left_ne_zero_of_mul hne)
      have e2 := patY' q j (right_ne_zero_of_mul hne)
      unfold symEdge at he he'; unfold Prec at e1 e2 hpq
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩), if_pos he, if_pos he] at h
    have h1 : X p p * Y q q = 1 := mul_left_cancel₀ (ha p q he) (by rw [mul_one]; exact h)
    exact mul_right_cancel₀ (hY0 q) (by rw [h1, diag q])
  let D : ℕ → k := fun m => if h : m < n then X ⟨m, h⟩ ⟨m, h⟩ else 0
  have hDX : ∀ i : Fin n, X i i = D i.val := fun i => by simp [D, i.2]
  have hD : ∀ m m' (hm : m < n) (hm' : m' < n),
      ((m' = m + 1 ∧ m + 1 ≠ ρ ∧ m + 1 ≠ ρ + κ) ∨ (m + 1 = ρ ∧ m' = ρ + κ)) → D m = D m' := by
    intro m m' hm hm' he
    have := S5 ⟨m, hm⟩ ⟨m', hm'⟩ he
    simpa [D, hm, hm'] using this
  have c1 : ∀ m, m < ρ → D m = D 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih (by omega)]
      exact (hD m (m + 1) (by omega) (by omega) (Or.inl ⟨rfl, by omega, by omega⟩)).symm
  have c2 : D (ρ + κ) = D 0 := by
    rw [← c1 (ρ - 1) (by omega)]
    exact (hD (ρ - 1) (ρ + κ) (by omega) (by omega) (Or.inr ⟨by omega, rfl⟩)).symm
  have c3 : ∀ m, ρ + κ + m < n → D (ρ + κ + m) = D 0 := by
    intro m hm
    induction m with
    | zero => exact c2
    | succ m ih =>
      rw [← ih (by omega)]
      exact (hD (ρ + κ + m) (ρ + κ + (m + 1)) (by omega) (by omega) (Or.inl ⟨by omega, by omega, by omega⟩)).symm
  have c4 : ∀ m, m < κ → D (ρ + m) = D ρ := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih (by omega)]
      exact (hD (ρ + m) (ρ + (m + 1)) (by omega) (by omega) (Or.inl ⟨by omega, by omega, by omega⟩)).symm
  have diagX : ∀ i : Fin n, X i i = if ρ ≤ i.val ∧ i.val < ρ + κ then D ρ else D 0 := by
    intro i
    rw [hDX]
    split_ifs with hi
    · have := c4 (i.val - ρ) (by omega); rwa [show ρ + (i.val - ρ) = i.val by omega] at this
    · by_cases h1 : i.val < ρ
      · exact c1 _ h1
      · have := c3 (i.val - (ρ + κ)) (by omega)
        rwa [show ρ + κ + (i.val - (ρ + κ)) = i.val by omega] at this
  have hs0 : D 0 ≠ 0 := by have := hX0 ⟨0, by omega⟩; rwa [hDX] at this
  have hc0 : D ρ ≠ 0 := by have := hX0 ⟨ρ, by omega⟩; rwa [hDX] at this
  have hDD : midDiag n ρ κ (D 0) (D ρ) * midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ = 1 := by
    unfold midDiag; rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> field_simp
  have hD'D : midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * midDiag n ρ κ (D 0) (D ρ) = 1 := by
    unfold midDiag; rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> field_simp
  have hmd : ∀ (s c : k) (Z : Matrix (Fin n) (Fin n) k) (i j : Fin n),
      (midDiag n ρ κ s c * Z) i j = (if ρ ≤ i.val ∧ i.val < ρ + κ then c else s) * Z i j := by
    intro s c Z i j; unfold midDiag; rw [diagonal_mul]
  let U : GL (Fin n) k := ⟨midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X, Y * midDiag n ρ κ (D 0) (D ρ),
    by rw [mul_assoc, ← mul_assoc X, hXY, one_mul, hD'D],
    by rw [mul_assoc, ← mul_assoc (midDiag n ρ κ (D 0) (D ρ)), hDD, one_mul, hYX]⟩
  refine ⟨Units.mk0 (D 0) hs0, Units.mk0 (D ρ) hc0, U, ?_, ?_⟩
  · refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      show (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X) i j = 0
      rw [hmd]
      rcases eq_or_ne (X i j) 0 with h | h
      · rw [h, mul_zero]
      · exfalso; have := patX' i j h; unfold Prec at this; omega
    · show (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X) i i = 1
      rw [hmd, diagX]
      split_ifs with hi
      · exact inv_mul_cancel₀ hc0
      · exact inv_mul_cancel₀ hs0
    · show (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X) i j = 0
      rw [hmd]
      rcases eq_or_ne (X i j) 0 with h | h
      · rw [h, mul_zero]
      · exfalso; have := patX' i j h; unfold Prec at this; omega
  · show X = midDiag n ρ κ (D 0) (D ρ) * (midDiag n ρ κ (D 0)⁻¹ (D ρ)⁻¹ * X)
    rw [← mul_assoc, hDD, one_mul]

end GlobalTheory.SymNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserUnipSymCharPatternStatement
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normaliser_unipSym_char_pattern : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → 2 ≤ κ → ∀ ψ : AddChar k ℂ, ψ ≠ 1 → ∀ a : Fin n → Fin n → k, (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ M : GL (Fin n) k, (∀ h ∈ unipSym k n ρ κ, M * h * M⁻¹ ∈ unipSym k n ρ κ ∧ ψ (edgeVal ρ κ a (M * h * M⁻¹)) = ψ (edgeVal ρ κ a h)) → (∀ h ∈ unipSym k n ρ κ, M⁻¹ * h * M ∈ unipSym k n ρ κ) → ∃ s c : kˣ, ∃ h ∈ unipSym k n ρ κ, (M : Matrix (Fin n) (Fin n) k) = midDiag n ρ κ (s : k) (c : k) * (h : Matrix (Fin n) (Fin n) k) := by
  first | exact @GlobalTheory.SymNorm.normaliser_unipSym_char | exact GlobalTheory.SymNorm.normaliser_unipSym_char | (intros; apply GlobalTheory.SymNorm.normaliser_unipSym_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfConjIntegralGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfConjIntegralGenerators
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section
namespace GlobalTheory.ScalConj

theorem single_conj_apply {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (a b i j : Fin n) :
    (A * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * B) i j = A i a * B b j := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

def conjInt {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) :
    Subalgebra O (Matrix (Fin n) (Fin n) O) where
  carrier := {X | ∃ Y : Matrix (Fin n) (Fin n) O,
    Y.map O.subtype = (m : Matrix (Fin n) (Fin n) K) * X.map O.subtype * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  mul_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y * Y', ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, hY, hY']
    have : ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (m : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul m
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), this, Matrix.one_mul]
  add_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y + Y', ?_⟩
    rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hY, hY', Matrix.mul_add, Matrix.add_mul]
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap O _ r, ?_⟩
    have h : (algebraMap O (Matrix (Fin n) (Fin n) O) r).map O.subtype = (r : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, h, Matrix.one_apply_ne h]
    rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

theorem single_map_subtype {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : O)).map O.subtype = (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem entry_mul_inv_entry_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) (i a b j : Fin n) :
    (m : Matrix (Fin n) (Fin n) K) i a * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b j ∈ O := by
  have hle : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) ≤ conjInt O m := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx'⟩ := hc x hx
    exact ⟨x', congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx'⟩
  rw [hT] at hle
  obtain ⟨Y, hY⟩ := hle (Algebra.mem_top : Matrix.single a b (1 : O) ∈ (⊤ : Subalgebra O (Matrix (Fin n) (Fin n) O)))
  have h := congrFun (congrFun hY i) j
  rw [single_map_subtype, single_conj_apply] at h
  rw [← h]
  exact (Y i j).2

theorem isScal_of_conj (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) : IsScal O m := by
  have H := entry_mul_inv_entry_mem O m T hT hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  set M : Matrix (Fin n) (Fin n) K := (m : Matrix (Fin n) (Fin n) K) with hM
  set N : Matrix (Fin n) (Fin n) K := ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hMN : M * N = 1 := Units.mul_inv m
  obtain ⟨⟨i0, a0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => O.valuation (M p.1 p.2)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set c := M i0 a0 with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : ∀ i a, M i a = 0 := fun i a => by
      have h1 := hmax (i, a) (Finset.mem_univ _)
      simp only [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    have h1 := congrFun (congrFun hMN ⟨0, hn⟩) ⟨0, hn⟩
    simp [Matrix.mul_apply, hz] at h1
  have hv : 0 < O.valuation c := (Valuation.pos_iff _).2 hc0
  have hy : ∀ i a, c⁻¹ * M i a ∈ O := fun i a => by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hv).2 (hmax (i, a) (Finset.mem_univ _))
  have hz : ∀ b j, c * N b j ∈ O := fun b j => H i0 a0 b j
  let Y : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hy i j⟩
  let Z : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hz i j⟩
  have hYm : Y.map O.subtype = c⁻¹ • M := by ext i j; rfl
  have hZm : Z.map O.subtype = c • N := by ext i j; rfl
  have inj : Function.Injective fun X : Matrix (Fin n) (Fin n) O => X.map O.subtype :=
    Matrix.map_injective (Subtype.val_injective)
  have key : ∀ {A B : Matrix (Fin n) (Fin n) K}, A * B = 1 → (c⁻¹ • A) * (c • B) = 1 := fun {A B} h => by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, h]
  have hNM : N * M = 1 := Units.inv_mul m
  have e1 : Y * Z = 1 := inj (by
    show (Y * Z).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, key hMN])
  have e2 : Z * Y = 1 := inj (by
    show (Z * Y).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc0, one_smul, hNM])
  refine ⟨Units.mk0 c hc0, ⟨Y, Z, e1, e2⟩, ?_⟩
  show M = c • (Y.map O.subtype)
  rw [hYm, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end GlobalTheory.ScalConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfConjIntegralGeneratorsStatement
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators : ∀ (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K) (T : Set (GL (Fin n) O)), Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤ → (∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) → IsScal O m := by
  first | exact @GlobalTheory.ScalConj.isScal_of_conj | exact GlobalTheory.ScalConj.isScal_of_conj | (intros; apply GlobalTheory.ScalConj.isScal_of_conj <;> assumption)
end
end

noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV

namespace GlobalTheory.LevNorm

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {n : ℕ} (f : R →+* R') (g : R' →+* R'')
    (x : GL (Fin n) R) : bc g (bc f x) = bc (g.comp f) x := Units.ext rfl

theorem bc_injective {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ} {f : R →+* R'} (hf : Function.Injective f) :
    Function.Injective (bc (n := Fin n) f) := fun _ _ h =>
  Units.ext (Matrix.map_injective hf (congrArg Units.val h))

theorem bc_surjective {R k : Type} [CommRing R] [IsLocalRing R] [Field k] {n : ℕ} {f : R →+* k} (hf : Function.Surjective f) :
    Function.Surjective (bc (n := Fin n) f) := fun y => by
  choose j hj using hf
  have e : f.mapMatrix ((y : Matrix (Fin n) (Fin n) k).map j) = y := by ext a b; exact hj _
  haveI : IsLocalHom f := IsLocalHom.of_surjective f fun a => ⟨j a, hj a⟩
  have hu : IsUnit ((y : Matrix (Fin n) (Fin n) k).map j) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← isUnit_map_iff f, RingHom.map_det, e, ← Matrix.isUnit_iff_isUnit_det]
    exact y.isUnit
  exact ⟨hu.unit, Units.ext e⟩

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] (r : ∀ Q, S →+* k Q)
  (σ : A →+* A) {n : ℕ} (ρ κ : ℕ) (G : GL (Fin n) S) (T : Finset P) (ψ : ∀ Q, AddChar (k Q) ℂ) (a : ∀ Q, Fin n → Fin n → k Q)

def InLev (x : GL (Fin n) S) : Prop :=
  bc S.subtype x ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧ ∀ Q ∈ T, bc (r Q) x ∈ unipSym (k Q) n ρ κ

def levChr (x : GL (Fin n) S) : ℂ := ∏ Q ∈ T, ψ Q (edgeVal ρ κ (a Q) (bc (r Q) x))

def Keeps (m : GL (Fin n) A) : Prop :=
  ∀ x, InLev r σ ρ κ G T x → ∃ x', bc S.subtype x' = m * bc S.subtype x * m⁻¹ ∧ InLev r σ ρ κ G T x' ∧
    levChr r ρ κ T ψ a x' = levChr r ρ κ T ψ a x

variable {r σ ρ κ G T ψ a} (Z : PlaceSys A S P k r)

theorem bc_pO (Q : P) (x : GL (Fin n) S) : bc (Z.O Q).subtype (bc (Z.pO Q) x) = bc (Z.p Q) (bc S.subtype x) := Units.ext rfl

theorem bc_res {Q : P} {f : Z.O Q →+* k Q} (hf : ∀ s, f (Z.pO Q s) = r Q s) (x : GL (Fin n) S) :
    bc f (bc (Z.pO Q) x) = bc (r Q) x := by
  rw [bc_bc, show f.comp (Z.pO Q) = r Q from RingHom.ext hf]

theorem bc_r_one {Q : P} {x : GL (Fin n) S} (h : bc (Z.pO Q) x = 1) : bc (r Q) x = 1 := by
  obtain ⟨f, -, hf⟩ := Z.exists_res Q
  rw [← bc_res Z hf, h, map_one]

theorem pO_conj_one {Q : P} {m : GL (Fin n) A} {x x' : GL (Fin n) S} (e : bc S.subtype x' = m * bc S.subtype x * m⁻¹)
    (h : bc (Z.pO Q) x = 1) : bc (Z.pO Q) x' = 1 := by
  apply bc_injective (Z.O Q).subtype_injective
  rw [bc_pO, e, map_mul, map_mul, ← bc_pO, h, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem loc_split (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (hQ' : Q' ∉ T) {f : Z.O Q →+* k Q} (hf : ∀ s, f (Z.pO Q s) = r Q s)
    {m : GL (Fin n) A} (hm : Keeps r σ ρ κ G T ψ a m) (y : GL (Fin n) (Z.O Q)) (hy : Q ∈ T → bc f y ∈ unipSym (k Q) n ρ κ) :
    ∃ y' : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y' = bc (Z.p Q) m * bc (Z.O Q).subtype y * (bc (Z.p Q) m)⁻¹ ∧
      (Q ∈ T → bc f y' ∈ unipSym (k Q) n ρ κ ∧ ψ Q (edgeVal ρ κ (a Q) (bc f y')) = ψ Q (edgeVal ρ κ (a Q) (bc f y))) := by
  obtain ⟨u, hu, rfl, h1⟩ := GlobalTheory.T.exists_unitary_integral_of_splitPlace_component Z σ hσ hS n G hG Q Q' h hne y
  have h2 : ∀ Q'' ∈ T, Q'' ≠ Q → bc (Z.pO Q'') u = 1 := fun Q'' hT e => h1 Q'' e fun e' => hQ' (e' ▸ hT)
  obtain ⟨x', e, hx', hc⟩ := hm u ⟨hu, fun Q'' hT => by
    by_cases e : Q'' = Q
    · subst e; rw [← bc_res Z hf]; exact hy hT
    · rw [bc_r_one Z (h2 _ hT e)]; exact one_mem _⟩
  refine ⟨bc (Z.pO Q) x', by rw [bc_pO, bc_pO, e, map_mul, map_mul, map_inv], fun hT => ?_⟩
  rw [bc_res Z hf, bc_res Z hf]
  refine ⟨hx'.2 Q hT, ?_⟩
  unfold levChr at hc
  rwa [Finset.prod_eq_single_of_mem Q hT, Finset.prod_eq_single_of_mem Q hT] at hc
  · intro Q'' hT' e'
    rw [bc_r_one Z (h2 _ hT' e'), edgeVal_one, AddChar.map_zero_eq_one]
  · intro Q'' hT' e'
    rw [bc_r_one Z (pO_conj_one Z e (h2 _ hT' e')), edgeVal_one, AddChar.map_zero_eq_one]

theorem map_cT {Q Q' : P} {s : Z.K Q →+* Z.K Q'} (hs : ∀ a, s (Z.p Q a) = Z.p Q' (σ a)) (M : Matrix (Fin n) (Fin n) A) :
    (Z.p Q').mapMatrix (cT σ M) = (((Z.p Q).mapMatrix M).map s)ᵀ := by
  ext i j
  exact (hs _).symm

theorem loc_inert (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (hn : 3 ≤ n)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    {Q : P} (h : σ (Z.e Q) = Z.e Q) (hQ : Q ∉ T) (δ : S) (hδ : r Q (δ - ⟨σ δ, hS _ δ.2⟩) ≠ 0)
    {m : GL (Fin n) A} (hm : Keeps r σ ρ κ G T ψ a m) : IsScal (Z.O Q) (bc (Z.p Q) m) := by
  obtain ⟨s, hs, hsO⟩ := Z.exists_conj hS h
  obtain ⟨f, hf0, hf⟩ := Z.exists_res Q
  let t : Z.O Q →+* Z.O Q := (s.comp (Z.O Q).subtype).codRestrict (Z.O Q) fun x => hsO _ x.2
  have ht : ∀ x : S, t (Z.pO Q x) = Z.pO Q ⟨σ x, hS _ x.2⟩ := fun x => Subtype.ext (hs _)
  have htt : ∀ x, t (t x) = x := fun x => by
    obtain ⟨x, rfl⟩ := Z.pO_surj Q x
    rw [ht, ht]
    exact congrArg _ (Subtype.ext (hσ _))
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf0
  have hδ' : IsUnit (Z.pO Q δ - t (Z.pO Q δ)) := by
    rw [ht, ← map_sub, ← isUnit_map_iff f, hf]
    exact hδ.isUnit
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) (Z.O Q) => M.map (Z.O Q).subtype :=
    Matrix.map_injective (Z.O Q).subtype_injective
  have hgen := GlobalTheory.T.adjoin_unitaryGroup_hermitian_local_eq_top (Z.O Q) t htt ⟨_, hδ'⟩ n hn ((bc (Z.pO Q) G : GL (Fin n) (Z.O Q)) : Matrix (Fin n) (Fin n) (Z.O Q))
    (inj ((map_cT Z hs _).symm.trans (congrArg (Z.p Q).mapMatrix hG))) (Units.isUnit _)
  refine GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators _ _ n _ _ hgen fun y hy => ?_
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨u, rfl⟩ := Z.gl_int (x := x) fun Q' => by
    by_cases e : Q' = Q
    · subst e; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [hx2 _ e, map_one]⟩
  have hu1 : bc (Z.pO Q) u = y := bc_injective (Z.O Q).subtype_injective hx1
  have hu2 : ∀ Q', Q' ≠ Q → bc (Z.pO Q') u = 1 := fun Q' e =>
    bc_injective (Z.O Q').subtype_injective (by rw [bc_pO, hx2 _ e, map_one])
  have hU : bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
    refine Matrix.ext fun i j => Z.ext' fun Q' => ?_
    refine congrFun (congrFun (show (Z.p Q').mapMatrix _ = (Z.p Q').mapMatrix _ from ?_) i) j
    rw [map_mul, map_mul]
    by_cases e : Q' = Q
    · subst e
      rw [map_cT Z hs]
      have h3 : (Z.p Q').mapMatrix ((bc S.subtype u : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) =
        (Z.O Q').subtype.mapMatrix (y : Matrix (Fin n) (Fin n) (Z.O Q')) := congrArg Units.val hx1
      have h4 := congrArg (Z.O Q').subtype.mapMatrix (show cT t _ * _ * _ = _ from hy)
      rw [map_mul, map_mul] at h4
      rw [h3]
      exact h4
    · obtain ⟨Q₁, h1⟩ := Z.exists_bar hσ Q'
      have h1' : σ (Z.e Q₁) = Z.e Q' := by rw [← h1, hσ]
      obtain ⟨s', hs', -⟩ := Z.exists_conj hS h1'
      have e1 : Q₁ ≠ Q := fun e' => e (Z.e_injective (by rw [← h1', e', h]))
      have h3 : ∀ Q'', Q'' ≠ Q → (Z.p Q'').mapMatrix ((bc S.subtype u : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 :=
        fun Q'' e' => congrArg Units.val (hx2 Q'' e')
      rw [map_cT Z hs', h3 _ e, h3 _ e1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, one_mul, mul_one]
  obtain ⟨x', e, -, -⟩ := hm u ⟨hU, fun Q' hT => by
    rw [bc_r_one Z (hu2 _ fun e => hQ (e ▸ hT))]; exact one_mem _⟩
  exact ⟨bc (Z.pO Q) x', by rw [bc_pO, ← hu1, bc_pO, e, map_mul, map_mul, map_inv]⟩

theorem conj_of_smul {R : Type} [CommRing R] {z z' : R} (hz : z * z' = 1) {m x : GL (Fin n) R}
    (h : (m : Matrix (Fin n) (Fin n) R) = z • (x : Matrix (Fin n) (Fin n) R)) (y : GL (Fin n) R) :
    m * y * m⁻¹ = x * y * x⁻¹ ∧ m⁻¹ * y * m = x⁻¹ * y * x := by
  have h1 : ∀ y : GL (Fin n) R, (m * x⁻¹) * y = y * (m * x⁻¹) := fun y => Units.ext (by
    simp only [Units.val_mul, h, Matrix.smul_mul, Matrix.mul_smul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one])
  obtain ⟨w, rfl⟩ : ∃ w, m = w * x := ⟨m * x⁻¹, by group⟩
  rw [mul_inv_cancel_right] at h1
  constructor
  · calc _ = w * (x * y * x⁻¹) * w⁻¹ := by group
      _ = _ := by rw [h1]; group
  · calc _ = x⁻¹ * (w⁻¹ * (y * w)) * x := by group
      _ = _ := by rw [← h1]; group

theorem normaliser_core (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) (hn : n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hT : ∀ Q ∈ T, ∀ Q' ∈ T, σ (Z.e Q) ≠ Z.e Q')
    (hun : ∀ Q, σ (Z.e Q) = Z.e Q → ∃ δ : S, r Q (δ - ⟨σ δ, hS _ δ.2⟩) ≠ 0)
    (hψ : ∀ Q ∈ T, ψ Q ≠ 1) (ha : ∀ Q ∈ T, ∀ i j, symEdge ρ κ i j → a Q i j ≠ 0)
    {m : GL (Fin n) A} (hU : m ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (hm : Keeps r σ ρ κ G T ψ a m) (hm' : Keeps r σ ρ κ G T ψ a m⁻¹) :
    ∃ (z : A) (c : S) (x : GL (Fin n) S), z * σ z = 1 ∧ (c : A) * σ c = 1 ∧
      (∀ b : A, (∀ Q ∈ T, Z.p Q b ∈ Z.O Q ∧ Z.p Q (σ b) ∈ Z.O Q) → (1 - (c : A)) * b ∈ S) ∧
      (m : Matrix (Fin n) (Fin n) A) = z • ((bc S.subtype x : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      ∀ Q ∈ T, ∃ h ∈ unipSym (k Q) n ρ κ,
        ((bc (r Q) x : GL (Fin n) (k Q)) : Matrix (Fin n) (Fin n) (k Q)) = midDiag n ρ κ 1 (r Q c) * (h : Matrix (Fin n) (Fin n) (k Q)) := by
  classical
  choose bar hbar using Z.exists_bar hσ
  choose f hf0 hf using Z.exists_res
  have hb1 : ∀ Q ∈ T, Q ≠ bar Q := fun Q hQ e => hT Q hQ Q hQ (by rw [hbar, ← e])
  have hb2 : ∀ Q ∈ T, bar Q ∉ T := fun Q hQ e => hT Q hQ _ e (hbar Q)
  have hscT : ∀ Q ∈ T, IsScal (Z.O Q) (bc (Z.p Q) m) := fun Q hQ =>
    GlobalTheory.T.isScalarMul_integral_of_normalizes_symmetricLevel _ _ _ (f Q) (hf0 Q) n ρ κ hn hρ (ψ Q) (hψ Q hQ) (a Q) (ha Q hQ) _
      (fun y hy => by
        obtain ⟨y', h1, h2⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hm y fun _ => hy
        exact ⟨y', h1, (h2 hQ).2⟩)
      (fun y hy => by
        obtain ⟨y', h1, -⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hm' y fun _ => hy
        exact ⟨y', by rwa [map_inv, inv_inv] at h1⟩)
  obtain ⟨z₁, x₁, hz₁, hx₁⟩ := GlobalTheory.T.unitary_scalarMulIntegral_local_to_global Z σ hσ hS n G m hU fun Q => by
    by_cases hQ : Q ∈ T
    · exact Or.inl (hscT Q hQ)
    by_cases hQ' : bar Q ∈ T
    · exact Or.inr ⟨bar Q, by rw [← hbar, hσ], hscT _ hQ'⟩
    left
    by_cases e : Q = bar Q
    · have h1 : σ (Z.e Q) = Z.e Q := by rw [hbar, ← e]
      obtain ⟨δ, hδ⟩ := hun Q h1
      exact loc_inert Z hσ hS (by omega) hG h1 hQ δ hδ hm
    · refine GlobalTheory.T.isScalarMulIntegral_of_conj_integral_generators _ _ n _ _ (GlobalTheory.T.adjoin_range_GL_eq_top_matrix _ n) fun y _ => ?_
      obtain ⟨y', h1, -⟩ := loc_split Z hσ hS hG (hbar Q) e hQ' (hf Q) hm y fun h => absurd h hQ
      exact ⟨y', h1⟩
  have red : ∀ x : GL (Fin n) S, Keeps r σ ρ κ G T ψ a (bc S.subtype x) → ∀ Q ∈ T, ∀ h ∈ unipSym (k Q) n ρ κ,
      bc (r Q) x * h * (bc (r Q) x)⁻¹ ∈ unipSym (k Q) n ρ κ ∧
        ψ Q (edgeVal ρ κ (a Q) (bc (r Q) x * h * (bc (r Q) x)⁻¹)) = ψ Q (edgeVal ρ κ (a Q) h) := by
    intro x hx Q hQ h hh
    obtain ⟨y, rfl⟩ := bc_surjective (hf0 Q) h
    obtain ⟨y', h1, h2⟩ := loc_split Z hσ hS hG (hbar Q) (hb1 Q hQ) (hb2 Q hQ) (hf Q) hx y fun _ => hh
    have h3 : y' = bc (Z.pO Q) x * y * (bc (Z.pO Q) x)⁻¹ :=
      bc_injective (Z.O Q).subtype_injective (by rw [h1, map_mul, map_mul, map_inv, bc_pO])
    have h4 := h2 hQ
    rwa [h3, map_mul, map_mul, map_inv, bc_res Z (hf Q)] at h4
  have k1 : Keeps r σ ρ κ G T ψ a (bc S.subtype x₁) := fun x hx => by
    obtain ⟨x', h1, h2⟩ := hm x hx
    exact ⟨x', by rw [h1, (conj_of_smul hz₁ hx₁ _).1], h2⟩
  have k2 : Keeps r σ ρ κ G T ψ a (bc S.subtype x₁⁻¹) := fun x hx => by
    obtain ⟨x', h1, h2⟩ := hm' x hx
    exact ⟨x', by rw [h1, map_inv, inv_inv, inv_inv, (conj_of_smul hz₁ hx₁ _).2], h2⟩
  have fin : ∀ Q, ∃ s c : (k Q)ˣ, Q ∈ T → ∃ h ∈ unipSym (k Q) n ρ κ,
      ((bc (r Q) x₁ : GL (Fin n) (k Q)) : Matrix (Fin n) (Fin n) (k Q)) =
        midDiag n ρ κ (s : k Q) (c : k Q) * (h : Matrix (Fin n) (Fin n) (k Q)) := fun Q => by
    by_cases hQ : Q ∈ T
    · obtain ⟨s, c, h⟩ := GlobalTheory.T.normaliser_unipSym_char_pattern (k Q) n ρ κ hn hρ hκ (ψ Q) (hψ Q hQ) (a Q) (ha Q hQ) _ (red x₁ k1 Q hQ) fun h hh => by
        have := (red _ k2 Q hQ h hh).1
        rwa [map_inv, inv_inv] at this
      exact ⟨s, c, fun _ => h⟩
    · exact ⟨1, 1, fun h => absurd h hQ⟩
  choose s c hsc using fin
  obtain ⟨z₂, hz₂, hr₂, -⟩ := GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces Z σ hσ hS T hT s
  obtain ⟨c', hc', hrc, hsup⟩ := GlobalTheory.T.exists_normOne_with_residues_at_splitPlaces Z σ hσ hS T hT fun Q => (s Q)⁻¹ * c Q
  let w : S := ⟨σ z₂, hS _ z₂.2⟩
  have hw : z₂ * w = 1 := Subtype.ext hz₂
  have hw' : w * z₂ = 1 := by rw [mul_comm, hw]
  refine ⟨z₁ * z₂, c', ⟨w • x₁.1, z₂ • (x₁⁻¹).1, ?_, ?_⟩, ?_, hc', hsup, ?_, fun Q hQ => ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hw', Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hw, Units.inv_mul, one_smul]
  · rw [map_mul, mul_mul_mul_comm, hz₁, hz₂, one_mul]
  · rw [hx₁]
    ext i j
    show z₁ * _ = z₁ * z₂ * (σ z₂ * (x₁.1 i j : A))
    rw [mul_assoc, ← mul_assoc (z₂ : A), hz₂, one_mul]
    rfl
  · obtain ⟨h, hh, e⟩ := hsc Q hQ
    refine ⟨h, hh, ?_⟩
    have h1 : r Q w = ((s Q)⁻¹ : (k Q)ˣ) := by
      have := congrArg (r Q) hw
      rw [map_mul, map_one, hr₂ Q hQ] at this
      exact (Units.inv_eq_of_mul_eq_one_right this).symm
    ext i j
    have e' := congrFun (congrFun e i) j
    show r Q (w * x₁.1 i j) = _
    rw [map_mul, show r Q (x₁.1 i j) = _ from e', h1, hrc Q hQ]
    simp only [midDiag, Matrix.diagonal_mul]
    split_ifs
    · rw [Units.val_mul, mul_assoc]
    · rw [← mul_assoc, Units.inv_mul]

end GlobalTheory.LevNorm

end
