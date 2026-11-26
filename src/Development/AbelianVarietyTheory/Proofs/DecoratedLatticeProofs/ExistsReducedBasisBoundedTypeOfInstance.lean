module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorActionHermitianExpFixedOfMinNorm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameFamilyCompactRepresentation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulMatTranspose
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceFormRealCoordinatesIntegralGram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem unipotent_upper_inv_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  intro N C
  refine ⟨(Nat.factorial N : ℝ) * (max C 1) ^ N, ?_⟩
  intro n hd hl hb
  have htri : n.BlockTriangular id := fun i j h => hl i j h
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]; simp [hd]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  refine ⟨n⁻¹, Matrix.nonsing_inv_mul n hu, Matrix.mul_nonsing_inv n hu, ?_, ?_⟩
  · intro i j h
    letI := Matrix.invertibleOfIsUnitDet n hu
    exact Matrix.blockTriangular_inv_of_blockTriangular htri h
  · intro i j
    have hinv : n⁻¹ = n.adjugate := by rw [Matrix.inv_def, hdet]; simp
    rw [hinv, Matrix.adjugate_apply]
    have key := Matrix.det_le (abv := AbsoluteValue.abs) (x := max C 1)
      (A := n.updateRow j (Pi.single i 1)) ?_
    · simpa using key
    · intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self, Pi.single_apply]
        split_ifs <;> simp
      · rw [Matrix.updateRow_ne hk]
        exact le_trans (hb k l) (le_max_left _ _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBoundedStatement
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  first | exact @GlobalTheory.unipotent_upper_inv_bounded | exact GlobalTheory.unipotent_upper_inv_bounded | (intros; apply GlobalTheory.unipotent_upper_inv_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelReducedIntegralFormBoundedEntries
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelReducedIntegralFormBoundedEntries
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.RedBound

lemma entry_bound {N : ℕ} (P Z Q : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c : ℝ)
    (h : ∀ p q, |P i p * Z p q * Q q j| ≤ c) : |(P * Z * Q) i j| ≤ N * N * c := by
  have e : (P * Z * Q) i j = ∑ q, ∑ p, P i p * Z p q * Q q j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [e]
  calc |∑ q, ∑ p, P i p * Z p q * Q q j| ≤ ∑ q, |∑ p, P i p * Z p q * Q q j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q : Fin N, ∑ _p : Fin N, c := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => h p q)
    _ = N * N * c := by simp [Finset.sum_const, Finset.card_fin]; ring

lemma orth_entry_le {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (p q : Fin N) :
    |k p q| ≤ 1 := by
  have h1 : ∑ r, k r q * k r q = 1 := by
    have := congrFun (congrFun h q) q
    simpa [Matrix.mul_apply] using this
  have h2 : k p q * k p q ≤ ∑ r, k r q * k r q :=
    Finset.single_le_sum (f := fun r => k r q * k r q) (fun r _ => mul_self_nonneg _)
      (Finset.mem_univ p)
  rw [h1] at h2
  have h3 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact h2
  nlinarith [abs_nonneg (k p q)]

lemma le_of_le_idx {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : GlobalTheory.ClassFin.IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {i p : Fin N} (h : i ≤ p) : a i ≤ Cm * a p := by
  rcases h.lt_or_eq with h | h
  · exact (hS.le i p h).trans (mul_le_mul_of_nonneg_right hC (hS.pos p).le)
  · subst h; exact le_mul_of_one_le_left (hS.pos i).le h1

lemma prod_le {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : GlobalTheory.ClassFin.IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {p q r s : Fin N} (hr : p ≤ r) (hs : q ≤ s) : a p * a q ≤ Cm ^ 2 * (a r * a s) := by
  have har := le_of_le_idx hS h1 hC hr
  have has := le_of_le_idx hS h1 hC hs
  have h0 : 0 ≤ Cm * a r := mul_nonneg (by linarith) (hS.pos r).le
  calc a p * a q ≤ (Cm * a r) * (Cm * a s) := mul_le_mul har has (hS.pos q).le h0
    _ = Cm ^ 2 * (a r * a s) := by ring

end GlobalTheory.RedBound

namespace GlobalTheory.RedBound

theorem reduced_bound : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), GlobalTheory.ClassFin.IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) →
    B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) →
    (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X →
    ∀ i j, |(B i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨M, hM⟩ := GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded N C
  obtain ⟨Cm, hCm1, hCC⟩ : ∃ Cm : ℝ, 1 ≤ Cm ∧ C ≤ Cm := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨M₀, hM₀, hMM⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ M ≤ M₀ := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R₀, hR₀, hRR⟩ : ∃ R₀ : ℝ, 0 ≤ R₀ ∧ R ≤ R₀ := ⟨max R 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = N * N * (1 * R₀ * 1) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = N * N * K₁ + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := lt_of_lt_of_le one_pos hCm1
  have hR'0 : 0 ≤ R' := by rw [hR']; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨N * N * (Cm * (Cm ^ 2 * T * R') * Cm), ?_⟩
  intro k a n hS X B B' μ hμ hμR hX hB hB' i j
  obtain ⟨m, hmn, _hnm, hmlow, hmb⟩ := hM n hS.diag hS.lower hS.bdd
  have hmb' : ∀ p q, |m p q| ≤ M₀ := fun p q => (hmb p q).trans hMM
  have hnb : ∀ p q, |n p q| ≤ Cm := fun p q => (hS.bdd p q).trans hCC
  have hμ₀ : |μ| ≤ R₀ := hμR.trans hRR
  have hk : ∀ p q, |k p q| ≤ 1 := orth_entry_le k hS.orth
  obtain ⟨X', hX'def⟩ : ∃ X', X' = kᵀ * X * k := ⟨_, rfl⟩
  have hX' : ∀ p q, |X' p q| ≤ R' := by
    intro p q
    rw [hX'def, hR']
    apply entry_bound
    intro r s
    rw [abs_mul, abs_mul, Matrix.transpose_apply]
    exact mul_le_mul (mul_le_mul (hk r p) ((hX r s).trans hRR) (abs_nonneg _) zero_le_one)
      (hk s q) (abs_nonneg _) (by positivity)
  obtain ⟨Br', hBr'⟩ : ∃ Br', Br' = B'.map (Int.cast : ℤ → ℝ) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = n * Br' * nᵀ := ⟨_, rfl⟩
  have hWeq : diagonal a * W * diagonal a = μ • X' := by
    have h1 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k = μ • X' := by
      rw [hBr', hB', hX'def, Matrix.mul_smul, Matrix.smul_mul]
    rw [← h1, hWdef]
    have h2 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k =
        (kᵀ * k) * (diagonal a * (n * Br' * nᵀ) * diagonal a) * (kᵀ * k) := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [h2, hS.orth, Matrix.one_mul, Matrix.mul_one]
  have hWent : ∀ p q, a p * W p q * a q = μ * X' p q := by
    intro p q
    have := congrFun (congrFun hWeq p) q
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hBm : Br' = m * W * mᵀ := by
    rw [hWdef]
    calc Br' = (m * n) * Br' * (m * n)ᵀ := by rw [hmn]; simp
      _ = m * (n * Br' * nᵀ) * mᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hZ : B.map (Int.cast : ℤ → ℝ) = nᵀ * (diagonal a * X' * diagonal a) * n := by
    rw [hB, hX'def]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hA : ∀ p q, T ≤ a p * a q → B' p q = 0 := by
    intro p q hpq
    have hpos : 0 < a p * a q := mul_pos (hS.pos p) (hS.pos q)
    have hb : |Br' p q| ≤ N * N * (K₁ / (a p * a q)) := by
      rw [hBm]
      apply entry_bound
      intro r s
      rw [le_div_iff₀ hpos, Matrix.transpose_apply]
      by_cases hr : r < p
      · rw [hmlow p r hr]; simp; positivity
      by_cases hs : s < q
      · rw [hmlow q s hs]; simp; positivity
      push_neg at hr hs
      have hWb : |W r s| * (a r * a s) ≤ R₀ * R' := by
        calc |W r s| * (a r * a s) = |a r * W r s * a s| := by
              rw [abs_mul, abs_mul, abs_of_pos (hS.pos r), abs_of_pos (hS.pos s)]; ring
          _ = |μ| * |X' r s| := by rw [hWent r s, abs_mul]
          _ ≤ R₀ * R' := mul_le_mul hμ₀ (hX' r s) (abs_nonneg _) hR₀
      have hapq := prod_le hS hCm1 hCC hr hs
      rw [abs_mul, abs_mul, hK₁]
      calc |m p r| * |W r s| * |m q s| * (a p * a q)
          ≤ |m p r| * |W r s| * |m q s| * (Cm ^ 2 * (a r * a s)) :=
            mul_le_mul_of_nonneg_left hapq (by positivity)
        _ = |m p r| * (Cm ^ 2 * (|W r s| * (a r * a s))) * |m q s| := by ring
        _ ≤ M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ :=
            mul_le_mul (mul_le_mul (hmb' p r) (mul_le_mul_of_nonneg_left hWb (by positivity))
              (mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (mul_pos (hS.pos r) (hS.pos s)).le)) hM₀) (hmb' q s) (abs_nonneg _) (by positivity)
    have hlt : |Br' p q| < 1 := by
      have e : (N : ℝ) * N * (K₁ / (a p * a q)) = (N * N * K₁) / (a p * a q) := by ring
      rw [e] at hb
      exact hb.trans_lt ((div_lt_one hpos).mpr (by linarith))
    have h3 : |((B' p q : ℤ) : ℝ)| < 1 := by rw [hBr'] at hlt; simpa using hlt
    have h4 : |B' p q| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp h4
  have hBz : ∀ p q, Cm ^ 2 * T ≤ a p * a q → W p q = 0 := by
    intro p q h
    rw [hWdef]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_eq_zero
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r < p
    · rw [hS.lower p r hr]; ring
    by_cases hs : s < q
    · rw [hS.lower q s hs]; ring
    push_neg at hr hs
    have hapq := prod_le hS hCm1 hCC hr hs
    have hT' : T ≤ a r * a s := by
      have : Cm ^ 2 * T ≤ Cm ^ 2 * (a r * a s) := h.trans hapq
      exact le_of_mul_le_mul_left this (by positivity)
    have h0 := hA r s hT'
    simp [hBr', h0]
  have hZb : ∀ p q, |a p * X' p q * a q| ≤ Cm ^ 2 * T * R' := by
    intro p q
    by_cases h : Cm ^ 2 * T ≤ a p * a q
    · have e := hWent p q
      rw [hBz p q h] at e
      have h0 : μ * X' p q = 0 := by rw [← e]; ring
      have hx : X' p q = 0 := (mul_eq_zero.mp h0).resolve_left hμ
      rw [hx]; simp; positivity
    · push_neg at h
      calc |a p * X' p q * a q| = (a p * a q) * |X' p q| := by
            rw [abs_mul, abs_mul, abs_of_pos (hS.pos p), abs_of_pos (hS.pos q)]; ring
        _ ≤ (Cm ^ 2 * T) * R' := mul_le_mul h.le (hX' p q) (abs_nonneg _) (by positivity)
  have hBe : (B i j : ℝ) = (nᵀ * (diagonal a * X' * diagonal a) * n) i j := by
    rw [← hZ]; simp
  rw [hBe]
  apply entry_bound
  intro r s
  have hZe : (diagonal a * X' * diagonal a) r s = a r * X' r s * a s := by
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transpose_apply, hZe, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hnb r i) (hZb r s) (abs_nonneg _) hCm0.le) (hnb s j)
    (abs_nonneg _) (by positivity)

end GlobalTheory.RedBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelReducedIntegralFormBoundedEntriesStatement
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelReduced_integral_form_bounded_entries : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), GlobalTheory.ClassFin.IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) → B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) → (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X → ∀ i j, |(B i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.RedBound.reduced_bound | exact GlobalTheory.RedBound.reduced_bound | (intros; apply GlobalTheory.RedBound.reduced_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBounded
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.ReducedBasisBound

lemma abs_sum_le_card {N : ℕ} (f : Fin N → ℝ) (B : ℝ) (h : ∀ p, |f p| ≤ B) :
    |∑ p, f p| ≤ N * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p, |f p| ≤ ∑ _p : Fin N, B := Finset.sum_le_sum (fun p _ => h p)
    _ = N * B := by simp

lemma entry_eq {N : ℕ} (a : Fin N → ℝ) (n Z P : Matrix (Fin N) (Fin N) ℝ)
    (h : diagonal a * n * P = Z * diagonal a * n) (p j : Fin N) :
    a p * (n * P) p j = ∑ q, Z p q * a q * n q j := by
  have := congrFun (congrFun h p) j
  rw [Matrix.mul_assoc, diagonal_mul] at this
  rw [this, Matrix.mul_apply]
  simp [mul_diagonal]

lemma int_eq_zero {x : ℤ} (h : |(x : ℝ)| < 1) : x = 0 := by
  have : |x| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

lemma integral_entry_eq_zero (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T)
    (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hmn : m * n = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hε : 0 < ε) (hK : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1) :
    ∀ i j, a i ≤ ε * a j → M' j i = 0 := by
  intro i j hij
  apply int_eq_zero
  have hC0 : 0 ≤ C₁ := by linarith
  have hM' : M'.map (Int.cast : ℤ → ℝ) = m * (n * M'.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, j ≤ p → |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ N * (T * C₁ ^ 3 * ε) := by
    intro p hp
    have he := entry_eq a n Zᵀ _ h2 p i
    have hb : |∑ q, Zᵀ p q * a q * n q i| ≤ N * (T * C₁ ^ 3 * ε * a p) := by
      apply abs_sum_le_card
      intro q
      rcases le_or_gt q i with hq | hq
      · have haq : a q ≤ C₁ ^ 2 * ε * a p := by
          calc a q ≤ C₁ * a i := hle q i hq
            _ ≤ C₁ * (ε * a j) := by gcongr
            _ ≤ C₁ * (ε * (C₁ * a p)) := by gcongr; exact hle j p hp
            _ = C₁ ^ 2 * ε * a p := by ring
        rw [abs_mul, abs_mul, transpose_apply, abs_of_pos (ha q)]
        calc |Z q p| * a q * |n q i| ≤ T * (C₁ ^ 2 * ε * a p) * C₁ := by
              have := ha p
              exact mul_le_mul (mul_le_mul (hZ q p) haq (ha q).le hT) (hn q i) (abs_nonneg _) (by positivity)
          _ = T * C₁ ^ 3 * ε * a p := by ring
      · rw [hn_low q i hq]
        have := ha p
        simp only [mul_zero, abs_zero]
        positivity
    have : a p * |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ a p * (N * (T * C₁ ^ 3 * ε)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ ^ 3 * ε * a p) := hb
        _ = a p * (N * (T * C₁ ^ 3 * ε)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M' j i : ℤ) : ℝ) = (M'.map (Int.cast : ℤ → ℝ)) j i := by simp
  rw [hentry, hM', Matrix.mul_apply]
  refine lt_of_le_of_lt (abs_sum_le_card _ _ (fun p => ?_)) hK
  rcases le_or_gt j p with hp | hp
  · rw [abs_mul]
    exact mul_le_mul (hm j p) (hE p hp) (abs_nonneg _) hCm
  · rw [hm_low j p hp, zero_mul, abs_zero]
    have : (0 : ℝ) ≤ N * (T * C₁ ^ 3 * ε) := by positivity
    positivity

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

lemma conj_entry_eq_zero (hC : 1 ≤ C₁) (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hnm : n * m = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hA : ∀ i j, a i ≤ ε * a j → M' j i = 0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * C₁ ^ 2 = ε) :
    ∀ i j, a i ≤ δ * a j → Z i j = 0 := by
  intro i j hij
  have hC0 : 0 ≤ C₁ := by linarith
  have h := congrArg (· * m) h2
  simp only [Matrix.mul_assoc] at h
  rw [hnm, Matrix.mul_one] at h
  have e := congrFun (congrFun h j) i
  rw [diagonal_mul, mul_diagonal, transpose_apply] at e
  have hz : (n * (M'.map (Int.cast : ℤ → ℝ) * m)) j i = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro p _
    rcases lt_or_ge p j with hp | hp
    · rw [hn_low j p hp, zero_mul]
    · have hin : (M'.map (Int.cast : ℤ → ℝ) * m) p i = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro q _
        rcases lt_or_ge i q with hq | hq
        · rw [hm_low q i hq, mul_zero]
        · have hq' : a q ≤ ε * a p := by
            calc a q ≤ C₁ * a i := hle q i hq
              _ ≤ C₁ * (δ * a j) := by gcongr
              _ ≤ C₁ * (δ * (C₁ * a p)) := by gcongr; exact hle j p hp
              _ = ε * a p := by rw [← hδ]; ring
          rw [Matrix.map_apply, hA q p hq']
          simp
      rw [hin, mul_zero]
  rw [hz, mul_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_right (ne_of_gt (ha i))

lemma entry_bound_of_vanishing (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T) (ha : ∀ i, 0 < a i)
    (hmn : m * n = 1) (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M : Matrix (Fin N) (Fin N) ℤ)
    (h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n)
    (δ : ℝ) (hδ : 0 < δ) (hB : ∀ i j, a i ≤ δ * a j → Z i j = 0) :
    ∀ i j, |(M i j : ℝ)| ≤ N * (Cm * (N * (T * C₁ / δ))) := by
  intro i j
  have hC0 : 0 ≤ C₁ := by linarith
  have hM : M.map (Int.cast : ℤ → ℝ) = m * (n * M.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ N * (T * C₁ / δ) := by
    intro p
    have he := entry_eq a n Z _ h1 p j
    have hb : |∑ q, Z p q * a q * n q j| ≤ N * (T * C₁ / δ * a p) := by
      apply abs_sum_le_card
      intro q
      have := ha p
      by_cases hz : Z p q = 0
      · rw [hz]
        simp only [zero_mul, abs_zero]
        positivity
      · have hlt : δ * a q < a p := by
          by_contra hc
          exact hz (hB p q (not_lt.mp hc))
        have haq : a q ≤ a p / δ := by rw [le_div_iff₀ hδ]; linarith
        rw [abs_mul, abs_mul, abs_of_pos (ha q)]
        calc _ ≤ T * (a p / δ) * C₁ :=
              mul_le_mul (mul_le_mul (hZ p q) haq (ha q).le hT) (hn q j) (abs_nonneg _) (by positivity)
          _ = T * C₁ / δ * a p := by ring
    have : a p * |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ a p * (N * (T * C₁ / δ)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ / δ * a p) := hb
        _ = a p * (N * (T * C₁ / δ)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M i j : ℤ) : ℝ) = (M.map (Int.cast : ℤ → ℝ)) i j := by simp
  rw [hentry, hM, Matrix.mul_apply]
  exact abs_sum_le_card _ _ (fun p => by
    rw [abs_mul]; exact mul_le_mul (hm i p) (hE p) (abs_nonneg _) hCm)

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

lemma abs_entry_le_one {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (l i : Fin N) :
    |k l i| ≤ 1 := by
  have e := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, one_apply_eq] at e
  simp only [transpose_apply] at e
  have : k l i ^ 2 ≤ 1 := by
    rw [← e, sq]
    exact Finset.single_le_sum (f := fun l => k l i * k l i) (fun l _ => mul_self_nonneg _)
      (Finset.mem_univ l)
  exact sq_le_one_iff_abs_le_one _ |>.mp this

lemma conj_bound {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℝ) (hk : ∀ l i, |k l i| ≤ 1) (R : ℝ)
    (hR : 0 ≤ R) (hX : ∀ i j, |X i j| ≤ R) (i j : Fin N) :
    |(kᵀ * X * k) i j| ≤ N * (N * R) := by
  rw [Matrix.mul_apply]
  apply abs_sum_le_card
  intro q
  rw [abs_mul]
  have hin : |(kᵀ * X) i q| ≤ N * R := by
    rw [Matrix.mul_apply]
    apply abs_sum_le_card
    intro l
    rw [abs_mul, transpose_apply]
    calc |k l i| * |X l q| ≤ 1 * R := mul_le_mul (hk l i) (hX l q) (abs_nonneg _) zero_le_one
      _ = R := one_mul R
  calc |(kᵀ * X) i q| * |k q j| ≤ (N * R) * 1 := mul_le_mul hin (hk q j) (abs_nonneg _) (by positivity)
    _ = N * R := mul_one _

theorem integral_conj_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ)
    (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), GlobalTheory.ClassFin.IsSiegel C k a n →
    ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) →
    (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) →
    (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) →
    ∀ i j, |(M i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨C₁, hC₁d⟩ : ∃ C₁ : ℝ, C₁ = max C 1 := ⟨_, rfl⟩
  obtain ⟨Cm0, hCm0⟩ := GlobalTheory.unipotent_upper_inv_bounded N C₁
  obtain ⟨Cm, hCmd⟩ : ∃ Cm : ℝ, Cm = max Cm0 0 := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = N * (N * max R 0) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = N * (Cm * (N * (T * C₁ ^ 3))) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = 1 / (K + 1) := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε / C₁ ^ 2 := ⟨_, rfl⟩
  refine ⟨N * (Cm * (N * (T * C₁ / δ))), ?_⟩
  intro k a n hs X M M' hX hM hM'
  have hC : 1 ≤ C₁ := hC₁d ▸ le_max_right _ _
  have hC₁pos : 0 < C₁ := by linarith
  have hCm : 0 ≤ Cm := hCmd ▸ le_max_right _ _
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hT : 0 ≤ T := by rw [hTd]; positivity
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hε : 0 < ε := by rw [hεd]; positivity
  have hKε : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1 := by
    have e : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) = K * (1 / (K + 1)) := by
      rw [← hεd, hKd]; ring
    rw [e, mul_one_div, div_lt_one (by linarith)]
    linarith
  have hδ : 0 < δ := by rw [hδd]; positivity
  have hδε : δ * C₁ ^ 2 = ε := by rw [hδd]; field_simp
  have hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hs.le i j h).trans
        (mul_le_mul_of_nonneg_right (hC₁d ▸ le_max_left _ _) (hs.pos j).le)
    · subst h
      nlinarith [hs.pos i]
  have hn : ∀ i j, |n i j| ≤ C₁ := fun i j => (hs.bdd i j).trans (hC₁d ▸ le_max_left _ _)
  obtain ⟨m, hmn, hnm, hm_low, hm⟩ := hCm0 n hs.diag hs.lower hn
  have hm' : ∀ i j, |m i j| ≤ Cm := fun i j => (hm i j).trans (hCmd ▸ le_max_left _ _)
  have hk := abs_entry_le_one k hs.orth
  obtain ⟨Z, hZd⟩ : ∃ Z : Matrix (Fin N) (Fin N) ℝ, Z = kᵀ * X * k := ⟨_, rfl⟩
  have hZ : ∀ i j, |Z i j| ≤ T := by
    intro i j
    rw [hZd, hTd]
    exact conj_bound k X hk _ hR (fun i j => (hX i j).trans (le_max_left _ _)) i j
  have h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
  have h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM'
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hA := integral_entry_eq_zero hC hCm hT hs.pos hle hmn hs.lower hm_low hn hm' hZ M' h2 ε hε hKε
  have hB := conj_entry_eq_zero hC hs.pos hle hnm hs.lower hm_low M' h2 ε hA δ hδ.le hδε
  exact entry_bound_of_vanishing hC hCm hT hs.pos hmn hn hm' hZ M h1 δ hδ hB

end GlobalTheory.ReducedBasisBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedBasisIntegralConjEntriesBoundedStatement
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedBasis_integral_conj_entries_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), GlobalTheory.ClassFin.IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) → (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) → (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) → ∀ i j, |(M i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.ReducedBasisBound.integral_conj_bounded | exact GlobalTheory.ReducedBasisBound.integral_conj_bounded | (intros; apply GlobalTheory.ReducedBasisBound.integral_conj_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSetEntryBoundOfLatticeMin
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory

theorem siegelSet_entry_bound_of_lattice_min (N : ℕ) (C : ℝ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ) (hS : GlobalTheory.ClassFin.IsSiegel C k a n) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hmin : ∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖)
    (i j : Fin N) : |(k * diagonal a * n) i j| * t ^ N ≤ N * C ^ N := by
  have hN : 0 < N := Fin.pos i
  set i0 : Fin N := ⟨0, hN⟩ with hi0

  have hk : ∀ p q, |k p q| ≤ 1 := by
    intro p q
    have h := congrFun (congrFun hS.orth q) q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have : k p q * k p q ≤ ∑ x, k x q * k x q :=
      Finset.single_le_sum (f := fun x => k x q * k x q) (fun x _ => mul_self_nonneg _) (Finset.mem_univ p)
    rw [h] at this
    have h2 : |k p q| ^ 2 ≤ 1 := by rw [sq_abs, sq]; exact this
    nlinarith [abs_nonneg (k p q)]
  have hC1 : 1 ≤ C := by
    have := hS.bdd i i
    rw [hS.diag i, abs_one] at this
    exact this

  have hg : ∀ p q, (k * diagonal a * n) p q = ∑ l, k p l * a l * n l q := by
    intro p q
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]

  have hcol : ∀ p, (k * diagonal a * n) p i0 = k p i0 * a i0 := by
    intro p
    rw [hg, Finset.sum_eq_single i0]
    · rw [hS.diag i0, mul_one]
    · intro l _ hl
      have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      rw [hS.lower l i0 this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have ha0 : t ≤ a i0 := by
    have h := hmin (Pi.single i0 1) (by
      intro h; have := congrFun h i0; simp at this)
    refine h.trans ?_
    refine (pi_norm_le_iff_of_nonneg (le_of_lt (hS.pos i0))).2 ?_
    intro p
    have : ((k * diagonal a * n) *ᵥ fun i => (((Pi.single i0 (1:ℤ) : Fin N → ℤ) i : ℤ) : ℝ)) p
        = (k * diagonal a * n) p i0 := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hcol, Real.norm_eq_abs, abs_mul, abs_of_pos (hS.pos i0)]
    exact mul_le_of_le_one_left (le_of_lt (hS.pos i0)) (hk p i0)
  have hlow : ∀ l, t ≤ C * a l := by
    intro l
    by_cases hl : l = i0
    · subst hl
      nlinarith [hS.pos i0]
    · have : i0 < l := by
        rcases lt_or_gt_of_ne hl with h | h
        · exact absurd h (by simp [hi0, Fin.lt_def])
        · exact h
      exact ha0.trans (hS.le i0 l this)
  have hup : ∀ l, a l * t ^ (N - 1) ≤ C ^ (N - 1) := by
    intro l
    have hprod : ∏ x ∈ Finset.univ.erase l, t ≤ ∏ x ∈ Finset.univ.erase l, (C * a x) :=
      Finset.prod_le_prod₀ (fun _ _ => le_of_lt ht0) (fun x _ => hlow x)
    rw [Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin] at hprod
    have h1 : a l * ∏ x ∈ Finset.univ.erase l, a x = 1 := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ l)]; exact hS.prod_eq
    have hal := le_of_lt (hS.pos l)
    calc a l * t ^ (N - 1) ≤ a l * (C ^ (N - 1) * ∏ x ∈ Finset.univ.erase l, a x) :=
          mul_le_mul_of_nonneg_left hprod hal
      _ = C ^ (N - 1) * (a l * ∏ x ∈ Finset.univ.erase l, a x) := by ring
      _ = C ^ (N - 1) := by rw [h1, mul_one]
  have hent : |(k * diagonal a * n) i j| ≤ ∑ l, a l * C := by
    rw [hg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_mul, abs_of_pos (hS.pos l)]
    have h1 := hk i l
    have h2 := hS.bdd l j
    have hal := le_of_lt (hS.pos l)
    calc |k i l| * a l * |n l j| ≤ 1 * a l * C := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hal) h2 (abs_nonneg _) (by positivity)
      _ = a l * C := by ring
  have htN : t ^ N = t ^ (N - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have htpow : 0 ≤ t ^ N := by positivity
  calc |(k * diagonal a * n) i j| * t ^ N ≤ (∑ l, a l * C) * t ^ N :=
        mul_le_mul_of_nonneg_right hent htpow
    _ = ∑ l, (a l * t ^ (N - 1)) * C * t := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; rw [htN]; ring
    _ ≤ ∑ l : Fin N, C ^ (N - 1) * C * 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hup l) (by linarith)) ht1 (le_of_lt ht0)
        positivity
    _ = N * C ^ N := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← pow_succ,
          Nat.sub_add_cancel hN]

theorem siegel_entry_bound : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), GlobalTheory.ClassFin.IsSiegel C k a n → ∀ t : ℝ, 0 < t → t ≤ 1 →
    (∀ z : Fin N → ℤ, z ≠ 0 → t ≤ ‖(k * diagonal a * n) *ᵥ fun i => (z i : ℝ)‖) →
    ∀ i j, |(k * diagonal a * n) i j| * t ^ N ≤ C' :=
  fun N C => ⟨N * C ^ N, fun k a n hS t ht0 ht1 hmin i j =>
    siegelSet_entry_bound_of_lattice_min N C k a n hS t ht0 ht1 hmin i j⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstance
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.RedBasisPf

variable (I : AutInst)

theorem vec_sum_zsmul (y : I.Ginf) {N : ℕ} (z : Fin N → ℤ) (e : Fin N → Fin I.n → I.E) :
    vec I y (∑ j, z j • e j) = ∑ j, z j • vec I y (e j) := by
  exact MulCoord.vec_sum_zsmul I y e z

theorem gm_mulVec {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) (z : Fin N → ℤ) :
    gm I ρ y e *ᵥ (fun j => (z j : ℝ)) = ρ (vec I y (∑ j, z j • e j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [vec_sum_zsmul, map_sum]
  funext i
  simp only [map_zsmul]
  simp only [gm, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gm_change {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)) (y : I.Ginf)
    (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin N) (Fin N) ℤ) :
    gm I ρ y (fun j => ∑ i, M i j • e i) = gm I ρ y e * M.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [gm, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [vec_sum_zsmul I y (fun k => M k j) e, map_sum]
  simp only [map_zsmul]
  simp only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sum_change {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) (e : Fin N → Fin I.n → I.E) (w : Fin N → ℤ) :
    ∑ j, w j • (∑ i, M i j • e i) = ∑ i, (M *ᵥ w) i • e i := by
  simp only [Finset.smul_sum, smul_smul, mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem isZBasis_change {N : ℕ} (e : Fin N → Fin I.n → I.E) (he : IsZBasis I e)
    (M : Matrix (Fin N) (Fin N) ℤ) (hM : IsUnit M.det) : IsZBasis I (fun j => ∑ i, M i j • e i) := by
  obtain ⟨hli, hspan⟩ := he
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hinv' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨?_, fun u => ?_⟩
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg i
    rw [sum_change] at hg
    have hMg : M *ᵥ g = 0 := funext (hli _ hg)
    have hg' : g = M⁻¹ *ᵥ (M *ᵥ g) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    rw [hg', hMg, Matrix.mulVec_zero]
    rfl
  · rw [hspan u]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨M⁻¹ *ᵥ z, ?_⟩
      rw [sum_change, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    · rintro ⟨w, rfl⟩
      exact ⟨M *ᵥ w, sum_change I M e w⟩

theorem norm_le_sqrt {N : ℕ} {ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)}
    (hρ : IsRealCoord I ρ) (x : InfinitePlace I.F → Fin I.n → ℂ) : ‖x‖ ≤ Real.sqrt N * ‖ρ x‖ := by
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hsq : ∀ v i, ‖x v i‖ ^ 2 ≤ N * ‖ρ x‖ ^ 2 := by
    intro v i
    have h1 : ‖x v i‖ ^ 2 ≤ ∑ w, ∑ k, (star (x w k) * x w k).re := by
      simp only [hre]
      calc ‖x v i‖ ^ 2 ≤ ∑ k, ‖x v k‖ ^ 2 :=
            Finset.single_le_sum (f := fun k => ‖x v k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
        _ ≤ ∑ w, ∑ k, ‖x w k‖ ^ 2 :=
            Finset.single_le_sum (f := fun w => ∑ k, ‖x w k‖ ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ v)
    rw [← hρ x x] at h1
    refine h1.trans ?_
    unfold dotProduct
    calc ∑ k, ρ x k * ρ x k ≤ ∑ _k : Fin N, ‖ρ x‖ ^ 2 := Finset.sum_le_sum fun k _ => by
            have hk := norm_le_pi_norm (ρ x) k
            rw [Real.norm_eq_abs] at hk
            have h := mul_self_le_mul_self (abs_nonneg _) hk
            rw [abs_mul_abs_self] at h
            nlinarith [h]
      _ = N * ‖ρ x‖ ^ 2 := by simp
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h := Real.sqrt_le_sqrt (hsq v i)
  rwa [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

def entSum {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) : ℝ := ∑ i, ∑ j, |X i j|

theorem abs_le_entSum {N : ℕ} (X : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) : |X i j| ≤ entSum X := by
  unfold entSum
  calc |X i j| ≤ ∑ j', |X i j'| :=
        Finset.single_le_sum (f := fun j' => |X i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |X i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |X i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

end GlobalTheory.CuspGeo.RedBasisPf

end

noncomputable section

namespace GlobalTheory.CuspGeo.RedBasisPf

theorem smul_conj {N : ℕ} (l c : ℝ) (A X : Matrix (Fin N) (Fin N) ℝ) :
    (l • A)ᵀ * (c • X) * (l • A) = (l * c * l) • (Aᵀ * X * A) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ring_nf

theorem smul_conj' {N : ℕ} (l : ℝ) (A B : Matrix (Fin N) (Fin N) ℝ) :
    (l • A) * B * (l • A)ᵀ = (l * l) • (A * B * Aᵀ) := by
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

end GlobalTheory.CuspGeo.RedBasisPf


open GlobalTheory.CuspGeo.RedBasisPf in
theorem GlobalTheory.CuspGeo.redBasis_holds : ∀ I : AutInst, RedBasis I := by
  intro I
  obtain ⟨N, e0, ρ, d, hd, he0, hρ, hdet⟩ := covolume_const I
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨0, 0, 0, fun y => ⟨e0, he0, ⟨fun k j => j.elim0, fun i => i.elim0⟩, fun t _ _ _ j => j.elim0⟩⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨lam, hlam0, hlamN⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ^ N * d = 1 := by
    refine ⟨(d⁻¹) ^ ((N : ℝ)⁻¹), Real.rpow_pos_of_pos (inv_pos.2 hd) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_pos.2 hd).le, inv_mul_cancel₀ hNr.ne', Real.rpow_one,
      inv_mul_cancel₀ hd.ne']
  obtain ⟨c', hc'0, hc'1, hc'2⟩ : ∃ c' : ℝ, 0 < c' ∧ c' ≤ 1 ∧ c' ≤ lam / Real.sqrt N :=
    ⟨min 1 (lam / Real.sqrt N), lt_min one_pos (div_pos hlam0 (Real.sqrt_pos.2 hNr)), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨C0, hC0⟩ := siegel_cover (Fin N)
  obtain ⟨C1, hC1⟩ := siegel_entry_bound N C0
  have hint : ∀ k, IsIntegral ℤ (integralBasis I.E k) := by
    intro k
    rw [integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  choose X hX using fun k => MulCoord.mul_conj_coord I N ρ hρ _ (hint k)
  choose C2 hC2 using fun k => GlobalTheory.T.reducedBasis_integral_conj_entries_bounded N C0 (entSum (X k))
  obtain ⟨Xt, μ, c, hμ, hc, hXt⟩ := GlobalTheory.T.traceForm_real_coordinates_integral_gram I N ρ hρ
  obtain ⟨s, hs⟩ : ∃ s : ℝ, lam * s * lam = 1 := ⟨lam⁻¹ * lam⁻¹, by field_simp⟩
  obtain ⟨μ', hμ'0, hμ'⟩ : ∃ μ' : ℝ, μ' ≠ 0 ∧ lam * lam * μ = μ' * s := by
    refine ⟨lam * lam * μ * lam * lam, by positivity, ?_⟩
    have hs' : s = lam⁻¹ * lam⁻¹ := by
      field_simp
      linarith
    rw [hs']
    field_simp
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.siegelReduced_integral_form_bounded_entries N C0 (max |μ'| (entSum (s • Xt)))
  refine ⟨N, max (∑ k, |C2 k|) C3, Real.sqrt N * (lam⁻¹ * C1 / c' ^ N), fun y => ?_⟩
  have hdy := hdet y
  obtain ⟨S, hSu, hSd⟩ : ∃ S : Matrix (Fin N) (Fin N) ℤ, IsUnit S.det ∧
      (gm I ρ y e0 * S.map (Int.cast : ℤ → ℝ)).det = d := by
    rcases le_or_gt 0 (gm I ρ y e0).det with hpos | hneg
    · refine ⟨1, by simp, ?_⟩
      rw [Matrix.det_mul]
      simp only [Matrix.map_one Int.cast Int.cast_zero Int.cast_one, Matrix.det_one, mul_one]
      rw [← hdy, abs_of_nonneg hpos]
    · let f : Fin N → ℤ := fun i => if i = ⟨0, hN⟩ then -1 else 1
      have hf : ∏ i, f i = -1 := by
        simp [f, Finset.prod_ite_eq']
      refine ⟨Matrix.diagonal f, by rw [Matrix.det_diagonal, hf]; exact isUnit_one.neg, ?_⟩
      rw [Matrix.det_mul, Matrix.diagonal_map Int.cast_zero, Matrix.det_diagonal]
      have hf' : ∏ i, ((f i : ℤ) : ℝ) = -1 := by
        rw [← Int.cast_prod, hf]
        simp
      rw [hf', ← hdy, abs_of_neg hneg]
      ring
  let e1 : Fin N → Fin I.n → I.E := fun j => ∑ i, S i j • e0 i
  have he1 : IsZBasis I e1 := isZBasis_change I e0 he0 S hSu
  have hg1 : gm I ρ y e1 = gm I ρ y e0 * S.map Int.cast := gm_change I ρ y e0 S
  have hdet1 : (lam • gm I ρ y e1).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hg1, hSd, hlamN]
  obtain ⟨γ, hγ, k, a, n, hsieg, hfac⟩ := hC0 _ hdet1
  let e : Fin N → Fin I.n → I.E := fun j => ∑ i, γ i j • e1 i
  have he : IsZBasis I e := isZBasis_change I e1 he1 γ (by rw [hγ]; exact isUnit_one)
  have hK : k * Matrix.diagonal a * n = lam • gm I ρ y e := by
    rw [← hfac, gm_change I ρ y e1 γ, Matrix.smul_mul]
  refine ⟨e, he, ⟨fun kk j => ?_, fun i j => ?_⟩, fun t ht0 ht1 hns j => ?_⟩
  · obtain ⟨M, M', h1, h2, h3⟩ := hX kk y e he
    refine ⟨fun i => M i j, h3 j, fun i => ?_⟩
    have hb := hC2 kk k a n hsieg (X kk) M M' (fun i j => abs_le_entSum (X kk) i j)
      (by rw [hK, Matrix.smul_mul, h1, Matrix.mul_smul])
      (by rw [hK, Matrix.smul_mul, h2, Matrix.mul_smul]) i j
    calc |((M i j : ℤ) : ℝ)| ≤ C2 kk := hb
      _ ≤ |C2 kk| := le_abs_self _
      _ ≤ ∑ k, |C2 k| := Finset.single_le_sum (f := fun k => |C2 k|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ kk)
      _ ≤ _ := le_max_left _ _
  · obtain ⟨B, B', hB1, hB2, hB3⟩ := hXt y e he
    have hb := hC3 k a n hsieg (s • Xt) B B' μ' hμ'0 (le_max_left _ _)
      (fun i j => (abs_le_entSum (s • Xt) i j).trans (le_max_right _ _))
      (by rw [hK, smul_conj, hs, one_smul, hB1])
      (by rw [hK, smul_conj', hB2, smul_smul, smul_smul, hμ']) i j
    have hcast : ((B i j : ℤ) : ℝ) = (c : ℝ) * ((trForm I (e i) (e j) : ℚ) : ℝ) := by
      exact_mod_cast hB3 i j
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have htr : |((trForm I (e i) (e j) : ℚ) : ℝ)| ≤ |((B i j : ℤ) : ℝ)| := by
      rw [hcast, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c)]
      nlinarith [abs_nonneg ((trForm I (e i) (e j) : ℚ) : ℝ)]
    exact htr.trans (hb.trans (le_max_right _ _))
  · have hz : ∀ z : Fin N → ℤ, z ≠ 0 → c' * t ≤ ‖(k * Matrix.diagonal a * n) *ᵥ fun i => (z i : ℝ)‖ := by
      intro z hz
      rw [hK, Matrix.smul_mulVec, gm_mulVec, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
      have hu : (∑ j, z j • e j) ≠ 0 := by
        intro h
        apply hz
        exact funext (Fintype.linearIndependent_iff.1 he.1 z h)
      have hiv : IntVec I (∑ j, z j • e j) := (he.2 _).2 ⟨z, rfl⟩
      have h1 : t ≤ ‖vec I y (∑ j, z j • e j)‖ := hns _ hiv hu
      have h2 := norm_le_sqrt I hρ (vec I y (∑ j, z j • e j))
      have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
      calc c' * t ≤ lam / Real.sqrt N * t := mul_le_mul_of_nonneg_right hc'2 ht0.le
        _ ≤ lam / Real.sqrt N * (Real.sqrt N * ‖ρ (vec I y (∑ j, z j • e j))‖) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = lam * ‖ρ (vec I y (∑ j, z j • e j))‖ := by field_simp
    have hbound := hC1 k a n hsieg (c' * t) (mul_pos hc'0 ht0) (by nlinarith) hz
    have hcol : ∀ i, |ρ (vec I y (e j)) i| * t ^ N ≤ lam⁻¹ * C1 / c' ^ N := by
      intro i
      have hij := hbound i j
      have hKij : (k * Matrix.diagonal a * n) i j = lam * ρ (vec I y (e j)) i := by
        rw [hK]
        simp [gm]
      rw [hKij, abs_mul, abs_of_pos hlam0, mul_pow] at hij
      rw [le_div_iff₀ (pow_pos hc'0 N)]
      calc |ρ (vec I y (e j)) i| * t ^ N * c' ^ N
          = lam⁻¹ * (lam * |ρ (vec I y (e j)) i| * (c' ^ N * t ^ N)) := by field_simp
        _ ≤ lam⁻¹ * C1 := by gcongr
    have hD : 0 ≤ lam⁻¹ * C1 / c' ^ N := (by positivity : (0 : ℝ) ≤ |ρ (vec I y (e j)) j| * t ^ N).trans (hcol j)
    have hρn : ‖ρ (vec I y (e j))‖ ≤ lam⁻¹ * C1 / c' ^ N / t ^ N := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos ht0 N)]
      exact hcol i
    calc ‖vec I y (e j)‖ * t ^ N ≤ Real.sqrt N * ‖ρ (vec I y (e j))‖ * t ^ N :=
          mul_le_mul_of_nonneg_right (norm_le_sqrt I hρ _) (by positivity)
      _ ≤ Real.sqrt N * (lam⁻¹ * C1 / c' ^ N / t ^ N) * t ^ N := by gcongr
      _ = Real.sqrt N * (lam⁻¹ * C1 / c' ^ N) := by field_simp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReducedBasisBoundedTypeOfInstanceStatement
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsReducedBasisBoundedType_of_instance : ∀ I : AutInst, RedBasis I := by
  first | exact @GlobalTheory.CuspGeo.redBasis_holds | exact GlobalTheory.CuspGeo.redBasis_holds | (intros; apply GlobalTheory.CuspGeo.redBasis_holds <;> assumption)
end
