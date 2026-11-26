module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergTranslateFixedIntegralUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralGramOfPhaseConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompleteSquareDiagonalNegPowUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompleteSquareDiagonalNegPowUniformizer
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.SquareDiag

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n' : ℕ}

def selE (a : Fin n' → ℕ) (n : ℕ) : Matrix (Fin n') (Fin n) L :=
  Matrix.of fun i p => if (i : ℕ) = (p : ℕ) ∧ 0 < a i then 1 else 0

def halfSel (a : Fin n' → ℕ) (i j : Fin n') : L :=
  if a i < a j ∨ (a i = a j ∧ (i : ℕ) < (j : ℕ)) then 1 else if (i : ℕ) = (j : ℕ) then 2⁻¹ else 0

theorem diag_sel (ϖ : L) (a : Fin n' → ℕ) (n : ℕ) :
    (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) =
      (diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) : Matrix (Fin n') (Fin n') L) * (selE a n : Matrix (Fin n') (Fin n) L) := by
  ext i j
  simp only [Matrix.diagonal_mul, selE, Matrix.of_apply]
  split_ifs <;> simp

theorem selE_mul_transpose (a : Fin n' → ℕ) (n : ℕ) :
    (selE (L := L) a n : Matrix (Fin n') (Fin n) L) * (selE a n : Matrix (Fin n') (Fin n) L)ᵀ = diagonal (fun i : Fin n' => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [selE, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : (i : ℕ) < n ∧ 0 < a i
  · rw [Finset.sum_eq_single (⟨i, h.1⟩ : Fin n)]
    · by_cases hij : i = j
      · subst hij; simp [h]
      · have : (j : ℕ) ≠ (i : ℕ) := fun e => hij (Fin.ext e.symm)
        simp [hij, this]
    · intro b _ hb
      have : (i : ℕ) ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h, ite_self]
    refine Finset.sum_eq_zero fun p _ => ?_
    have : ¬ ((i : ℕ) = (p : ℕ) ∧ 0 < a i) := fun ⟨e, ha⟩ => h ⟨e ▸ p.isLt, ha⟩
    rw [if_neg this, zero_mul]

theorem halfSel_add (h2 : (2 : L) ≠ 0) (a : Fin n' → ℕ) (i j : Fin n') :
    halfSel (L := L) a i j + halfSel a j i = 1 := by
  unfold halfSel
  rcases eq_or_ne i j with rfl | hne
  · simp only [lt_irrefl, false_or, and_false, if_false, if_true]
    rw [← two_mul, mul_inv_cancel₀ h2]
  have hne' : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hne
  split_ifs <;> first | (exfalso; omega) | simp | rw [← two_mul, mul_inv_cancel₀ h2]

end GlobalTheory.Hk3.SquareDiag

namespace GlobalTheory.Hk3.SquareDiag


set_option maxHeartbeats 1000000 in
open GlobalTheory.Hk3 in
theorem square_diag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A B : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) → (∀ i j, B i j ∈ Formalism.UG.intL L) → A * B = 1 →
    (∀ i j, σ (A i j) = A j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ a : Fin n' → ℕ,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))) + σ (δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ n n' A B ψ hU hq hA hB hAB hherm hδ hψ hne a hC
  classical
  have hσσ := hU.1
  have hσv := hU.2.1
  have hσϖ := hU.2.2.1
  have hvϖ := hU.2.2.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have h20 : (2 : L) ≠ 0 := by intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖlt : Valued.v ϖ < 1 := by rw [hvϖ]; decide
  have hϖi : ϖ ∈ Formalism.UG.intL L := le_of_lt hϖlt
  have hδi : δ ∈ Formalism.UG.intL L := le_of_eq hδ.1
  have hσi : ∀ x ∈ Formalism.UG.intL L, σ x ∈ Formalism.UG.intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx
  have hσpow : ∀ k : ℕ, σ (ϖ⁻¹ ^ k) = ϖ⁻¹ ^ k := fun k => by rw [map_pow, map_inv₀, hσϖ]
  set D : Matrix (Fin n') (Fin n) L := Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDdef
  set E : Matrix (Fin n') (Fin n) L := selE a n with hEdef
  set Δ : Matrix (Fin n') (Fin n') L := diagonal (fun i : Fin n' => ϖ⁻¹ ^ a i) with hΔ
  have hDE : D = Δ * E := diag_sel ϖ a n
  have hEσ : E.map σ = E := by
    ext i p; simp only [E, selE, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp
  have hΔσ : Δ.map σ = Δ := by
    ext i j; simp only [Δ, Matrix.map_apply, Matrix.diagonal_apply]; split_ifs
    · exact hσpow _
    · exact map_zero σ
  have hDσ : D.map σ = D := by rw [hDE, Matrix.map_mul, hEσ, hΔσ]
  have hAm : A.map σ = Aᵀ := by ext i j; simp [hherm]
  have hAσ : (A.map σ)ᵀ = A := by rw [hAm, Matrix.transpose_transpose]
  have hBA : B * A = 1 := mul_eq_one_comm.mp hAB
  have hBσ : (B.map σ)ᵀ = B := by
    have h1 : (B.map σ)ᵀ * A = 1 := by
      have : ((A * B).map σ)ᵀ = ((1 : Matrix (Fin n) (Fin n) L).map σ)ᵀ := by rw [hAB]
      rwa [Matrix.map_mul, Matrix.transpose_mul, hAσ, Matrix.map_one _ (map_zero σ) (map_one σ),
        Matrix.transpose_one] at this
    calc (B.map σ)ᵀ = (B.map σ)ᵀ * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = B := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hEi : ∀ i p, E i p ∈ Formalism.UG.intL L := by
    intro i p; simp only [E, selE, Matrix.of_apply]; split_ifs
    · exact (Formalism.UG.intL L).one_mem
    · exact (Formalism.UG.intL L).zero_mem
  have hErow : ∀ i : Fin n', ¬ ((i : ℕ) < n ∧ 0 < a i) → ∀ p, E i p = 0 := by
    intro i h p; simp only [E, selE, Matrix.of_apply]
    rw [if_neg]; rintro ⟨e, ha⟩; exact h ⟨e ▸ p.isLt, ha⟩
  set A' : Matrix (Fin n') (Fin n') L := E * A * Eᵀ with hA'def
  have hA'i : ∀ i j, A' i j ∈ Formalism.UG.intL L := fun i j =>
    matMul_int (matMul_int hEi hA) (fun p k => hEi k p) i j
  have hA'σ : ∀ i j, σ (A' i j) = A' j i := by
    have hm : A'.map σ = A'ᵀ := by
      rw [hA'def, Matrix.map_mul, Matrix.map_mul, hEσ, hAm, Matrix.transpose_map, hEσ, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  set s : Fin n' → L := fun i => if (i : ℕ) < n ∧ 0 < a i then (1 : L) else 0 with hsdef
  have hEE : E * Eᵀ = diagonal s := selE_mul_transpose a n
  have hA's : ∀ i j, A' i j * s i = A' i j ∧ A' i j * s j = A' i j := by
    intro i j
    by_cases hi : (i : ℕ) < n ∧ 0 < a i
    · by_cases hj : (j : ℕ) < n ∧ 0 < a j
      · simp [s, hi, hj]
      · have : A' i j = 0 := by
          simp only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow j hj, mul_zero, Finset.sum_const_zero]
        simp [this]
    · have : A' i j = 0 := by
        simp only [A', Matrix.mul_apply, Matrix.transpose_apply, hErow i hi, zero_mul, Finset.sum_const_zero]
      simp [this]
  set G : Matrix (Fin n') (Fin n') L := D * A * (D.map σ)ᵀ with hGdef
  have hGΔ : G = Δ * A' * Δ := by
    rw [hGdef, hDσ, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, hA'def]
    simp only [Matrix.mul_assoc]
  have hGe : ∀ i j, G i j = ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j := by
    intro i j; rw [hGΔ, hΔ, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hGσ : ∀ i j, σ (G i j) = G j i := by
    intro i j; rw [hGe, hGe, map_mul, map_mul, hσpow, hσpow, hA'σ]; ring

  have hbound : ∀ i j, ϖ ^ (max (max (a i) (a j)) 1) * G j i ∈ Formalism.UG.intL L := by
    intro i j
    set m := max (max (a i) (a j)) 1 with hm
    have hmi : a i ≤ m := by omega
    have hmj : a j ≤ m := by omega
    have hm1 : 1 ≤ m := by omega
    have hsm : ∀ b' ∈ Formalism.UG.intL L, Valued.v (δ * (b' * ϖ ^ m)) < 1 ∧
        ∀ k ≤ m, δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k ∈ Formalism.UG.intL L := by
      intro b' hb'
      refine ⟨?_, fun k hk => ?_⟩
      · have e : δ * (b' * ϖ ^ m) = (δ * b' * ϖ ^ (m - 1)) * ϖ := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1, mul_assoc]
        have hx : Valued.v (δ * b' * ϖ ^ (m - 1)) ≤ 1 := mul_mem (mul_mem hδi hb') (pow_mem hϖi _)
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) hϖlt
      · have e : δ * (b' * ϖ ^ m) * ϖ⁻¹ ^ k = δ * b' * ϖ ^ (m - k) := by
          rw [← pow_sub_mul_pow ϖ hk, inv_pow]; field_simp
        rw [e]; exact mul_mem (mul_mem hδi hb') (pow_mem hϖi _)
    have hw : δ ^ 2 * ϖ ^ m * G j i ∈ Formalism.UG.intL L := by
      refine int_of_psi hU ψ hne _ (fun b hb => ?_)
      have hσb := hσi b hb
      set x := δ * (b * ϖ ^ m) with hx
      set y := δ * (σ b * ϖ ^ m) with hy
      have hσx : σ x = -y := by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2]; ring
      have hσy : σ y = -x := by rw [hx, hy, map_mul, map_mul, map_pow, hσϖ, hδ.2, hσσ]; ring
      set C : Matrix (Fin n') (Fin n') L := Matrix.single i j x + Matrix.single j i y with hCdef
      have hskew : ∀ k l, σ (C k l) = - C l k := by
        intro k l
        simp only [hCdef, Matrix.add_apply, Matrix.single_apply]
        have e1 : (i = l ∧ j = k) ↔ (j = k ∧ i = l) := and_comm
        have e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
        by_cases hP : i = k ∧ j = l <;> by_cases hQ : j = k ∧ i = l
        · rw [if_pos hP, if_pos hQ, if_pos (e1.2 hQ), if_pos (e2.2 hP), map_add (f := _), hσx, hσy]; ring
        · rw [if_pos hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_pos (e2.2 hP), map_add (f := _), hσx, map_zero]; ring
        · rw [if_neg hP, if_pos hQ, if_pos (e1.2 hQ), if_neg (fun h => hP (e2.1 h)), map_add (f := _), hσy, map_zero]; ring
        · rw [if_neg hP, if_neg hQ, if_neg (fun h => hQ (e1.1 h)), if_neg (fun h => hP (e2.1 h)), map_add (f := _), map_zero]; ring
      have hsmall : ∀ k l, Valued.v (C k l) < 1 := by
        intro k l
        simp only [hCdef, Matrix.add_apply, Matrix.single_apply]
        refine Valuation.map_add_lt _ ?_ ?_
        · split_ifs
          · exact (hsm b hb).1
          · rw [map_zero]; exact zero_lt_one
        · split_ifs
          · exact (hsm (σ b) hσb).1
          · rw [map_zero]; exact zero_lt_one
      have hsingle : ∀ (r s' : Fin n') (z : L), (∀ p, z * D s' p ∈ Formalism.UG.intL L) →
          ∀ k p, (Matrix.single r s' z * D) k p ∈ Formalism.UG.intL L := by
        intro r s' z hz k p
        by_cases h : k = r
        · subst h; rw [Matrix.single_mul_apply_same]; exact hz p
        · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ h]; exact (Formalism.UG.intL L).zero_mem
      have hDrow : ∀ (s' : Fin n') (b' : L), b' ∈ Formalism.UG.intL L → a s' ≤ m →
          ∀ p, δ * (b' * ϖ ^ m) * D s' p ∈ Formalism.UG.intL L := by
        intro s' b' hb' hs' p
        rw [hDdef, Matrix.of_apply]
        split_ifs
        · exact (hsm b' hb').2 _ hs'
        · rw [mul_zero]; exact (Formalism.UG.intL L).zero_mem
      have hint : ∀ k p, (C * D) k p ∈ Formalism.UG.intL L := by
        intro k p
        rw [hCdef, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hsingle i j x (hDrow j b hb hmj) k p) (hsingle j i y (hDrow i (σ b) hσb hmi) k p)
      have h := hC C hskew hsmall hint
      have htr : Matrix.trace (C * G) = x * G j i + y * G i j := by
        rw [hCdef, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, smul_eq_mul, smul_eq_mul]
      rw [htr] at h
      have key : (δ * (x * G j i + y * G i j) + σ (δ * (x * G j i + y * G i j))) / 2 =
          b * (δ ^ 2 * ϖ ^ m * G j i) + σ (b * (δ ^ 2 * ϖ ^ m * G j i)) := by
        rw [hx, hy]
        simp only [map_add (f := _), map_mul, map_pow, hσϖ, hδ.2, hσσ, hGσ]
        rw [div_eq_iff h20]; ring
      rw [← key]; exact h
    have e : Valued.v (δ ^ 2 * ϖ ^ m * G j i) = Valued.v (ϖ ^ m * G j i) := by
      rw [mul_assoc, map_mul, map_pow, hδ.1, one_pow, one_mul]
    rw [GlobalTheory.Hk3.mem_intL_iff, ← e]; exact hw
  set t : Fin n' → Fin n' → L := halfSel a with htdef
  have ht : ∀ i j, t i j + t j i = 1 := halfSel_add h20 a
  have h2i : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by rw [GlobalTheory.Hk3.mem_intL_iff, map_inv₀, h2, inv_one]
  have htσ : ∀ i j, σ (t i j) = t i j := by
    intro i j; simp only [htdef, halfSel]; split_ifs <;> simp [map_inv₀, map_ofNat]
  have hcore : ∀ i j, a i ≤ a j → ϖ⁻¹ ^ a i * A' i j ∈ Formalism.UG.intL L := by
    intro i j hle
    rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hA'i i j
    · have hmx : max (max (a j) (a i)) 1 = a j := by omega
      have := hbound j i
      rw [hmx, hGe i j] at this
      have e : ϖ ^ a j * (ϖ⁻¹ ^ a i * A' i j * ϖ⁻¹ ^ a j) = ϖ⁻¹ ^ a i * A' i j := by
        rw [inv_pow, inv_pow]; field_simp
      rwa [e] at this
  set W : Matrix (Fin n') (Fin n') L := Matrix.of fun i j => t i j * (ϖ⁻¹ ^ a i * A' i j) with hWdef
  have hWi : ∀ i j, W i j ∈ Formalism.UG.intL L := by
    intro i j
    simp only [hWdef, Matrix.of_apply, htdef, halfSel]
    split_ifs with h1 h3
    · exact mul_mem (Formalism.UG.intL L).one_mem (hcore i j (by rcases h1 with h | ⟨h, -⟩ <;> omega))
    · exact mul_mem h2i (hcore i j (le_of_eq (congrArg a (Fin.ext h3))))
    · rw [zero_mul]; exact (Formalism.UG.intL L).zero_mem
  set Z : Matrix (Fin n') (Fin n) L := W * E with hZdef
  set Zσ : Matrix (Fin n) (Fin n') L := (Z.map σ)ᵀ with hZσdef
  have hZi : ∀ i p, Z i p ∈ Formalism.UG.intL L := matMul_int hWi hEi
  have hZσi : ∀ p i, Zσ p i ∈ Formalism.UG.intL L := fun p i => hσi _ (hZi i p)
  have hDZ : D * Zσ = Δ * (diagonal s * (W.map σ)ᵀ) := by
    rw [hDE, hZσdef, hZdef, Matrix.map_mul, Matrix.transpose_mul, hEσ, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]
  have hZD : Z * Dᵀ = W * (diagonal s * Δ) := by
    rw [hZdef, hDE, Matrix.transpose_mul, hΔ, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEE]
  have hsplit : G = D * Zσ + Z * Dᵀ := by
    ext i j
    rw [hGe, Matrix.add_apply, hDZ, hZD, hΔ, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal,
      Matrix.mul_diagonal]
    simp only [Matrix.transpose_apply, Matrix.map_apply, hWdef, Matrix.of_apply, map_mul, htσ, hσpow, hA'σ]
    obtain ⟨e1, e2⟩ := hA's i j
    linear_combination (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t j i)) * e1 + (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * t i j)) * e2 +
      (-(ϖ⁻¹ ^ a i * ϖ⁻¹ ^ a j * A' i j)) * ht i j
  refine ⟨Z * B, fun i p => matMul_int hZi hB i p, ?_⟩
  have hlσ : ((D - Z * B).map σ)ᵀ = Dᵀ - B * Zσ := by
    rw [hZσdef, Matrix.map_sub _ (map_sub σ), hDσ, Matrix.transpose_sub, Matrix.map_mul, Matrix.transpose_mul, hBσ]
  have hM : (D - Z * B) * A * ((D - Z * B).map σ)ᵀ = Z * B * Zσ := by
    rw [hlσ, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have e1 : D * A * (B * Zσ) = D * Zσ := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAB, Matrix.one_mul]
    have e2 : Z * B * A * Dᵀ = Z * Dᵀ := by rw [Matrix.mul_assoc Z, hBA, Matrix.mul_one]
    have e3 : Z * B * A * (B * Zσ) = Z * B * Zσ := by
      calc Z * B * A * (B * Zσ) = Z * (B * A) * (B * Zσ) := by rw [Matrix.mul_assoc Z B A]
        _ = Z * (B * Zσ) := by rw [hBA, Matrix.mul_one]
        _ = Z * B * Zσ := (Matrix.mul_assoc _ _ _).symm
    have e4 : D * A * Dᵀ = G := by rw [hGdef, hDσ]
    rw [e1, e2, e3, e4, hsplit]; abel
  intro i j
  rw [hM]
  exact matMul_int (matMul_int hZi hB) hZσi i j

end GlobalTheory.Hk3.SquareDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompleteSquareDiagonalNegPowUniformizerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completeSquare_diagonalNegPowUniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A B : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) → (∀ i j, B i j ∈ Formalism.UG.intL L) → A * B = 1 →
    (∀ i j, σ (A i j) = A j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ a : Fin n' → ℕ,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))) + σ (δ * Matrix.trace (C * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))).map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l) * A * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l).map σ)) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.SquareDiag.square_diag | exact GlobalTheory.Hk3.SquareDiag.square_diag | (intros; apply GlobalTheory.Hk3.SquareDiag.square_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionIntegralBasisChange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionIntegralBasisChange
namespace GlobalTheory


open Matrix in
theorem phaseCondition_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ)
    (P : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) →
    (∀ i j, P i j ∈ Formalism.UG.intL L) → (∀ i j, Q' i j ∈ Formalism.UG.intL L) → Q * Q' = 1 →
    ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (P * x * Q)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))) + σ (δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))))) / 2) = 1) := by
  intro L _ _ σ δ n n' A ψ P Q Q' hσσ hσv hP hQ' hQQ' x hx C' hskew hv hint
  have hmap1 : (1 : Matrix (Fin n) (Fin n) L).map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  have hyQ' : (P * x * Q) * Q' = P * x := by rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
  have e1 : ∀ Z : Matrix (Fin n) (Fin n') L, Q * (Q' * Z) = Z := by
    intro Z; rw [← Matrix.mul_assoc, hQQ', Matrix.one_mul]
  have e2 : ∀ Z : Matrix (Fin n) (Fin n') L, (Q'.map σ)ᵀ * ((Q.map σ)ᵀ * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', hmap1, Matrix.transpose_one,
      Matrix.one_mul]
  have intMul : ∀ {a b c : ℕ} (M : Matrix (Fin a) (Fin b) L) (N : Matrix (Fin b) (Fin c) L),
      (∀ i j, M i j ∈ Formalism.UG.intL L) → (∀ i j, N i j ∈ Formalism.UG.intL L) → ∀ i j, (M * N) i j ∈ Formalism.UG.intL L := by
    intro a b c M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)
  have hPσ : ∀ i j, (P.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
    intro i j
    show Valued.v (σ (P j i)) ≤ 1
    rw [hσv]; exact hP j i
  have htr : Matrix.trace ((P.map σ)ᵀ * C' * P * (x * A * (x.map σ)ᵀ)) =
      Matrix.trace (C' * ((P * x * Q) * (Q' * A * (Q'.map σ)ᵀ) * ((P * x * Q).map σ)ᵀ)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, e1, e2]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hCx : (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * C' * P * x := by
    calc (P.map σ)ᵀ * (C' * (P * x * Q)) * Q' = (P.map σ)ᵀ * (C' * ((P * x * Q) * Q')) := by
          simp only [Matrix.mul_assoc]
      _ = (P.map σ)ᵀ * (C' * (P * x)) := by rw [hyQ']
      _ = _ := by simp only [Matrix.mul_assoc]
  have := hx ((P.map σ)ᵀ * C' * P) ?_ ?_ ?_
  · rw [htr] at this; exact this
  · intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσσ, hskew,
      Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · intro i j
    have hlt : ∀ (a b : L), Valued.v a ≤ 1 → Valued.v b < 1 → Valued.v (a * b) < 1 := by
      intro a b ha hb
      rw [map_mul]
      calc Valued.v a * Valued.v b ≤ 1 * Valued.v b := mul_le_mul' ha le_rfl
        _ = Valued.v b := one_mul _
        _ < 1 := hb
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [mul_comm]
    refine hlt _ _ (hP k j) ?_
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
    exact hlt _ _ (hPσ i l) (hv l k)
  · intro i j
    rw [← hCx]
    exact intMul _ _ (intMul _ _ hPσ hint) hQ' i j

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionIntegralBasisChangeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phaseCondition_integral_basisChange : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ)
    (P : Matrix (Fin n') (Fin n') L) (Q Q' : Matrix (Fin n) (Fin n) L),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) →
    (∀ i j, P i j ∈ Formalism.UG.intL L) → (∀ i j, Q' i j ∈ Formalism.UG.intL L) → Q * Q' = 1 →
    ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (P * x * Q)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))) + σ (δ * Matrix.trace (C * ((P * x * Q) * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((P * x * Q)).map σ))))) / 2) = 1) := by
  first | exact @GlobalTheory.phaseCondition_basisChange | exact GlobalTheory.phaseCondition_basisChange | (intros; apply GlobalTheory.phaseCondition_basisChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionSubIntegralMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionSubIntegralMatrix
noncomputable section

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} (P : Matrix (Fin a) (Fin b) L) (Q : Matrix (Fin b) (Fin c) L)
    (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) (hQ : ∀ i j, Q i j ∈ Formalism.UG.intL L) :
    ∀ i j, (P * Q) i j ∈ Formalism.UG.intL L := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hQ k j)

theorem trace_int {a : ℕ} (P : Matrix (Fin a) (Fin a) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    P.trace ∈ Formalism.UG.intL L :=
  Subring.sum_mem _ fun i _ => hP i i

theorem conjT_int {a b : ℕ} (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (P : Matrix (Fin a) (Fin b) L) (hP : ∀ i j, P i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (P.map σ)) i j ∈ Formalism.UG.intL L := by
  intro i j
  show Valued.v (σ (P j i)) ≤ 1
  rw [hσ]; exact hP j i

theorem phase_shift (σ : L →+* L) (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (h2 : Valued.v (2 : L) = 1) (ψ : AddChar L ℂ) (hψ : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (u u' : L) (hd : u - u' ∈ Formalism.UG.intL L) (h : ψ ((u + σ u) / 2) = 1) :
    ψ ((u' + σ u') / 2) = 1 := by
  have he : ((u - u') + σ (u - u')) / 2 ∈ Formalism.UG.intL L := by
    show Valued.v (((u - u') + σ (u - u')) / 2) ≤ 1
    rw [map_div₀, h2, div_one]
    refine (Formalism.UG.intL L).add_mem hd ?_
    show Valued.v (σ (u - u')) ≤ 1
    rw [hσ]; exact hd
  have hs : σ (((u - u') + σ (u - u')) / 2) = ((u - u') + σ (u - u')) / 2 := by
    rw [map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
  have heq : (u' + σ u') / 2 = (u + σ u) / 2 - ((u - u') + σ (u - u')) / 2 := by
    rw [map_sub]; ring
  rw [heq, AddChar.map_sub_eq_div, h, hψ _ he hs, div_one]

end GlobalTheory.Hk3.ShiftPhase

namespace GlobalTheory.Hk3.ShiftPhase

open Matrix

theorem conjT_mul_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ} (σ : L →+* L)
    (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (C : Matrix (Fin a) (Fin a) L) (hC : ∀ i j, σ (C i j) = - C j i)
    (x : Matrix (Fin a) (Fin b) L) (hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L) :
    ∀ i j, (Matrix.transpose (x.map σ) * C) i j ∈ Formalism.UG.intL L := by
  intro j k
  have h : (Matrix.transpose (x.map σ) * C) j k = - σ ((C * x) k j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hC,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  refine (Formalism.UG.intL L).neg_mem ?_
  show Valued.v (σ _) ≤ 1
  rw [hσ]; exact hCx k j

theorem shift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) →
    Valued.v δ = 1 → σ δ = -δ → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    ∀ x l : Matrix (Fin n') (Fin n) L, (∀ i j, l i j ∈ Formalism.UG.intL L) →
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (x - l)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))) + σ (δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))))) / 2) = 1) := by
  intro L _ _ ϖ σ q δ n n' A ψ hU hq hA hδ _ hψ x l hl hx C hC hCv hCxl
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, -⟩ := hU
  have hCi : ∀ i j, C i j ∈ Formalism.UG.intL L := fun i j => (hCv i j).le
  have hCl : ∀ i j, (C * l) i j ∈ Formalism.UG.intL L := mul_int C l hCi hl
  have hCx : ∀ i j, (C * x) i j ∈ Formalism.UG.intL L := by
    have e : C * x = C * (x - l) + C * l := by rw [Matrix.mul_sub]; abel
    intro i j
    rw [e, Matrix.add_apply]
    exact (Formalism.UG.intL L).add_mem (hCxl i j) (hCl i j)
  have hsub : Matrix.transpose ((x - l).map σ) = Matrix.transpose (x.map σ) - Matrix.transpose (l.map σ) := by
    ext i j; simp [map_sub]
  set X := Matrix.transpose (x.map σ) with hX
  set Y := Matrix.transpose (l.map σ) with hY
  have hYi : ∀ i j, Y i j ∈ Formalism.UG.intL L := conjT_int σ hσv l hl
  have hXC : ∀ i j, (X * C) i j ∈ Formalism.UG.intL L := conjT_mul_int σ hσσ hσv C hC x hCx
  have hd : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y)))
      = Matrix.trace (C * x * A * Y) + Matrix.trace (X * C * l * A) - Matrix.trace (C * l * A * Y) := by
    have h3 : Matrix.trace (C * (l * A * X)) = Matrix.trace (X * C * l * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
    rw [h3]
    simp only [Matrix.mul_assoc]
    abel
  have hdi : Matrix.trace (C * (x * A * X)) - Matrix.trace (C * ((x - l) * A * (X - Y))) ∈ Formalism.UG.intL L := by
    rw [hd]
    refine (Formalism.UG.intL L).sub_mem ((Formalism.UG.intL L).add_mem ?_ ?_) ?_
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCx hA) hYi)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hXC hl) hA)
    · exact trace_int _ (mul_int _ _ (mul_int _ _ hCl hA) hYi)
  rw [hsub]
  refine phase_shift σ hσσ hσv h2 ψ hψ (δ * Matrix.trace (C * (x * A * X))) _ ?_ (hx C hC hCv hCx)
  rw [← mul_sub]
  refine (Formalism.UG.intL L).mul_mem ?_ hdi
  show Valued.v δ ≤ 1
  rw [hδ]

end GlobalTheory.Hk3.ShiftPhase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionSubIntegralMatrixStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phaseCondition_sub_integral_matrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (A : Matrix (Fin n) (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → (∀ i j, A i j ∈ Formalism.UG.intL L) →
    Valued.v δ = 1 → σ δ = -δ → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    ∀ x l : Matrix (Fin n') (Fin n) L, (∀ i j, l i j ∈ Formalism.UG.intL L) →
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1) → (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * (x - l)) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))) + σ (δ * Matrix.trace (C * ((x - l) * A * Matrix.transpose (((x - l)).map σ))))) / 2) = 1) := by
  first | exact @GlobalTheory.Hk3.ShiftPhase.shift | exact GlobalTheory.Hk3.ShiftPhase.shift | (intros; apply GlobalTheory.Hk3.ShiftPhase.shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralGramOfPhaseConditions
noncomputable section
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Square

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem star_int {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) :
    (Matrix.transpose (A.map σ)) i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  change Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact h

theorem gen {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L}
    {n n' : ℕ} {A B : Matrix (Fin n) (Fin n) L} {ψ : AddChar L ℂ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (hAB : A * B = 1) (hAh : ∀ i j, σ (A i j) = A j i)
    (hδ : Valued.v δ = 1 ∧ σ δ = -δ) (hpi : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (x : Matrix (Fin n') (Fin n) L)
    (hx : (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1)) :
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * A * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.T.smith_normal_form_integral_matrix L ϖ hU.2.2.2.1 n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hA'i : ∀ i j, (Q' * A * Matrix.transpose (Q'.map σ)) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hQ' hA) (star_int hv hQ')
  have hB'i : ∀ i j, (Matrix.transpose (Q.map σ) * B * Q) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int (star_int hv hQ) hB) hQ
  have h1 : Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ) = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hA'B' : (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q) = 1 := by
    calc (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q)
        = Q' * A * (Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ)) * B * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Matrix.mul_assoc Q' A B, hAB, Matrix.mul_one, hQ'Q]
  have hAm : A.map σ = Matrix.transpose A := by ext i j; simp [hAh]
  have hQm : (Q'.map σ).map σ = Q' := by ext i j; simp [hσ]
  have hA'h : ∀ i j, σ ((Q' * A * Matrix.transpose (Q'.map σ)) i j) = (Q' * A * Matrix.transpose (Q'.map σ)) j i := by
    have hm : (Q' * A * Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose (Q' * A * Matrix.transpose (Q'.map σ)) := by
      have hQt : (Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose Q' := by ext i j; simp [hσ]
      rw [Matrix.map_mul, Matrix.map_mul, hAm, hQt]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  have hy := GlobalTheory.T.phaseCondition_integral_basisChange L σ δ n n' A ψ P Q Q' hσ hv hP hQ' hQQ' x hx
  have hD := GlobalTheory.T.phaseCondition_sub_integral_matrix L ϖ σ q δ n n' _ ψ hU hq hA'i hδ.1 hδ.2 hpi (P * x * Q) _ hE hy
  rw [sub_sub_cancel] at hD
  obtain ⟨l', hl', hG⟩ := GlobalTheory.T.completeSquare_diagonalNegPowUniformizer L ϖ σ q δ n n' _ _ ψ hU hq hA'i hB'i hA'B' hA'h hδ hpi hne a hD
  refine ⟨P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q', ?_, ?_⟩
  · intro i j
    exact mul_int (mul_int hP' (fun i j => add_mem (hE i j) (hl' i j))) hQ' i j
  · have hxe : x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q' := by
      have hx0 : x = P' * (P * x * Q) * Q' := by
        simp only [Matrix.mul_assoc, hQQ', Matrix.mul_one]
        rw [← Matrix.mul_assoc, hP'P, Matrix.one_mul]
      rw [show x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * (P * x * Q) * Q' - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' from by rw [← hx0]]
      have hab : P * x * Q - ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') = (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l' := by abel
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, hab]
    rw [hxe]
    have hg : (P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q') * A * Matrix.transpose ((P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q').map σ) =
        P' * (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l').map σ)) * Matrix.transpose (P'.map σ) := by
      simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hg]
    exact mul_int (mul_int hP' hG) (star_int hv hP')

end GlobalTheory.Hk3.HoweDuality.Square

theorem GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q δ n n' JS ψ hU hq hJS hJh hδ hpi hne x hx
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have glint_entry : ∀ {g : GL (Fin n) L}, g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j,
      (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro g hg i j
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
    exact (k.val i j).2
  have hJi : (JS⁻¹ : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := Subgroup.inv_mem _ hJS
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  have hSm : (JS : Matrix (Fin n) (Fin n) L).map σ = Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) := by
    ext i j; simp [hJh]
  have hPJ : P * (JS : Matrix (Fin n) (Fin n) L) = 1 := by rw [hPdef]; exact JS.inv_mul
  have hJP : (JS : Matrix (Fin n) (Fin n) L) * P = 1 := by rw [hPdef]; exact JS.mul_inv
  have e1 : P.map σ * Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← hSm, ← Matrix.map_mul, hPJ]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have e2 : (JS : Matrix (Fin n) (Fin n) L) * Matrix.transpose (P.map σ) = 1 := by
    have := congrArg Matrix.transpose e1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have e3 : Matrix.transpose (P.map σ) = P := by
    calc Matrix.transpose (P.map σ) = (P * (JS : Matrix (Fin n) (Fin n) L)) * Matrix.transpose (P.map σ) := by
          rw [hPJ, Matrix.one_mul]
      _ = P := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  have hPh : ∀ i j, σ (P i j) = P j i := by
    intro i j
    have := congrFun (congrFun e3 j) i
    simpa using this
  exact GlobalTheory.Hk3.HoweDuality.Square.gen hU hq (glint_entry hJi) (glint_entry hJS) hPJ hPh hδ hpi hne x hx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralGramOfPhaseConditionsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_gram_of_phase_conditions : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases | exact GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases | (intros; apply GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixed
noncomputable section
namespace GlobalTheory.Hk3.HoweDuality

theorem exists_int_gram_of_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan x hw
  obtain ⟨hne, hfx⟩ := GlobalTheory.T.heisenbergTranslate_fixed_integralUnitary L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs x hw
  have Hph : ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1 := by
    intro h hh hint
    have e := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hs _ hint, add_sub_cancel, hfx h hh hint] at e
    have e2 : (ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) - 1) • ρ x s = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.1 e2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hne
  exact GlobalTheory.T.exists_integral_gram_of_phase_conditions L ϖ σ q δ n n' JS ψ hP.unr hP.odd hP.intS hP.hermS hP.delta hP.psi_int hP.psi_ne x
    (GlobalTheory.T.cayleyTransform_trivial_phase_skewHermitian L ϖ σ q δ n n' JS JT ψ hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT hP.delta hP.psi_int x Hph)
end GlobalTheory.Hk3.HoweDuality
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_gram_of_fixed_alt : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_fixed | exact GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_fixed | (intros; apply GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_fixed <;> assumption)
end
