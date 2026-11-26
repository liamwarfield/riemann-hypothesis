module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnil
open Matrix Polynomial

namespace GlobalTheory.UnitDiscAlg

section Residue
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]

def unitBallMaxIdeal : Ideal (unitBallSubring E) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal E

theorem mem_unitBallMaxIdeal {t : unitBallSubring E} :
    t ∈ unitBallMaxIdeal E ↔ ‖(t : E)‖ < 1 := Iff.rfl

theorem unitBallMaxIdeal_isMaximal : (unitBallMaxIdeal E).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    have h' : ‖((1 : E))‖ < 1 := h
    simp at h'
  · intro J x _ hx hxJ
    have hx1 : ¬ ‖(x : E)‖ < 1 := hx
    have hx2 : ‖(x : E)‖ ≤ 1 := x.2
    have hn : ‖(x : E)‖ = 1 := le_antisymm hx2 (not_lt.mp hx1)
    have hx0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv : ‖(x : E)⁻¹‖ ≤ 1 := by rw [norm_inv, hn, inv_one]
    have hmem := J.mul_mem_left ⟨(x : E)⁻¹, hinv⟩ hxJ
    convert hmem using 1
    apply Subtype.ext
    exact (inv_mul_cancel₀ hx0).symm

end Residue

theorem norm_lt_one_of_pow_of_commute (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hb : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (w : Matrix (Fin n) (Fin n) E) (hwN : w * N = N * w) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (M : ℕ) (hM : ∀ i j, ‖(w ^ M) i j‖ < 1) : ∀ i j, ‖w i j‖ < 1 := by
  intro i j
  have hM0 : M ≠ 0 := by
    rintro rfl
    have := hM i i
    simp at this
  obtain ⟨u, v, hu, hv, huv⟩ := hb
  haveI := unitBallMaxIdeal_isMaximal E
  letI : Field (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.field _
  let O := unitBallSubring E
  let π : O →+* (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.mk _
  let N' : Matrix (Fin n) (Fin n) O := fun a b => ⟨N a b, hN a b⟩
  let w' : Matrix (Fin n) (Fin n) O := fun a b => ⟨w a b, hw a b⟩
  have hNm : O.subtype.mapMatrix N' = N := by ext; rfl
  have hwm : O.subtype.mapMatrix w' = w := by ext; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) := by
    intro a b h
    ext x y
    exact congrFun (congrFun h x) y
  have hwN' : w' * N' = N' * w' := hinj (by rw [map_mul, map_mul, hNm, hwm, hwN])
  have hu' : (u.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hu m
  have hv' : (v.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hv m
  have hNmap : N'.map O.subtype = N := by ext; rfl
  have hbO : u.toSubring O hu' * N'.charpoly + v.toSubring O hv' * derivative N'.charpoly = 1 := by
    apply Polynomial.map_injective O.subtype Subtype.val_injective
    rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_toSubring, Polynomial.map_toSubring, ← Matrix.charpoly_map, hNmap,
      Polynomial.map_one]
    exact huv
  set N'' := N'.map π with hN''
  set w'' := w'.map π with hw''
  have hbk : (u.toSubring O hu').map π * N''.charpoly
      + (v.toSubring O hv').map π * derivative N''.charpoly = 1 := by
    have := congrArg (Polynomial.map π) hbO
    simpa [hN'', Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.derivative_map,
      Matrix.charpoly_map] using this
  have hwk : w'' * N'' = N'' * w'' := by
    rw [hN'', hw'', ← Matrix.map_mul, ← Matrix.map_mul, hwN']
  have hs : N''.charpoly.Separable := ⟨_, _, hbk⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RegSS.cyclicField (unitBallSubring E ⧸ unitBallMaxIdeal E) (Fin n) N'' hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra _ (Fin n) N'' x hx).2.2
  have hmem : w'' ∈ Algebra.adjoin (unitBallSubring E ⧸ unitBallMaxIdeal E) {N''} :=
    GlobalTheory.RegSS.mem_genAlg_of_commute hbij hwk
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hpowm : O.subtype.mapMatrix (w' ^ M) = w ^ M := by rw [map_pow, hwm]
  have hpow : w'' ^ M = 0 := by
    rw [hw'', ← Matrix.map_pow]
    ext a b
    rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_unitBallMaxIdeal]
    have := congrFun (congrFun hpowm a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    show ‖(((w' ^ M) a b : O) : E)‖ < 1
    rw [show (((w' ^ M) a b : O) : E) = (w ^ M) a b from this]
    exact hM a b
  have hfM : aeval N'' (f ^ M) = 0 := by
    rw [map_pow]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [hf, hpow]
  have hdvd := minpoly.dvd _ N'' hfM
  have hsq : Squarefree (minpoly (unitBallSubring E ⧸ unitBallMaxIdeal E) N'') :=
    hs.squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly N'')
  have hdvd' := (Squarefree.dvd_pow_iff_dvd hsq hM0).mp hdvd
  have hf0 : aeval N'' f = 0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd' (minpoly.aeval _ _)
  have hw0 : w'' = 0 := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [← hf, hf0]
  have hij := congrFun (congrFun hw0 i) j
  rw [hw'', Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_unitBallMaxIdeal] at hij
  exact hij

end GlobalTheory.UnitDiscAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnilStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_integral_matrix_topnil : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → ∀ w : Matrix (Fin n) (Fin n) E, w * N = N * w → (∀ i j, ‖w i j‖ ≤ 1) → ∀ M : ℕ, (∀ i j, ‖(w ^ M) i j‖ < 1) → ∀ i j, ‖w i j‖ < 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | exact GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute | (intros; apply GlobalTheory.UnitDiscAlg.norm_lt_one_of_pow_of_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixDecompose
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg.Red

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

def Sm (s : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, ‖s i j‖ < 1

theorem sm_add {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : Sm y) : Sm (x + y) := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hx i j) (hy i j))

theorem sm_neg {x : Matrix (Fin n) (Fin n) E} (hx : Sm x) : Sm (-x) := by
  intro i j; rw [Matrix.neg_apply, norm_neg]; exact hx i j

theorem sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E) := by intro i j; simp

theorem norm_sum_lt_one' {s : Finset (Fin n)} {f : Fin n → E} (h : ∀ k, ‖f k‖ < 1) :
    ‖∑ k ∈ s, f k‖ < 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (h a) ih)

theorem sm_mul_left {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : Sm y) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hx i k)) (hy k j))

theorem sm_mul_right {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hy k j)) (hx i k))

theorem sm_eq_smul {N s : Matrix (Fin n) (Fin n) E} {ϖ : E} (h0 : 0 < ‖ϖ‖)
    (hu : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) (hs : Sm s) (hc : s * N = N * s) :
    ∃ a : Matrix (Fin n) (Fin n) E, a * N = N * a ∧ (∀ i j, ‖a i j‖ ≤ 1) ∧ s = ϖ • a := by
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp h0
  refine ⟨ϖ⁻¹ • s, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ h0, mul_one]
    exact hu _ (hs i j)
  · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]

end GlobalTheory.UnitDiscAlg.Red

namespace GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem exists_pow_close [LocallyCompactSpace E] (y : Matrix (Fin n) (Fin n) E)
    (hy : ∀ i j, ‖y i j‖ ≤ 1) : ∃ a b : ℕ, a < b ∧ Sm (y ^ b - y ^ a) := by
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  let f : ℕ → Fin n → Fin n → E := fun k i j => (y ^ k) i j
  have hs : IsCompact (Metric.closedBall (0 : Fin n → Fin n → E) 1) := isCompact_closedBall _ _
  have hf : ∀ k, f k ∈ Metric.closedBall (0 : Fin n → Fin n → E) 1 := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    exact integ_pow hy k i j
  obtain ⟨x, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hf
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq 1 one_pos
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  intro i j
  have h1 := hN (N + 1) (Nat.le_succ N) N le_rfl
  have h2 : dist (f (φ (N + 1)) i j) (f (φ N) i j) < 1 :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ j).trans (dist_le_pi_dist _ _ i)) h1
  rw [dist_eq_norm] at h2
  simpa [f, Matrix.sub_apply] using h2

end GlobalTheory.UnitDiscAlg.Red

namespace GlobalTheory.UnitDiscAlg.Red

theorem main : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  intro E _ _ _ n N ϖ hN hB h0 _ hu y hyN hy
  have hred := GlobalTheory.T.commuting_integral_matrix_topnil E n N hN hB
  obtain ⟨a, b, hab, hsm⟩ := exists_pow_close y hy
  have hcy : Commute y N := hyN
  have step : ∀ k, a ≤ k → Sm (y ^ (k + (b - a)) - y ^ k) := by
    intro k hk
    have e1 : y ^ (k + (b - a)) - y ^ k = y ^ (k - a) * (y ^ b - y ^ a) := by
      rw [mul_sub, ← pow_add, ← pow_add]
      congr 2 <;> omega
    rw [e1]
    exact sm_mul_left (integ_pow hy _) hsm
  have per : ∀ k, a ≤ k → ∀ j, Sm (y ^ (k + j * (b - a)) - y ^ k) := by
    intro k hk j
    induction j with
    | zero => simpa using (sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E))
    | succ j ih =>
      have e2 : y ^ (k + (j + 1) * (b - a)) - y ^ k
          = (y ^ (k + j * (b - a) + (b - a)) - y ^ (k + j * (b - a)))
            + (y ^ (k + j * (b - a)) - y ^ k) := by
        rw [show k + (j + 1) * (b - a) = k + j * (b - a) + (b - a) by ring]
        abel
      rw [e2]
      exact sm_add (step _ (by omega)) ih
  set M := (b - a) * (a + 1) with hMdef
  have hpos : 1 ≤ b - a := by omega
  have hMa : a + 1 ≤ M := by
    rw [hMdef]; nlinarith
  have hidem : Sm (y ^ M * y ^ M - y ^ M) := by
    rw [← pow_add]
    have := per M (by omega) (a + 1)
    rwa [show M + (a + 1) * (b - a) = M + M by rw [hMdef]; ring] at this
  set x := y ^ M with hx
  have hxi : ∀ i j, ‖x i j‖ ≤ 1 := integ_pow hy M
  have hxN : Commute x N := hcy.pow_left M
  have hyx : Commute y x := (Commute.refl y).pow_right M
  have h1i : ∀ i j, ‖((1 : Matrix (Fin n) (Fin n) E) - x) i j‖ ≤ 1 := integ_sub integ_one hxi

  have hwM : Sm ((y * (1 - x)) ^ M) := by
    have hc : Commute y (1 - x) := (Commute.one_right y).sub_right hyx
    rw [hc.mul_pow, ← hx]
    obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    rw [hm, pow_succ', ← mul_assoc]
    apply sm_mul_right _ (integ_pow h1i m)
    have : x * (1 - x) = -(x * x - x) := by rw [mul_sub, mul_one]; abel
    rw [this]
    exact sm_neg hidem
  have hwN : Commute (y * (1 - x)) N := hcy.mul_left ((Commute.one_left N).sub_left hxN)
  have hw : Sm (y * (1 - x)) :=
    hred (y * (1 - x)) hwN.eq (integ_mul hy h1i) M hwM
  have hc1 : Commute (x * x - x) N := (hxN.mul_left hxN).sub_left hxN
  obtain ⟨a₁, ha₁N, ha₁i, ha₁⟩ := sm_eq_smul h0 hu hidem hc1.eq
  obtain ⟨a₂, ha₂N, ha₂i, ha₂⟩ := sm_eq_smul h0 hu hw hwN.eq
  have hyz : y * y ^ (M - 1) = x := by
    rw [hx, ← pow_succ']; congr 1; omega
  refine ⟨x, y ^ (M - 1), a₁, a₂, a₁, ⟨hxN.eq, (hcy.pow_left _).eq, ha₁N, ha₂N, ha₁N⟩,
    fun i j => ⟨hxi i j, integ_pow hy _ i j, ha₁i i j, ha₂i i j, ha₁i i j⟩, ha₁, ha₂, ?_⟩
  rw [hyz, ha₁]

end GlobalTheory.UnitDiscAlg.Red
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixDecomposeStatement
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_integral_matrix_decompose : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  first | exact @GlobalTheory.UnitDiscAlg.Red.main | exact GlobalTheory.UnitDiscAlg.Red.main | (intros; apply GlobalTheory.UnitDiscAlg.Red.main <;> assumption)
end
