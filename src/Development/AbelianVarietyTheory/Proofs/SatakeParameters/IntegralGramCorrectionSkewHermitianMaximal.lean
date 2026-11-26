module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximal
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ringHomConjTranspose_mul_rev (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem sigmaConjTranspose_integral_gramSeparation (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  show Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact hA j i

theorem val_div_pow_le_one {ϖ x y : L} {k m : ℕ} (hϖ : Valued.v ϖ ≤ 1) (hy : Valued.v y = Valued.v ϖ) (hϖ0 : ϖ ≠ 0)
    (hx : Valued.v x ≤ Valued.v ϖ ^ m) (hkm : k ≤ m) : x * (y ^ k)⁻¹ ∈ Formalism.UG.intL L := by
  show Valued.v (x * (y ^ k)⁻¹) ≤ 1
  have h0 : Valued.v ϖ ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hϖ0)
  have h1 : Valued.v x ≤ Valued.v ϖ ^ k := hx.trans (pow_le_pow_right_of_le_one' hϖ hkm)
  rw [map_mul, map_inv₀, map_pow, hy]
  calc Valued.v x * (Valued.v ϖ ^ k)⁻¹ ≤ Valued.v ϖ ^ k * (Valued.v ϖ ^ k)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ h0

end GlobalTheory.Hk3.GramSep

namespace GlobalTheory.Hk3.GramSep

theorem eint : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  intro L _ _ ϖ σ hvϖ hv n r JS a M e Γ hJS hSD he hM haM hΓ
  classical
  have hΓv : ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j) := hΓ.2
  have hϖlt : Valued.v ϖ < 1 := by
    rw [hvϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]; decide
  have hϖ1 : Valued.v ϖ ≤ 1 := hϖlt.le
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hσϖ0 : σ ϖ ≠ 0 := (map_ne_zero σ).mpr hϖ0
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJ
  set D : Matrix (Fin r) (Fin r) L := diagonal fun k => ϖ ^ e k with hD
  set Di : Matrix (Fin r) (Fin r) L := diagonal fun k => (ϖ ^ e k)⁻¹ with hDi
  set Ds : Matrix (Fin r) (Fin r) L := diagonal fun k => σ ϖ ^ e k with hDs
  set Dsi : Matrix (Fin r) (Fin r) L := diagonal fun k => (σ ϖ ^ e k)⁻¹ with hDsi
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
  have hDsiDs : Dsi * Ds = 1 := by
    rw [hDs, hDsi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact inv_mul_cancel₀ (pow_ne_zero _ hσϖ0)
  have hcTD : Formalism.UG.cT σ D = Ds := by
    rw [hD, hDs]; unfold Formalism.UG.cT
    rw [diagonal_map (map_zero σ), diagonal_transpose]
    congr 1; funext k; simp
  have haia : ai * A = 1 := by rw [hai, hA]; exact a.inv_mul
  have hcTa : Formalism.UG.cT σ ai * Formalism.UG.cT σ A = 1 := by
    have haai : A * ai = 1 := by rw [hai, hA]; exact a.mul_inv
    rw [← ringHomConjTranspose_mul_rev, haai]
    unfold Formalism.UG.cT; rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

  set P : Matrix (Fin n) (Fin r) L := ai * M * D with hP
  have hPi : ∀ i k, P i k ∈ Formalism.UG.intL L := by
    intro i k; rw [hP, hD, mul_diagonal]; exact haM i k
  set G1 : Matrix (Fin r) (Fin r) L := Di * Γ with hG1
  have hG1i : ∀ k j, G1 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG1, hDi, diagonal_mul, mul_comm]
    exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) (le_max_left _ _)
  set G2 : Matrix (Fin r) (Fin r) L := Γ * Dsi with hG2
  have hG2i : ∀ k j, G2 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG2, hDsi, mul_diagonal]
    exact val_div_pow_le_one hϖ1 (hv ϖ) hϖ0 (hΓv k j) (le_max_right _ _)
  have hcTM := sigmaConjTranspose_integral_gramSeparation σ hv hM
  have hSDa : ∀ i j, (Formalism.UG.cT σ A * J * A) i j ∈ Formalism.UG.intL L := hSD.1
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have e1 : ai * (M * Γ * Formalism.UG.cT σ M * J) = P * G1 * (Formalism.UG.cT σ M * J) := by
      rw [hP, hG1]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]
    rw [e1]
    exact matMul_int (matMul_int hPi hG1i) (matMul_int hcTM hJS) i j
  · have e2 : M * Γ * Formalism.UG.cT σ M * J * A = M * G2 * (Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A)) := by
      rw [hP, hG2, ringHomConjTranspose_mul_rev, ringHomConjTranspose_mul_rev, hcTD]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Dsi Ds, hDsiDs, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.cT σ ai) (Formalism.UG.cT σ A), hcTa,
        Matrix.one_mul]
    rw [e2]
    exact matMul_int (matMul_int hM hG2i) (matMul_int (sigmaConjTranspose_integral_gramSeparation σ hv hPi) hSDa) i j
  · set G3 : Matrix (Fin r) (Fin r) L := Matrix.of fun k j => Γ k j * (ϖ ^ 1)⁻¹ with hG3
    have hG3i : ∀ k j, G3 k j ∈ Formalism.UG.intL L := by
      intro k j
      exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) ((he k).trans (le_max_left _ _))
    have hΓ3 : Γ = ϖ • G3 := by
      ext k j; rw [hG3]; simp only [Matrix.smul_apply, of_apply, smul_eq_mul, pow_one]
      field_simp
    have e3 : M * Γ * Formalism.UG.cT σ M * J = ϖ • (M * G3 * Formalism.UG.cT σ M * J) := by
      rw [hΓ3, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    rw [e3, Matrix.smul_apply, smul_eq_mul, map_mul]
    have hint : Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ 1 :=
      matMul_int (matMul_int (matMul_int hM hG3i) hcTM) hJS i j
    calc Valued.v ϖ * Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hϖlt

end GlobalTheory.Hk3.GramSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGramCorrectionSkewHermitianMaximalStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_gramCorrection_skewHermitian_maximal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  first | exact @GlobalTheory.Hk3.GramSep.eint | exact GlobalTheory.Hk3.GramSep.eint | (intros; apply GlobalTheory.Hk3.GramSep.eint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegers
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.VacPhase

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_mul' (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' (σ : L →+* L) {a : ℕ} : Formalism.UG.cT σ (1 : Matrix (Fin a) (Fin a) L) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem cT_sub' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A - B) = Formalism.UG.cT σ A - Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  change Valued.v (σ (A j i)) ≤ 1
  rw [hσ]; exact h

theorem locH_sub_trace_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  intro L _ _ σ δ hσ hδ n n' JS a k JT E y hJ hP hT hSD hE hAiE hEA hk hKi hyA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJdef
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  set T : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hTdef
  set K : Matrix (Fin n) (Fin n) L := (k : Matrix (Fin n) (Fin n) L) with hKdef
  set Ki : Matrix (Fin n) (Fin n) L := ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKidef
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hAdef
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAidef
  have hPJ : P * J = 1 := by rw [hPdef, hJdef]; exact JS.inv_mul
  have hJP : J * P = 1 := by rw [hPdef, hJdef]; exact JS.mul_inv
  have hKKi : K * Ki = 1 := by rw [hKdef, hKidef]; exact k.mul_inv
  have hAAi : A * Ai = 1 := by rw [hAdef, hAidef]; exact a.mul_inv
  set R : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ Ki * J with hRdef
  set Z : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ y * T * y with hZdef

  have h1 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) = δ * Matrix.trace ((R - 1) * Z) := by
    unfold GlobalTheory.Hk3.locH
    have : ((y * (Ki - 1)).map σ)ᵀ = Formalism.UG.cT σ (Ki - 1) * Formalism.UG.cT σ y := cT_mul' σ y (Ki - 1)
    rw [← hPdef, ← hTdef, this, cT_sub', cT_one']
    congr 1
    rw [hRdef, hZdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J P, hJP, Matrix.one_mul]
  have h2 : δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) = δ * Matrix.trace (E * Z) := by
    rw [hZdef]; simp only [Matrix.mul_assoc]

  have hR : R * (1 - E) = 1 := by
    have hcK : Formalism.UG.cT σ K * J = J * (1 - E) := by
      rw [hk, cT_add', cT_one', Matrix.add_mul, hE, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    rw [hRdef, Matrix.mul_assoc, ← hcK, ← Matrix.mul_assoc, Matrix.mul_assoc P, ← cT_mul', hKKi, cT_one', Matrix.mul_one, hPJ]
  have hR' : (1 - E) * R = 1 := mul_eq_one_comm.mp hR
  have hRE : R - 1 - E = E * R * E := by
    have e1 : R - 1 = R * E := by
      have := hR; rw [Matrix.mul_sub, Matrix.mul_one] at this
      rw [← this]; abel
    have e2 : R - 1 = E * R := by
      have := hR'; rw [Matrix.sub_mul, Matrix.one_mul] at this
      rw [← this]; abel
    calc R - 1 - E = (R - 1) * E := by rw [Matrix.sub_mul, Matrix.one_mul, e1]
      _ = E * R * E := by rw [e2]
  have h3 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) - δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) =
      δ * Matrix.trace (R * (E * Z * E)) := by
    rw [h1, h2, ← mul_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, hRE]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm E]
    simp only [Matrix.mul_assoc]
  rw [h3]

  have hRint : ∀ i j, R i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hP (cT_int σ hσ hKi)) hJ
  have hy' : Formalism.UG.cT σ y = Formalism.UG.cT σ Ai * Formalism.UG.cT σ (y * A) := by
    rw [← cT_mul', Matrix.mul_assoc, hAAi, Matrix.mul_one]
  have hW : E * Z * E = ((E * A) * (Ai * P * Formalism.UG.cT σ Ai) * Formalism.UG.cT σ (y * A)) * T * ((y * A) * (Ai * E)) := by
    rw [hZdef, hy']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A Ai, hAAi, Matrix.one_mul, ← Matrix.mul_assoc A Ai E, hAAi, Matrix.one_mul]
  have hWint : ∀ i j, (E * Z * E) i j ∈ Formalism.UG.intL L := by
    rw [hW]
    exact mul_int (mul_int (mul_int (mul_int hEA hSD.2) (cT_int σ hσ hyA)) hT) (mul_int hyA hAiE)
  refine Subring.mul_mem _ hδ ?_
  exact Subring.sum_mem _ fun i _ => mul_int hRint hWint i i

end GlobalTheory.Hk3.VacPhase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegersStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumPhase_sub_trace_mem_integers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem | exact GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem | (intros; apply GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmithNormalFormGeneratorsExactOrders
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmithNormalFormGeneratorsExactOrders
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SnfGen

open GlobalTheory.Hk3.Smith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} {x : Fin b → L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hx : ∀ j, x j ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ x) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hx k)

theorem exp_of_gt {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {d : L} (hd : 1 < Valued.v d) :
    1 ≤ (-Formalism.UG.ordL d).toNat ∧ Valued.v (d * ϖ ^ (-Formalism.UG.ordL d).toNat) = 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hv := v_eq_ord hd0
  rw [hv] at hd
  have hpos : 0 < -Formalism.UG.ordL d := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt] at hd; exact hd
  refine ⟨by omega, ?_⟩
  have h2 := v_inv_pow hϖ (-Formalism.UG.ordL d).toNat
  rw [Int.toNat_of_nonneg hpos.le, ← hv] at h2
  rw [map_mul, ← h2, ← map_mul, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, map_one]

theorem main_gen (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (n : ℕ) (b : Matrix (Fin n) (Fin n) L) :
    ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (b * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧
    (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (b *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
    (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (b *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  classical
  obtain ⟨P, Q, ⟨hPi, P', hP'i, hPP'⟩, ⟨hQi, Q', hQ'i, hQQ'⟩, hD⟩ := exists_diag n n b
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  obtain ⟨D, hDdef⟩ : ∃ D, D = P * b * Q := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDd : ∀ i j, i ≠ j → D i j = 0 := fun i j h => hD i j (fun h' => h (Fin.ext h'))
  have hbQ : b * Q = P' * D := by
    rw [hDdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul]
  obtain ⟨r, σ, hσinj, hσ⟩ : ∃ (r : ℕ) (σ : Fin r → Fin n), Function.Injective σ ∧
      ∀ j, (1 < Valued.v (D j j) ↔ ∃ k, σ k = j) := by
    let S := {i : Fin n // 1 < Valued.v (D i i)}
    refine ⟨Fintype.card S, fun k => ((Fintype.equivFin S).symm k).1,
      fun k l h => (Fintype.equivFin S).symm.injective (Subtype.ext h), fun j => ⟨fun h => ?_, ?_⟩⟩
    · exact ⟨Fintype.equivFin S ⟨j, h⟩, by simp⟩
    · rintro ⟨k, rfl⟩; exact ((Fintype.equivFin S).symm k).2
  have hσsel : ∀ k, 1 < Valued.v (D (σ k) (σ k)) := fun k => (hσ _).2 ⟨k, rfl⟩
  have hsum : ∀ g : Fin n → L, ∑ k, g (σ k) = ∑ j, if 1 < Valued.v (D j j) then g j else 0 := by
    intro g
    rw [← Finset.sum_filter, ← Finset.sum_image (hσinj.injOn)]
    congr 1; ext j; simp [hσ]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin r) L, ∀ i k, M i k = Q i (σ k) :=
    ⟨Matrix.of fun i k => Q i (σ k), fun _ _ => rfl⟩
  have hbM : ∀ i k, (b * M) i k = P' i (σ k) * D (σ k) (σ k) := by
    intro i k
    have : (b * M) i k = (b * Q) i (σ k) := by simp only [Matrix.mul_apply, hM]
    rw [this, hbQ, Matrix.mul_apply, Finset.sum_eq_single (σ k)]
    · intro l _ hl; rw [hDd l (σ k) hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPbM : ∀ j k, (P * b * M) j k = D j (σ k) := by
    intro j k; simp only [hDdef, Matrix.mul_apply, hM]
  refine ⟨r, M, fun k => (-Formalism.UG.ordL (D (σ k) (σ k))).toNat, fun k => (exp_of_gt hϖ (hσsel k)).1,
    fun i k => by rw [hM]; exact hQi _ _, fun i k => ?_, fun m hm => ?_, fun β hβ hbβ k => ?_⟩
  · rw [hbM, mem_intL, mul_assoc, map_mul, (exp_of_gt hϖ (hσsel k)).2, mul_one]
    exact mem_intL.1 (hP'i _ _)
  · obtain ⟨c, hc⟩ : ∃ c, c = Q' *ᵥ m := ⟨_, rfl⟩
    have hci : ∀ j, c j ∈ Formalism.UG.intL L := by rw [hc]; exact mulVec_int hQ'i hm
    have hmc : m = Q *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, hQQ', Matrix.one_mulVec]
    obtain ⟨cs, hcs⟩ : ∃ cs : Fin n → L, ∀ j, cs j = if 1 < Valued.v (D j j) then c j else 0 :=
      ⟨fun j => if 1 < Valued.v (D j j) then c j else 0, fun _ => rfl⟩
    refine ⟨fun k => c (σ k), fun k => hci _, ?_⟩
    have hMα : M *ᵥ (fun k => c (σ k)) = Q *ᵥ cs := by
      funext i
      simp only [Matrix.mulVec, dotProduct, hM, hcs]
      exact (hsum (fun j => Q i j * c j)).trans (by simp only [mul_ite, mul_zero])
    rw [hmc, hMα, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hbQ, ← Matrix.mulVec_mulVec]
    refine mulVec_int hP'i (fun j => ?_)
    have hDv : (D *ᵥ (c - cs)) j = D j j * (c j - cs j) := by
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      rw [Finset.sum_eq_single j]
      · intro l _ hl; rw [hDd j l (Ne.symm hl), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hDv, hcs]
    split_ifs with hj
    · rw [sub_self, mul_zero]; exact Subring.zero_mem _
    · rw [sub_zero]; exact Subring.mul_mem _ (mem_intL.2 (not_lt.1 hj)) (hci j)
  · have h1 := mulVec_int hPi hbβ (σ k)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
    have h2 : ((P * b * M) *ᵥ β) (σ k) = D (σ k) (σ k) * β k := by
      simp only [Matrix.mulVec, dotProduct, hPbM]
      rw [Finset.sum_eq_single k]
      · intro l _ hl; rw [hDd _ _ (fun h => hl (hσinj h).symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2, mem_intL] at h1
    have hex := (exp_of_gt hϖ (hσsel k)).2
    beta_reduce
    calc Valued.v (β k) = Valued.v (β k) * Valued.v (D (σ k) (σ k) * ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat) := by
          rw [hex, mul_one]
      _ = Valued.v (D (σ k) (σ k) * β k) * Valued.v ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat := by
          rw [map_mul, map_mul, map_pow]; ac_rfl
      _ ≤ Valued.v ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat := mul_le_of_le_one_left' h1

end GlobalTheory.Hk3.SnfGen

theorem GlobalTheory.Hk3.snf_generators : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
  ∀ (n : ℕ) (a : GL (Fin n) L), ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧ (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧ (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  intro L _ _ ϖ hϖ n a
  exact GlobalTheory.Hk3.SnfGen.main_gen ϖ hϖ n _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmithNormalFormGeneratorsExactOrdersStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smithNormalForm_generators_exactOrders : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
  ∀ (n : ℕ) (a : GL (Fin n) L), ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧ (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧ (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  first | exact @GlobalTheory.Hk3.snf_generators | exact GlobalTheory.Hk3.snf_generators | (intros; apply GlobalTheory.Hk3.snf_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassEqOfSigmaHermitianFormBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassEqOfSigmaHermitianFormBounds
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramConv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_add_left' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u u' w : Fin n → L) :
    Formalism.UG.hform σ J (u + u') w = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u' w := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w w' : Fin n → L) :
    Formalism.UG.hform σ J u (w + w') = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u w' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u (c • w) = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left' (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L)
    (u w : Fin n → L) : Formalism.UG.hform σ J (σ c • u) w = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hσ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_sub_mat (σ : L →+* L) {n : ℕ} (J J' : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ (J - J') u w = Formalism.UG.hform σ J u w - Formalism.UG.hform σ J' u w := by
  simp only [Formalism.UG.hform, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec_mulVec (σ : L →+* L) {n r : ℕ} (J : Matrix (Fin n) (Fin n) L) (B : Matrix (Fin n) (Fin r) L)
    (α β : Fin r → L) :
    Formalism.UG.hform σ J (B *ᵥ α) (B *ᵥ β) = Formalism.UG.hform σ (Formalism.UG.cT σ B * J * B) α β := by
  have hs : (fun i => σ ((B *ᵥ α) i)) = (fun k => σ (α k)) ᵥ* Formalism.UG.cT σ B := by
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, map_sum, map_mul, Matrix.transpose_apply,
      Matrix.map_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hform_eq_dot, hform_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem mulVec_int' {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ j, w j ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hw j)

theorem hform_int' (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {J : Matrix (Fin n) (Fin n) L}
    (hJ : ∀ i j, J i j ∈ Formalism.UG.intL L) {u w : Fin n → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : Formalism.UG.hform σ J u w ∈ Formalism.UG.intL L := by
  have hsu : ∀ i, σ (u i) ∈ Formalism.UG.intL L := fun i => by
    show Valued.v (σ (u i)) ≤ 1
    rw [hv]; exact hu i
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (hsu i) (hJ i j)) (hw j)

theorem gramEq_of_gram_bounds : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ϖ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (x y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) → (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) →
  (∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.GramEq σ JT x y := by
  intro L _ _ ϖ σ hσ hv hϖ n n' r JT a x y M e hJ hJh hiff hxa hya hM hAM hdec hbd hG
  intro m m' hm hm' c hc hxm hxm'
  have toV : ∀ t : L, t ∈ Formalism.UG.intL L → Valued.v t ≤ 1 := fun t h => h
  have ofV : ∀ t : L, Valued.v t ≤ 1 → t ∈ Formalism.UG.intL L := fun t h => h
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAi
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hAAi : A * Ai = 1 := by rw [hA, hAi]; exact a.mul_inv
  have hAiA : Ai * A = 1 := by rw [hA, hAi]; exact a.inv_mul

  have key : ∀ μ : Fin n → L, (∀ i, μ i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • μ)) i ∈ Formalism.UG.intL L) →
      ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧ (∀ i, (Ai *ᵥ (μ - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
        (∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L) ∧ ∀ k, Valued.v (c * α k) ≤ Valued.v ϖ ^ e k := by
    intro μ hμ hxμ
    obtain ⟨α, hα, hν⟩ := hdec μ hμ
    have hcμ : ∀ i, (c • μ) i ∈ Formalism.UG.intL L := fun i => Subring.mul_mem _ hc (hμ i)
    obtain ⟨u, hu, hcu⟩ := (hiff (c • μ) hcμ).2 hxμ
    have heq : Ai *ᵥ (M *ᵥ (c • α)) = u - c • (Ai *ᵥ (μ - M *ᵥ α)) := by
      have h1 : M *ᵥ (c • α) = c • μ - c • (μ - M *ᵥ α) := by
        rw [Matrix.mulVec_smul, smul_sub, sub_sub_cancel]
      rw [h1, Matrix.mulVec_sub, hcu, Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec, Matrix.mulVec_smul]
    have hint : ∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L := by
      intro i
      rw [heq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact Subring.sub_mem _ (hu i) (Subring.mul_mem _ hc (hν i))
    have hcα : ∀ k, (c • α) k ∈ Formalism.UG.intL L := fun k => Subring.mul_mem _ hc (hα k)
    refine ⟨α, hα, hν, hint, fun k => ?_⟩
    have := hbd (c • α) hcα hint k
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  obtain ⟨α, hα, hν, hcαA, hbdα⟩ := key m hm hxm
  obtain ⟨α', hα', hν', hcα'A, hbdα'⟩ := key m' hm' hxm'

  have hσcα : ∀ i, (Ai *ᵥ (M *ᵥ (σ c • α))) i ∈ Formalism.UG.intL L := by
    intro i
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine Subring.sum_mem _ fun k _ => ofV _ ?_
    calc Valued.v ((Ai * M) i k * (σ c * α k)) = Valued.v ((Ai * M) i k) * Valued.v (c * α k) := by
          rw [map_mul, map_mul, map_mul, hv]
      _ ≤ Valued.v ((Ai * M) i k) * Valued.v ϖ ^ e k := mul_le_mul' le_rfl (hbdα k)
      _ = Valued.v ((Ai * M) i k * ϖ ^ e k) := by rw [map_mul, map_pow]
      _ ≤ 1 := toV _ (hAM i k)

  have hz : ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * A) i j ∈ Formalism.UG.intL L) →
      c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α'))
        ∈ Formalism.UG.intL L := by
    intro z hzA
    have hzw : ∀ w : Fin n → L, (∀ i, (Ai *ᵥ w) i ∈ Formalism.UG.intL L) → ∀ i, (z *ᵥ w) i ∈ Formalism.UG.intL L := by
      intro w hw
      have : z *ᵥ w = (z * A) *ᵥ (Ai *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hAAi, Matrix.mul_one]
      rw [this]; exact mulVec_int' hzA hw
    have e1 : z *ᵥ m = z *ᵥ (M *ᵥ α) + z *ᵥ (m - M *ᵥ α) := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have e2 : z *ᵥ m' = z *ᵥ (M *ᵥ α') + z *ᵥ (m' - M *ᵥ α') := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have s1 : σ c • (z *ᵥ (M *ᵥ α)) = z *ᵥ (M *ᵥ (σ c • α)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have s2 : c • (z *ᵥ (M *ᵥ α')) = z *ᵥ (M *ᵥ (c • α')) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hexp : c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α')) =
        Formalism.UG.hform σ J (σ c • (z *ᵥ (M *ᵥ α))) (z *ᵥ (m' - M *ᵥ α')) +
        Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (c • (z *ᵥ (M *ᵥ α'))) +
        c * Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (z *ᵥ (m' - M *ᵥ α')) := by
      rw [hform_smul_left' σ hσ, hform_smul_right', e1, e2, hform_add_left', hform_add_right', hform_add_right']
      ring
    rw [hexp, s1, s2]
    have hJi : ∀ i j, J i j ∈ Formalism.UG.intL L := hJ
    refine Subring.add_mem _ (Subring.add_mem _ ?_ ?_) (Subring.mul_mem _ hc ?_)
    · exact hform_int' σ hv hJi (hzw _ hσcα) (hzw _ hν')
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hcα'A)
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hν')

  have hmain : c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
      Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) ∈ Formalism.UG.intL L := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hform_mulVec_mulVec, hform_mulVec_mulVec, ← hform_sub_mat, ← hform_smul_right']
    set D := Formalism.UG.cT σ (y * M) * J * (y * M) - Formalism.UG.cT σ (x * M) * J * (x * M) with hD
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ofV _ ?_
    have h1 : Valued.v (α i) * Valued.v (c * α' j) ≤ Valued.v ϖ ^ max (e i) (e j) := by
      rcases le_total (e i) (e j) with h | h
      · rw [max_eq_right h]
        calc Valued.v (α i) * Valued.v (c * α' j) ≤ 1 * Valued.v ϖ ^ e j := mul_le_mul' (toV _ (hα i)) (hbdα' j)
          _ = _ := one_mul _
      · rw [max_eq_left h]
        calc Valued.v (α i) * Valued.v (c * α' j) = Valued.v (c * α i) * Valued.v (α' j) := by
              rw [map_mul, map_mul, mul_left_comm, ← mul_assoc]
          _ ≤ Valued.v ϖ ^ e i * 1 := mul_le_mul' (hbdα i) (toV _ (hα' j))
          _ = _ := mul_one _
    calc Valued.v (σ (α i) * D i j * (c • α') j) = (Valued.v (α i) * Valued.v (c * α' j)) * Valued.v (D i j) := by
          rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, hv, mul_right_comm]
      _ ≤ Valued.v ϖ ^ max (e i) (e j) * Valued.v (D i j) := mul_le_mul' h1 le_rfl
      _ = Valued.v (D i j * ϖ ^ max (e i) (e j)) := by rw [map_mul, map_pow, mul_comm]
      _ ≤ 1 := toV _ (hG i j)
  have hfin : c * (Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m')) =
      (c * Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - c * Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α'))) -
      (c * Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m') - c * Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) +
      c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
        Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) := by ring
  rw [hfin]
  exact Subring.add_mem _ (Subring.sub_mem _ (hz y hya) (hz x hxa)) hmain

end GlobalTheory.Hk3.GramConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassEqOfSigmaHermitianFormBoundsStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClassEq_of_sigmaHermitianForm_bounds : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ϖ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (x y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) → (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) →
  (∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.GramEq σ JT x y := by
  first | exact @GlobalTheory.Hk3.GramConv.gramEq_of_gram_bounds | exact GlobalTheory.Hk3.GramConv.gramEq_of_gram_bounds | (intros; apply GlobalTheory.Hk3.GramConv.gramEq_of_gram_bounds <;> assumption)
end
end
