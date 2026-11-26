module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExists
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExists
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertDual

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem antiJ_iff (i j : Fin N) : i.val + j.val + 1 = N ↔ j = i.rev := by
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.isLt
  have := j.isLt
  constructor <;> intro h <;> omega

theorem antiJ_mulVec (b : Fin N → L) (k : Fin N) : (antiJ L N *ᵥ b) k = b k.rev := by
  simp [Matrix.mulVec, dotProduct, antiJ, antiJ_iff]

theorem antiJ_mul_self : antiJ L N * antiJ L N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, antiJ, antiJ_iff, boole_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem isInt_antiJ : IsInt (antiJ L N) := by
  intro i j
  simp only [antiJ]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem cT_add (σ : L →+* L) (A B : Matrix (Fin N) (Fin N) L) : cT σ (A + B) = cT σ A + cT σ B := by
  ext i j
  simp [cT]

theorem isInt_cT {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) :
    IsInt (cT σ M) := by
  intro i j
  have h : M j i ∈ intL L := hM j i
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [hmem] at h ⊢
  rw [hσ]
  exact h

theorem int_mulVec {M : Matrix (Fin N) (Fin N) L} (hM : IsInt M) {w : Fin N → L} (hw : ∀ i, w i ∈ intL L) (i : Fin N) :
    (M *ᵥ w) i ∈ intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem (fun j _ => mul_mem (hM i j) (hw j))

theorem iff_of_inverse {D E Q R Dg : Matrix (Fin N) (Fin N) L} (hED : E * D = 1) (hQ : IsInt (Q * E))
    (hR : IsInt (R * E)) (hDg : IsInt Dg) (hD : IsInt D) (e : D = Dg * R + D * Q) (B : Fin N → L) :
    (∀ i, (D *ᵥ B) i ∈ intL L) ↔ (∀ i, (Q *ᵥ B) i ∈ intL L) ∧ ∀ i, (R *ᵥ B) i ∈ intL L := by
  constructor
  · intro h
    have key : ∀ P : Matrix (Fin N) (Fin N) L, IsInt (P * E) → ∀ i, (P *ᵥ B) i ∈ intL L := by
      intro P hP i
      have hPB : P *ᵥ B = (P * E) *ᵥ (D *ᵥ B) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hED, Matrix.mul_one]
      rw [hPB]
      exact int_mulVec hP h i
    exact ⟨key Q hQ, key R hR⟩
  · rintro ⟨hq, hr⟩ i
    have hDB : D *ᵥ B = Dg *ᵥ (R *ᵥ B) + D *ᵥ (Q *ᵥ B) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← e]
    rw [hDB, Pi.add_apply]
    exact add_mem (int_mulVec hDg hr i) (int_mulVec hD hq i)

theorem dual : Dual := by
  unfold GlobalTheory.InertZeta.Dual
  intro L _ _ ϖ σ q N hU g U V C hF r b t hr
  obtain ⟨hσσ, hσv, -, -, -, -, -⟩ := hU
  obtain ⟨hUi, hVi, hCi, hAi, hUVC⟩ := hF
  have hg : cT σ (mat g) * antiJ L N * mat g = antiJ L N := g.2
  have hJJ : antiJ L N * antiJ L N = 1 := antiJ_mul_self
  have hJi : IsInt (antiJ L N) := isInt_antiJ
  have hmem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Valuation.mem_integer_iff _ _
  have hsub : ∀ {X Y : Matrix (Fin N) (Fin N) L}, IsInt X → IsInt Y → IsInt (X - Y) :=
    fun hX hY i j => sub_mem (hX i j) (hY i j)
  have hcTmul : ∀ X Y : Matrix (Fin N) (Fin N) L, cT σ (X * Y) = cT σ Y * cT σ X := by
    intro X Y
    simp [cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcTone : cT σ (1 : Matrix (Fin N) (Fin N) L) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT]
    · simp [cT, Matrix.one_apply, h, Ne.symm h]
  have hGJ : mat g * antiJ L N * cT σ (mat g) = antiJ L N := by
    have h1 : (antiJ L N * cT σ (mat g) * antiJ L N) * mat g = 1 := by
      rw [show antiJ L N * cT σ (mat g) * antiJ L N * mat g
          = antiJ L N * (cT σ (mat g) * antiJ L N * mat g) by simp only [Matrix.mul_assoc], hg, hJJ]
    have h2 := mul_eq_one_comm.mp h1
    calc mat g * antiJ L N * cT σ (mat g)
        = mat g * (antiJ L N * cT σ (mat g) * antiJ L N) * antiJ L N := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = antiJ L N := by rw [h2, Matrix.one_mul]
  have hCUV : C * (U + V * mat g) = 1 := mul_eq_one_comm.mp hUVC
  have hCUV' : C * U + C * V * mat g = 1 := by
    rw [Matrix.mul_assoc C V, ← Matrix.mul_add]
    exact hCUV
  have hED : (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N) = 1 := by
    calc (antiJ L N * cT σ (U + V * mat g)) * (cT σ C * antiJ L N)
        = antiJ L N * cT σ (C * (U + V * mat g)) * antiJ L N := by
          rw [hcTmul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCUV, hcTone, Matrix.mul_one, hJJ]
  have hD : IsInt (cT σ C * antiJ L N) := (isInt_cT hσv hCi).mul hJi
  have hDg : IsInt (cT σ (mat g * C) * antiJ L N) := (isInt_cT hσv hAi).mul hJi
  have he : cT σ C * antiJ L N
      = cT σ (mat g * C) * antiJ L N * (mat g * C * U) + cT σ C * antiJ L N * (C * V * mat g) := by
    have h1 : cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U) = cT σ C * antiJ L N * (C * U) := by
      calc cT σ C * cT σ (mat g) * antiJ L N * (mat g * C * U)
          = cT σ C * (cT σ (mat g) * antiJ L N * mat g) * (C * U) := by simp only [Matrix.mul_assoc]
        _ = cT σ C * antiJ L N * (C * U) := by rw [hg]
    rw [hcTmul, h1, ← Matrix.mul_add, hCUV', Matrix.mul_one]
  have hcTU : IsInt (cT σ U) := isInt_cT hσv hUi
  have hcTV : IsInt (cT σ V) := isInt_cT hσv hVi
  have hQE : IsInt (C * V * mat g * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCVG : C * V * mat g = 1 - C * U := eq_sub_of_add_eq' hCUV'
    have h2 : C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V)) = C * V * (antiJ L N * cT σ V) := by
      calc C * V * mat g * (antiJ L N * (cT σ (mat g) * cT σ V))
          = C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h2, hCVG, Matrix.sub_mul, Matrix.one_mul]
    exact (hsub (hJi.mul hcTU) ((hCi.mul hUi).mul (hJi.mul hcTU))).add ((hCi.mul hVi).mul (hJi.mul hcTV))
  have hRE : IsInt (mat g * C * U * (antiJ L N * cT σ (U + V * mat g))) := by
    have hCU : C * U = 1 - C * V * mat g := eq_sub_of_add_eq hCUV'
    have hA : mat g * (antiJ L N * cT σ (mat g)) * cT σ V = antiJ L N * cT σ V := by
      rw [← Matrix.mul_assoc (mat g) (antiJ L N), hGJ]
    have hB : mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
        = mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * (C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V
          = mat g * C * V * (mat g * antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * C * V * (antiJ L N * cT σ V) := by rw [hGJ]; simp only [Matrix.mul_assoc]
    have h3 : mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
        = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
      calc mat g * C * U * (antiJ L N * (cT σ (mat g) * cT σ V))
          = mat g * (C * U) * (antiJ L N * cT σ (mat g)) * cT σ V := by simp only [Matrix.mul_assoc]
        _ = mat g * (1 - C * V * mat g) * (antiJ L N * cT σ (mat g)) * cT σ V := by rw [hCU]
        _ = antiJ L N * cT σ V - mat g * C * V * (antiJ L N * cT σ V) := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.sub_mul, hA, hB]
    rw [cT_add, hcTmul, Matrix.mul_add (antiJ L N), Matrix.mul_add, h3]
    exact ((hAi.mul hUi).mul (hJi.mul hcTU)).add (hsub (hJi.mul hcTV) ((hAi.mul hVi).mul (hJi.mul hcTV)))
  have hJb : antiJ L N *ᵥ b = fun k => b k.rev := funext (antiJ_mulVec b)
  have hσvec : ∀ j, σ (vecMul r C j) = -((cT σ C * antiJ L N) *ᵥ b) j := by
    intro j
    rw [← Matrix.mulVec_mulVec, hJb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply,
      map_sum, map_mul, hr, map_neg, hσσ, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hL : ∀ j, (t * vecMul r C j ∈ intL L ↔ t * ((cT σ C * antiJ L N) *ᵥ b) j ∈ intL L) := by
    intro j
    rw [hmem, hmem, Valuation.map_mul, Valuation.map_mul, ← hσv (vecMul r C j), hσvec j, Valuation.map_neg]
  have key := iff_of_inverse (D := cT σ C * antiJ L N) (E := antiJ L N * cT σ (U + V * mat g))
    (Q := C * V * mat g) (R := mat g * C * U) (Dg := cT σ (mat g * C) * antiJ L N)
    hED hQE hRE hDg hD he (t • b)
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at key
  rw [forall_congr' hL]
  exact key

end GlobalTheory.CompanionTheory.InertDual

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.DualPairingExistsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_exists : Dual := by
  first | exact @GlobalTheory.CompanionTheory.InertDual.dual | exact GlobalTheory.CompanionTheory.InertDual.dual | (intros; apply GlobalTheory.CompanionTheory.InertDual.dual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl

namespace GlobalTheory.CompanionTheory.InertDoubling

theorem ring_gram {R : Type} [Ring R] (J A B U V a b u v S s : R) (hJ : J * J = 1) (h1 : U * A + V * B = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * (U * J * u - V * J * v) * J + J * S + s * J := by
  have e : (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * U * (J * J) * J * u * J + J * U * (J * J) * A * S + s * a * (J * J) * u * J + s * (a * J * A) * S
      - J * V * (J * J) * J * v * J + J * V * (J * J) * B * S + s * b * (J * J) * v * J - s * (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : J * U * 1 * J * u * J + J * U * 1 * A * S + s * a * 1 * u * J + s * (b * J * B) * S
      - J * V * 1 * J * v * J + J * V * 1 * B * S + s * b * 1 * v * J - s * (b * J * B) * S =
      J * (U * J * u - V * J * v) * J + J * (U * A + V * B) * S + s * (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h1, h2]
  noncomm_ring

theorem ring_pair {R : Type} [Ring R] (J A B U V a b u v S : R) (hJ : J * J = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) = J := by
  have e : a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) =
      (a * (J * J) * u + b * (J * J) * v) * J + (a * J * A) * S - (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : (a * 1 * u + b * 1 * v) * J + (b * J * B) * S - (b * J * B) * S = (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h2, one_mul]

section Cong

variable {L : Type} [Field L] {σ : L →+* L} {m p : Type}

theorem cT_add' (M N : Matrix m p L) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem cT_sub' (M N : Matrix m p L) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem cT_neg' (M : Matrix m p L) : cT σ (-M) = -cT σ M := by
  ext i j; simp [cT]

theorem cT_smul' (c : L) (M : Matrix m p L) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

theorem cT_cT' (h : ∀ x, σ (σ x) = x) (M : Matrix m p L) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, h]

theorem cT_fromBlocks {m₁ m₂ p₁ p₂ : Type} (A : Matrix m₁ p₁ L) (B : Matrix m₁ p₂ L) (C : Matrix m₂ p₁ L)
    (D : Matrix m₂ p₂ L) : cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext (i | i) (j | j) <;> simp [cT]

theorem cT_submatrix {ι : Type} (e : m ≃ ι) (M : Matrix m m L) :
    cT σ (M.submatrix e.symm e.symm) = (cT σ M).submatrix e.symm e.symm := by
  ext i j; simp [cT]

end Cong

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isInt_fromBlocks {m₁ m₂ p₁ p₂ : Type} {A : Matrix m₁ p₁ L} {B : Matrix m₁ p₂ L} {C : Matrix m₂ p₁ L}
    {D : Matrix m₂ p₂ L} (hA : IsInt A) (hB : IsInt B) (hC : IsInt C) (hD : IsInt D) : IsInt (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem isInt_neg' {m p : Type} {A : Matrix m p L} (h : IsInt A) : IsInt (-A) := fun i j => neg_mem (h i j)

theorem isInt_sub' {m p : Type} {A B : Matrix m p L} (h : IsInt A) (h' : IsInt B) : IsInt (A - B) :=
  fun i j => sub_mem (h i j) (h' i j)

theorem isInt_smul' {m p : Type} {A : Matrix m p L} {c : L} (hc : c ∈ intL L) (h : IsInt A) : IsInt (c • A) :=
  fun i j => mul_mem hc (h i j)

theorem isInt_cT' {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {m p : Type} {A : Matrix m p L} (h : IsInt A) :
    IsInt (cT σ A) := fun i j => by
  have := h j i
  rw [GlobalTheory.UnitarySwap.mem_int] at this ⊢
  simpa [cT, hσ] using this

theorem isInt_antiJ (n : ℕ) : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end Int

theorem cT_antiJ {L : Type} [Field L] (σ : L →+* L) (n : ℕ) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, antiJ, transpose_apply, map_apply]
  by_cases h : i.val + j.val + 1 = n
  · have : j.val + i.val + 1 = n := by omega
    simp [h, this]
  · have : ¬ (j.val + i.val + 1 = n) := by omega
    simp [h, this]

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem exists_block (hσσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {A B U V : Matrix (Fin n) (Fin n) L} (hA : IsInt A) (hB : IsInt B) (hU : IsInt U) (hV : IsInt V)
    (hAB : cT σ A * antiJ L n * A = cT σ B * antiJ L n * B) (hUV : U * A + V * B = 1) :
    ∃ k₀ k₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt k₀ ∧ IsInt k₁ ∧ k₁ * k₀ = 1 ∧
      cT σ k₀ * fromBlocks (antiJ L n) 0 0 (-antiJ L n) * k₀ = fromBlocks (antiJ L n) 0 0 (-antiJ L n) ∧
      k₀.toBlocks₁₁ + k₀.toBlocks₁₂ = A ∧ k₀.toBlocks₂₁ + k₀.toBlocks₂₂ = B := by
  obtain ⟨J, hJdef⟩ : ∃ J, J = antiJ L n := ⟨_, rfl⟩
  rw [← hJdef] at hAB ⊢
  have hJ : J * J = 1 := hJdef ▸ GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJc : cT σ J = J := hJdef ▸ cT_antiJ σ n
  have hJi : IsInt J := hJdef ▸ isInt_antiJ n
  have hτ' : σ τ ∈ intL L := by rw [GlobalTheory.UnitarySwap.mem_int, hσv]; exact hτ
  obtain ⟨R, hR⟩ : ∃ R, R = U * J * cT σ U - V * J * cT σ V := ⟨_, rfl⟩
  have hRc : cT σ R = R := by
    rw [hR]; simp only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have hRi : IsInt R := hR ▸ isInt_sub' ((hU.mul hJi).mul (isInt_cT' hσv hU)) ((hV.mul hJi).mul (isInt_cT' hσv hV))
  obtain ⟨S, hS⟩ : ∃ S, S = -(τ • (R * J)) := ⟨_, rfl⟩
  have hSc : cT σ S = -(σ τ • (J * R)) := by rw [hS, cT_neg', cT_smul', cT_mul, hRc, hJc]
  have hSi : IsInt S := hS ▸ isInt_neg' (isInt_smul' hτ (hRi.mul hJi))
  obtain ⟨Ψ₁, hΨ₁⟩ : ∃ Ψ, Ψ = J * cT σ U * J + A * S := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂⟩ : ∃ Ψ, Ψ = -(J * cT σ V * J) + B * S := ⟨_, rfl⟩
  have hΨ₁i : IsInt Ψ₁ := hΨ₁ ▸ ((hJi.mul (isInt_cT' hσv hU)).mul hJi).add (hA.mul hSi)
  have hΨ₂i : IsInt Ψ₂ := hΨ₂ ▸ (isInt_neg' ((hJi.mul (isInt_cT' hσv hV)).mul hJi)).add (hB.mul hSi)
  have h2 : cT σ A * cT σ U + cT σ B * cT σ V = 1 := by
    have := congrArg (cT σ) hUV
    rwa [cT_add', cT_mul, cT_mul, cT_one] at this
  have g12 : cT σ A * J * Ψ₁ - cT σ B * J * Ψ₂ = J := by
    rw [hΨ₁, hΨ₂]; exact ring_pair J A B U V _ _ _ _ S hJ h2 hAB
  have g21 : cT σ Ψ₁ * J * A - cT σ Ψ₂ * J * B = J := by
    have := congrArg (cT σ) g12
    simpa only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc] using this
  have cΨ₁ : cT σ Ψ₁ = J * U * J + cT σ S * cT σ A := by
    rw [hΨ₁]; simp only [cT_add', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have cΨ₂ : cT σ Ψ₂ = -(J * V * J) + cT σ S * cT σ B := by
    rw [hΨ₂]; simp only [cT_add', cT_neg', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have g22 : cT σ Ψ₁ * J * Ψ₁ - cT σ Ψ₂ * J * Ψ₂ = 0 := by
    rw [cΨ₁, cΨ₂, hΨ₁, hΨ₂, ring_gram J A B U V _ _ _ _ S _ hJ hUV h2 hAB, ← hR, hSc, hS]
    have e : J * R * J + J * -(τ • (R * J)) + -(σ τ • (J * R)) * J = (1 - τ - σ τ) • (J * R * J) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_smul, one_smul]
      abel
    rw [e, show 1 - τ - σ τ = 0 by linear_combination -hτ1, zero_smul]
  have e1 : σ τ • (1 : Matrix (Fin n) (Fin n) L) + τ • 1 = 1 := by rw [← add_smul, add_comm, hτ1, one_smul]
  have e2 : σ τ • J + τ • J = J := by rw [← add_smul, add_comm, hτ1, one_smul]
  obtain ⟨Jd, hJd⟩ : ∃ Jd : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, Jd = fromBlocks J 0 0 (-J) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, H = fromBlocks 0 J J 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks 1 (τ • 1) 1 (-(σ τ • 1)) := ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks (σ τ • 1) (τ • 1) 1 (-1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, P = fromBlocks A Ψ₁ B Ψ₂ := ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨e1, by simp, by simp, ?_⟩
    rw [add_comm]; exact e1
  have hHH : H * H = 1 := by
    rw [hH, fromBlocks_multiply, ← fromBlocks_one]
    simp [hJ]
  have hDg : cT σ D * Jd * D = H := by
    rw [hD, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [cT_neg', cT_smul', cT_one, hσσ, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨by simp, by rw [add_comm]; exact e2, e2, ?_⟩
    rw [smul_comm, add_neg_cancel]
  have hPg : cT σ P * Jd * P = H := by
    rw [hP, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg]
    simp only [← sub_eq_add_neg]
    rw [fromBlocks_inj]
    exact ⟨sub_eq_zero.2 hAB, g12, g21, g22⟩
  have hDi' : IsInt Di := hDi ▸ isInt_fromBlocks (isInt_smul' hτ' isInt_one) (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' isInt_one)
  have hDint : IsInt D := hD ▸ isInt_fromBlocks isInt_one (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' (isInt_smul' hτ' isInt_one))
  have hPi : IsInt P := hP ▸ isInt_fromBlocks hA hΨ₁i hB hΨ₂i
  have hHi : IsInt H := hH ▸ isInt_fromBlocks isInt_zero hJi hJi isInt_zero
  have hJdi : IsInt Jd := hJd ▸ isInt_fromBlocks hJi isInt_zero isInt_zero (isInt_neg' hJi)
  refine ⟨P * Di, D * H * cT σ P * Jd, hPi.mul hDi', ((hDint.mul hHi).mul (isInt_cT' hσv hPi)).mul hJdi, ?_, ?_, ?_, ?_⟩
  · calc D * H * cT σ P * Jd * (P * Di) = D * H * (cT σ P * Jd * P) * Di := by simp only [Matrix.mul_assoc]
      _ = D * (H * H) * Di := by rw [hPg]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, hDDi]
  · rw [← hJd]
    calc cT σ (P * Di) * Jd * (P * Di) = cT σ Di * (cT σ P * Jd * P) * Di := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ Di * (cT σ D * Jd * D) * Di := by rw [hPg, hDg]
      _ = cT σ (D * Di) * Jd * (D * Di) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Jd := by rw [hDDi, cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • A + Ψ₁ + (τ • A + -Ψ₁) = (τ + σ τ) • A by rw [add_smul]; abel, hτ1, one_smul]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • B + Ψ₂ + (τ • B + -Ψ₂) = (τ + σ τ) • B by rw [add_smul]; abel, hτ1, one_smul]

theorem completion : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hF
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  have hσσ := hU.1
  have hσv := hU.2.1
  obtain ⟨hUi, hVi, hC, hgC, hone⟩ := hF
  have hg : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have hAB : cT σ C * antiJ L n * C = cT σ (mat g * C) * antiJ L n * (mat g * C) := by
    rw [cT_mul]
    calc cT σ C * antiJ L n * C = cT σ C * (cT σ (mat g) * antiJ L n * mat g) * C := by rw [hg]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hUV : U * C + V * (mat g * C) = 1 := by
    rw [← hone]; simp only [Matrix.add_mul, Matrix.mul_assoc]
  obtain ⟨k₀, k₁, h0, h1, h10, hu, hx, hy⟩ := exists_block hσσ hσv hτ hτ1 hC hgC hUi hVi hAB hUV
  have hmul : k₀.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      k₁.submatrix (finSumFinEquiv (m := n) (n := n)).symm finSumFinEquiv.symm = 1 := by
    rw [submatrix_mul_equiv, mul_eq_one_comm.1 h10, submatrix_one_equiv]
  obtain ⟨k, hki, hke⟩ := P.cartan_exists_glint (intL L) _ _ hmul (fun i j => h0 _ _) (fun i j => h1 _ _)
  refine ⟨k, ?_, hki, fun x => ?_⟩
  · show cT σ (k : Matrix _ _ L) * dblGram finSumFinEquiv (antiJ L n) * (k : Matrix _ _ L) = _
    rw [hke, cT_submatrix, dblGram, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, hu]
  · rw [hke, mulVec_pairVec]
    have e : (k₀.submatrix (finSumFinEquiv (m := n) (n := n)).symm finSumFinEquiv.symm).submatrix finSumFinEquiv
        finSumFinEquiv = k₀ := by ext i j; simp
    rw [e, ← add_mulVec, ← add_mulVec, hx, hy]

end Main

end GlobalTheory.CompanionTheory.InertDoubling
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExistsStatement
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_exists : Completion := by
  first | exact @GlobalTheory.CompanionTheory.InertDoubling.completion | exact GlobalTheory.CompanionTheory.InertDoubling.completion | (intros; apply GlobalTheory.CompanionTheory.InertDoubling.completion <;> assumption)
end
end
