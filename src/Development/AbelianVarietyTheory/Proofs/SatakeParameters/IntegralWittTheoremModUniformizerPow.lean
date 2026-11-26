module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupHenselStepFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizer
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SkewLift

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L]

theorem cT_cT (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_mul_rect (σ : L →+* L) {a b c : Type} [Fintype b] (M : Matrix a b L) (N : Matrix b c L) :
    Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, map_sum, mul_comm]

theorem isIntM_sub' [Valued L (WithZero (Multiplicative ℤ))] {a b : Type} {M N : Matrix a b L} (hM : IsIntM M) (hN : IsIntM N) : IsIntM (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)

theorem skew_lift : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT herm ι _ _ z w a hz hw ha hdual hcong
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσσ := hU.1
  have hσv := hU.2.1
  have hhalf : (2 : L)⁻¹ ∈ Formalism.UG.intL L := by
    show Valued.v ((2 : L)⁻¹) ≤ 1
    rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJI : IsIntM J := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hcJ : Formalism.UG.cT σ J = J := cT_herm σ herm
  let B : Matrix (Fin n') ι L := fun r i => (J *ᵥ w i) r
  let Z : Matrix (Fin n') ι L := fun r j => z j r
  let A : Matrix ι (Fin n') L := fun i r => a i r
  let P : Matrix ι ι L := Formalism.UG.cT σ B * Z
  let C : Matrix (Fin n') (Fin n') L :=
    B * A - Formalism.UG.cT σ A * Formalism.UG.cT σ B + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * A)
  have hAZ : A * Z = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; exact hdual i j
  have hAI : IsIntM A := fun i r => ha i r
  have hZI : IsIntM Z := fun r j => hz j r
  have hBI : IsIntM B := fun r i => by
    show (J *ᵥ w i) r ∈ Formalism.UG.intL L
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun s _ => mul_mem (hJI r s) (hw i s)
  have hPI : IsIntM P := isIntM_mul (isIntM_cT hσv hBI) hZI
  have hcC : Formalism.UG.cT σ C = -C := by
    simp only [C, cT_add, cT_sub, cT_smul, cT_mul_rect, cT_cT σ hσσ, hσhalf]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, smul_sub, neg_add, neg_sub]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro r s
    have := congrFun (congrFun hcC s) r
    simpa [Formalism.UG.cT] using this
  · exact isIntM_add (isIntM_sub' (isIntM_mul hBI hAI) ((isIntM_mul (isIntM_cT hσv hAI) (isIntM_cT hσv hBI))))
      (isIntM_smul hhalf (isIntM_mul (isIntM_mul (isIntM_cT hσv hAI) (isIntM_sub' hPI (isIntM_cT hσv hPI))) hAI))
  · have hP : ∀ k i, P k i = Formalism.UG.hform σ J (w k) (z i) := by
      intro k i
      show ∑ r, σ (B r k) * z i r = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [B, Formalism.UG.hform, Matrix.transpose_apply, Matrix.map_apply,
        Matrix.mulVec, dotProduct, map_sum, map_mul, herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hσh : ∀ x y : Fin n' → L, σ (Formalism.UG.hform σ J x y) = Formalism.UG.hform σ J y x := by
      intro x y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Formalism.UG.hform, map_sum, map_mul, hσσ, herm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hS : ∀ k i, DvdPow ϖ 1 ((P + Formalism.UG.cT σ P) k i) := by
      intro k i
      have e : (P + Formalism.UG.cT σ P) k i = Formalism.UG.hform σ J (z k) (w i) + Formalism.UG.hform σ J (w k) (z i) := by
        show P k i + σ (P i k) = _
        rw [hP, hP, hσh, add_comm]
      rw [e]; exact hcong k i
    have hCZ : C * Z = B - (2⁻¹ : L) • (Formalism.UG.cT σ A * (P + Formalism.UG.cT σ P)) := by
      have e1 : C * Z = B * (A * Z) - Formalism.UG.cT σ A * P + (2⁻¹ : L) • (Formalism.UG.cT σ A * (P - Formalism.UG.cT σ P) * (A * Z)) := by
        simp only [C, P, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [e1, hAZ, Matrix.mul_one, Matrix.mul_one]
      have e2 : Formalism.UG.cT σ A * P = (2⁻¹ : L) • (Formalism.UG.cT σ A * P) + (2⁻¹ : L) • (Formalism.UG.cT σ A * P) := by
        rw [← add_smul]
        have : (2⁻¹ + 2⁻¹ : L) = 1 := by
          have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
          field_simp; norm_num
        rw [this, one_smul]
      rw [e2, Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub]
      abel
    intro i r
    have e : (C *ᵥ z i) r - (J *ᵥ w i) r = (C * Z) r i - B r i := rfl
    rw [e, hCZ, Matrix.sub_apply, sub_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    refine dvdPow_neg (dvdPow_sum _ _ fun k _ => ?_)
    rw [← mul_assoc]
    exact dvdPow_mul_int (hS k i) (mul_mem hhalf (isIntM_cT hσv hAI r k))

end GlobalTheory.Hk3.SkewLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizerStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  first | exact @GlobalTheory.Hk3.SkewLift.skew_lift | exact GlobalTheory.Hk3.SkewLift.skew_lift | (intros; apply GlobalTheory.Hk3.SkewLift.skew_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformIntegralUnitaryCongruentOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformIntegralUnitaryCongruentOne
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.CayleyCong

open GlobalTheory.Hk3.CayleyPhase GlobalTheory.Hk3.IntWitt

theorem cayley_cong : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hermT C hskew hCI k hk
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  have hσv := hU.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hvϖ : Valued.v ϖ < 1 := by
    rw [hU.2.2.2.1]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) < 1 by decide)
  have hϖI : ϖ ∈ Formalism.UG.intL L := le_of_lt hvϖ
  have hvϖk : Valued.v (ϖ ^ k) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hvϖ (by omega)
  have hhalf : Valued.v ((2 : L)⁻¹) ≤ 1 := by rw [map_inv₀, h2, inv_one]
  have hσhalf : σ ((2 : L)⁻¹) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  set Jt : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJt
  set Jti : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJti
  have hJtiI : IsIntM Jti := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJJi : Jt * Jti = 1 := by rw [hJt, hJti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcJt : Formalism.UG.cT σ Jt = Jt := cT_herm σ hermT
  have hcC : Formalism.UG.cT σ C = -C := cT_skew σ hskew
  have hcJti : Formalism.UG.cT σ Jti * Jt = 1 := by
    calc Formalism.UG.cT σ Jti * Jt = Formalism.UG.cT σ Jti * Formalism.UG.cT σ Jt := by rw [hcJt]
      _ = Formalism.UG.cT σ (Jt * Jti) := (Formalism.UG.cT_mul σ _ _).symm
      _ = 1 := by rw [hJJi, Formalism.UG.cT_one]
  set M : Matrix (Fin n') (Fin n') L := Jti * C with hMdef
  have hMI : IsIntM M := isIntM_mul hJtiI hCI
  set Y : Matrix (Fin n') (Fin n') L := ϖ ^ k • M with hYdef
  have hσϖk : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hσϖ]
  have hY : Formalism.UG.cT σ Y * Jt = -(ϖ ^ k • C) := by
    rw [hYdef, cT_smul, hσϖk, Matrix.smul_mul, hMdef, Formalism.UG.cT_mul, hcC, Matrix.mul_assoc, hcJti, Matrix.mul_one,
      smul_neg]
  have hJY : Jt * Y = ϖ ^ k • C := by
    rw [hYdef, Matrix.mul_smul, hMdef, ← Matrix.mul_assoc, hJJi, Matrix.one_mul]
  set Z : Matrix (Fin n') (Fin n') L := (2⁻¹ : L) • Y with hZdef
  have hZZ : Z + Z = Y := by
    rw [hZdef, ← add_smul]
    have : (2⁻¹ + 2⁻¹ : L) = 1 := by
      have h2ne : (2 : L) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
      field_simp; norm_num
    rw [this, one_smul]
  have hZ : Formalism.UG.cT σ Z * Jt = -(Jt * Z) := by
    rw [hZdef, cT_smul, hσhalf, Matrix.smul_mul, hY, Matrix.mul_smul, hJY, smul_neg]
  have hYsmall : IsSmallM Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul]; exact lt_one_mul hvϖk (hMI i j)
  have hZsmall : IsSmallM Z := small_smul hhalf hYsmall
  obtain ⟨hPdet, hPiI⟩ := inv_one_sub hZsmall
  obtain ⟨hQdet, hQiI⟩ := inv_one_add hZsmall
  set Pi := (1 - Z)⁻¹ with hPi
  set Qi := (1 + Z)⁻¹ with hQi
  have hP1 : Pi * (1 - Z) = 1 := Matrix.nonsing_inv_mul _ hPdet
  have hP2 : (1 - Z) * Pi = 1 := Matrix.mul_nonsing_inv _ hPdet
  have hQ1 : Qi * (1 + Z) = 1 := Matrix.nonsing_inv_mul _ hQdet
  have hQ2 : (1 + Z) * Qi = 1 := Matrix.mul_nonsing_inv _ hQdet
  have hPs : Formalism.UG.cT σ Pi * (1 - Formalism.UG.cT σ Z) = 1 := by
    rw [← Formalism.UG.cT_one σ, ← cT_sub, ← Formalism.UG.cT_mul, hP2]
  let g : GL (Fin n') L := ⟨Pi * (1 + Z), Qi * (1 - Z), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 + Z), hQ2, Matrix.one_mul, hP1], by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Z), hP2, Matrix.one_mul, hQ1]⟩
  have hgU : g ∈ Formalism.UG.UJ σ Jt := by
    show Formalism.UG.cT σ (Pi * (1 + Z)) * Jt * (Pi * (1 + Z)) = Jt
    rw [Formalism.UG.cT_mul, cT_add, Formalism.UG.cT_one]
    exact cayley_unitary_ring hZ hP1 hP2 hQ1 hQ2 hPs
  have hone : IsIntM (1 : Matrix (Fin n') (Fin n') L) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hIZ : IsIntM (1 + Z) := isIntM_add hone (isIntM_of_small hZsmall)
  have hIZ' : IsIntM (1 - Z) := by
    rw [sub_eq_add_neg]; exact isIntM_add hone (isIntM_neg (isIntM_of_small hZsmall))
  have hgI : g ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) :=
    mem_GLint_of_int (isIntM_mul hPiI hIZ) (isIntM_mul hQiI hIZ')
  obtain ⟨hr1, hr2⟩ := cayley_ring hP1 hP2
  have hg1 : Pi * (1 + Z) - 1 = ϖ ^ k • (M * Pi) := by
    rw [hr1, hZZ, hYdef, Matrix.smul_mul]
  have hg2 : Pi * (1 + Z) - 1 - Y = (ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹)) • (M * Pi * M) := by
    have e : ϖ ^ (k + 1) * (ϖ ^ (k - 1) * 2⁻¹) = ϖ ^ k * (2⁻¹ * ϖ ^ k) := by
      have : k + 1 + (k - 1) = k + k := by omega
      rw [← mul_assoc, ← pow_add, this, pow_add]; ring
    rw [e, hr1, hZZ]
    have e2 : Y * Pi - Y = Y * (Pi - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]
    rw [e2, hr2, hZdef, hYdef]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc]
    congr 1; ring
  refine ⟨⟨g, hgU⟩, hgI, fun r s => ?_, fun r s => ?_⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s =
        (Pi * (1 + Z) - 1) r s := by rw [Matrix.sub_apply]
    rw [this, hg1, Matrix.smul_apply, smul_eq_mul]
    exact ⟨_, isIntM_mul hMI hPiI r s, rfl⟩
  · have : ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s =
        (Pi * (1 + Z) - 1 - Y) r s := by rw [Matrix.sub_apply, Matrix.sub_apply]
    rw [this, hg2, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    refine ⟨_, mul_mem (mul_mem (pow_mem hϖI _) hhalf) (isIntM_mul (isIntM_mul hMI hPiI) hMI r s), rfl⟩

end GlobalTheory.Hk3.CayleyCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformIntegralUnitaryCongruentOneStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_transform_integral_unitary_congruent_one : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) → (∀ r s, C r s ∈ Formalism.UG.intL L) →
    ∀ k : ℕ, 1 ≤ k →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s -
        (ϖ ^ k • (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * C)) r s) := by
  first | exact @GlobalTheory.Hk3.CayleyCong.cayley_cong | exact GlobalTheory.Hk3.CayleyCong.cayley_cong | (intros; apply GlobalTheory.Hk3.CayleyCong.cayley_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralDualOfIndependentModUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralDualOfIndependentModUniformizer
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isUnit_valuationSubring_iff (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsUnit x ↔ Valued.v (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := congrArg (fun y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring =>
      Valued.v (y : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h1
    have hu : Valued.v ((u : _) : L) ≤ 1 := ((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)).2
    have hw : Valued.v ((u⁻¹ : _) : L) ≤ 1 := ((u⁻¹ : _) : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).2
    refine le_antisymm hu ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ Valued.v ((u : _) : L) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hx0 : (x : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    let y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring :=
      ⟨(x : L)⁻¹, by
        show Valued.v (x : L)⁻¹ ≤ 1
        rw [map_inv₀, h, inv_one]⟩
    have hxy : x * y = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, rfl⟩

theorem residue_eq_zero_iff_dvdPow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (x : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    IsLocalRing.residue _ x = 0 ↔ DvdPow ϖ 1 (x : L) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_valuationSubring_iff]
  have hx : Valued.v (x : L) ≤ 1 := x.2
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  constructor
  · intro hne
    have hlt : Valued.v (x : L) < 1 := lt_of_le_of_ne hx hne
    have hle := le_exp_neg_one_of_lt_one' hlt
    refine ⟨(x : L) / ϖ, ?_, by field_simp⟩
    show Valued.v ((x : L) / ϖ) ≤ 1
    rw [map_div₀, hϖ]
    have hpos : (0 : WithZero (Multiplicative ℤ)) < ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
      WithZero.zero_lt_coe _
    exact (div_le_one₀ hpos).2 hle
  · rintro ⟨b, hb, hxb⟩ h1
    have hb' : Valued.v b ≤ 1 := hb
    rw [hxb, pow_one, map_mul, hϖ] at h1
    have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * Valued.v b ≤
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * 1 := by gcongr
    rw [h1, mul_one] at this
    exact absurd this (by decide)

theorem exists_dual_of_indepMod : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  intro L _ _ ϖ hϖ m ι _ _ z hz hind
  classical
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  let Z : Matrix ι (Fin m) O := fun i r => ⟨z i r, hz i r⟩
  let Zb : Matrix ι (Fin m) k := Z.map res

  have hinj : LinearMap.ker (Matrix.mulVecLin Zbᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    let d : ι → O := fun i => (hres (w i)).choose
    have hd : ∀ i, res (d i) = w i := fun i => (hres (w i)).choose_spec
    have hsum : ∀ r, DvdPow ϖ 1 (∑ i, ((d i : O) : L) * z i r) := by
      intro r
      have h1 : res (∑ i, d i * Z i r) = 0 := by
        have := congrFun hw r
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simpa [Zb, hd, mul_comm] using this
      have h2 := (residue_eq_zero_iff_dvdPow hϖ _).1 h1
      simpa [Z] using h2
    have hdi := hind (fun i => (d i : L)) (fun i => (d i).2) hsum
    funext i
    rw [← hd i]
    exact (residue_eq_zero_iff_dvdPow hϖ _).2 (hdi i)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  let B : Matrix ι (Fin m) k := LinearMap.toMatrix' g
  have hB : B * Zbᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
  let Bo : Matrix ι (Fin m) O := fun i r => (hres (B i r)).choose
  have hBo : Bo.map res = B := by
    ext i r; exact (hres (B i r)).choose_spec
  let M : Matrix ι ι O := Bo * Zᵀ
  have hM : M.map res = 1 := by
    simp only [M, Matrix.map_mul, Matrix.transpose_map, hBo]
    exact hB
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : res M.det = 1 := by
      rw [RingHom.map_det]
      change (M.map res).det = 1
      rw [hM, Matrix.det_one]
    rw [show IsLocalRing.residue O M.det = res M.det from rfl, this]
    exact one_ne_zero
  let A : Matrix ι (Fin m) O := M⁻¹ * Bo
  have hA : A * Zᵀ = 1 := by
    simp only [A, Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul M hdet
  refine ⟨fun i r => (A i r : L), fun i r => (A i r).2, fun i j => ?_⟩
  have h := congrArg (fun x : O => (x : L)) (congrFun (congrFun hA i) j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have h2 : ((∑ r, A i r * Z j r : O) : L) = ∑ r, (A i r : L) * z j r := by
    simp [Z, O]
  rw [h2] at h
  rw [h]
  split_ifs <;> simp

end GlobalTheory.Hk3.IntWitt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralDualOfIndependentModUniformizerStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_of_independentModUniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (m : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → Fin m → L), (∀ i r, z i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    ∃ a : ι → Fin m → L, (∀ i r, a i r ∈ Formalism.UG.intL L) ∧ ∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod | exact GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod | (intros; apply GlobalTheory.Hk3.IntWitt.exists_dual_of_indepMod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupHenselStepFamilies
open Matrix

namespace GlobalTheory.Hk3.IntWitt

theorem hensel_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L) (k : ℕ), 1 ≤ k →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    (∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k (z' i r - z i r)) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ ϖ σ q hU hq n' JT hJT hherm ι _ z z' k hk hz hz' hind hdiff hgram
  classical
  have hv := hU.2.2.2.1
  have hσϖ : σ ϖ = ϖ := hU.2.2.1
  have hσv := hU.2.1
  have hϖI : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hv]; exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 from by decide)
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJI : ∀ r s, J r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint hJT
  have hJiI : ∀ r s, Ji r s ∈ Formalism.UG.intL L := GlobalTheory.Hk3.HoweDuality.entry_mem_of_mem_GLint (inv_mem hJT)
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  choose w hwI hwe using hdiff
  have hz'e : ∀ i r, z' i r = z i r + ϖ ^ k * w i r := fun i r => by rw [← hwe]; ring
  have hz'v : ∀ i, z' i = z i + ϖ ^ k • w i := fun i => funext fun r => by simp [hz'e]

  have hformI : ∀ x y : Fin n' → L, (∀ r, x r ∈ Formalism.UG.intL L) → (∀ r, y r ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ J x y ∈ Formalism.UG.intL L := by
    intro x y hx hy
    refine sum_mem fun r _ => sum_mem fun s _ => mul_mem (mul_mem ?_ (hJI r s)) (hy s)
    show Valued.v (σ (x r)) ≤ 1
    rw [hσv]; exact hx r
  have key : ∀ i j, Formalism.UG.hform σ J (z' i) (z' j) - Formalism.UG.hform σ J (z i) (z j) =
      ϖ ^ k * (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) + ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
    intro i j
    simp only [Formalism.UG.hform, hz'e, map_add (f := _), map_mul, map_pow, hσϖ, mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  have hgram1 : ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j)) := by
    intro i j
    have h1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ J (z i) (w j) + Formalism.UG.hform σ J (w i) (z j) +
        ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      obtain ⟨b, hb, hbe⟩ := hgram i j
      refine ⟨b, hb, ?_⟩
      have := (key i j).symm.trans hbe
      rw [pow_succ, mul_assoc] at this
      rw [pow_one]
      exact mul_left_cancel₀ (pow_ne_zero k hϖ0) this
    have h2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (ϖ ^ k * Formalism.UG.hform σ J (w i) (w j)) := by
      refine ⟨ϖ ^ (k - 1) * Formalism.UG.hform σ J (w i) (w j),
        mul_mem (pow_mem hϖI _) (hformI _ _ (hwI i) (hwI j)), ?_⟩
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    have := GlobalTheory.Hk3.IntWitt.dvdPow_sub h1 h2
    simpa using this
  obtain ⟨a, haI, ha⟩ := GlobalTheory.T.exists_integral_dual_of_independentModUniformizer L ϖ hv n' ι z hz hind
  obtain ⟨C, hCs, hCI, hCz⟩ := GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer L ϖ σ q hU hq n' JT hJT hherm ι z w a hz hwI haI ha hgram1
  obtain ⟨g, hgI, hg1, hg2⟩ := GlobalTheory.T.cayley_transform_integral_unitary_congruent_one L ϖ σ q hU hq n' JT hJT hherm C hCs hCI k hk
  refine ⟨g, hgI, hg1, fun i r => ?_⟩
  set G : Matrix (Fin n') (Fin n') L := ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hGdef
  have e : G *ᵥ z i - z' i = (G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i + ϖ ^ k • (Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec (w i) Ji J, hJiJ, Matrix.one_mulVec, hz'v, smul_sub]
    abel
  have e' := congrFun e r
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e'
  rw [e']
  have t1 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (((G - 1 - ϖ ^ k • (Ji * C)) *ᵥ z i) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (∑ s, (G - 1 - ϖ ^ k • (Ji * C)) r s * z i s)
    refine GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => ?_
    rw [mul_comm]
    exact GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hg2 r s) (hz i s)
  have t2 : GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((Ji *ᵥ (C *ᵥ z i - J *ᵥ w i)) r) := by
    show GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (∑ s, Ji r s * (C *ᵥ z i - J *ᵥ w i) s)
    exact GlobalTheory.Hk3.IntWitt.dvdPow_sum _ _ fun s _ => GlobalTheory.Hk3.IntWitt.dvdPow_mul_int (hCz i s) (hJiI r s)
  refine GlobalTheory.Hk3.IntWitt.dvdPow_add t1 ?_
  obtain ⟨b, hb, hbe⟩ := t2
  exact ⟨b, hb, by rw [hbe, pow_succ]; ring⟩

end GlobalTheory.Hk3.IntWitt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupHenselStepFamiliesStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_hensel_step_families : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L) (k : ℕ), 1 ≤ k →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z →
    (∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k (z' i r - z i r)) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (g : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      (∀ r s, GlobalTheory.Hk3.IntWitt.DvdPow ϖ k ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) r s - (1 : Matrix (Fin n') (Fin n') L) r s)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) ((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.IntWitt.hensel_step | exact GlobalTheory.Hk3.IntWitt.hensel_step | (intros; apply GlobalTheory.Hk3.IntWitt.hensel_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittTheoremModUniformizerPow
noncomputable section

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem pi_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem glint_entry {n : ℕ} {h : GL (Fin n) L} (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (r s : Fin n) :
    (h : Matrix (Fin n) (Fin n) L) r s ∈ Formalism.UG.intL L := by
  obtain ⟨g0, hg0⟩ := hh
  rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) r s).2

theorem mulVec_int {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : (M *ᵥ v) r ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun s _ => (Formalism.UG.intL L).mul_mem (hM r s) (hv s)

theorem dvdPow_mulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, DvdPow ϖ k (M r s))
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]; exact dvdPow_mul_int (hM r s) (hv s)

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (h : Formalism.UG.UJ σ J) (x y : Fin n → L) :
    Formalism.UG.hform σ J (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x)
      (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hu : Formalism.UG.cT σ ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J := h.2
  rw [hform_eq_dot, hform_eq_dot]
  set H := ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have e1 : (fun i => σ ((H *ᵥ x) i)) = (H.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; exact RingHom.map_mulVec σ H x i
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  exact congrArg (· *ᵥ y) hu

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_intMulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, DvdPow ϖ k (v r)) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  exact dvdPow_sum _ _ fun s _ => dvdPow_mul_int (hv s) (hM r s)

theorem indepMod_mulVec {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {h : GL (Fin n) L}
    (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) {z : ι → Fin n → L} (hz : IndepMod ϖ z) :
    IndepMod ϖ (fun i => (h : Matrix (Fin n) (Fin n) L) *ᵥ z i) := by
  intro d hd hs i
  refine hz d hd (fun r => ?_) i
  set w : Fin n → L := ∑ j, d j • z j with hw
  have e1 : ∀ s, ((h : Matrix (Fin n) (Fin n) L) *ᵥ w) s = ∑ j, d j * ((h : Matrix (Fin n) (Fin n) L) *ᵥ z j) s := by
    intro s
    simp [hw, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]
  have e2 : ∑ j, d j * z j r = (((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ ((h : Matrix (Fin n) (Fin n) L) *ᵥ w)) r := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    simp [hw, Finset.sum_apply]
  rw [e2]
  exact dvdPow_intMulVec (glint_entry ((Formalism.UG.GLint _ _).inv_mem hh)) (fun s => by rw [e1]; exact hs s) r

theorem indepMod_sub {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {z : ι → Fin n → L} (hz : IndepMod ϖ z)
    (p : ι → Prop) [DecidablePred p] : IndepMod ϖ (fun i : {i // p i} => z i.1) := by
  intro d hd hs i
  let d' : ι → L := fun j => if hj : p j then d ⟨j, hj⟩ else 0
  have h1 : ∀ j, d' j ∈ Formalism.UG.intL L := by
    intro j; by_cases hj : p j
    · simp only [d', dif_pos hj]; exact hd _
    · simp only [d', dif_neg hj]; exact (Formalism.UG.intL L).zero_mem
  have h2 : ∀ r, ∑ j, d' j * z j r = ∑ j : {i // p i}, d j * z j.1 r := by
    intro r
    rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => d' j * z j r)]
    have a1 : ∑ j : {i // ¬ p i}, d' j.1 * z j.1 r = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [d', dif_neg j.2]
    rw [a1, add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp [d', dif_pos j.2]
  have := hz d' h1 (fun r => by rw [h2]; exact hs r) i.1
  simpa [d', dif_pos i.2] using this

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

theorem witt_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJT hJh ι _ a z z' ha hz hz' hiz hiz' hG
  classical
  have hϖ := pi_int hU
  have key : ∀ k, 1 ≤ k → ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
      (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, DvdPow ϖ (min (a i) k) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨h, hh, hc⟩ := GlobalTheory.T.integral_witt_unitary_mod_uniformizer L ϖ σ q hU hq n' JT hJT hJh ι z z' hz hz' hiz hiz'
        (fun i j => dvdPow_mono hϖ (le_min (ha i) (ha j)) (hG i j))
      refine ⟨h, hh, fun i r => ?_⟩
      rw [min_eq_right (ha i)]; exact hc i r
    | succ k hk ih =>
      obtain ⟨h, hh, hc⟩ := ih
      have hHint := glint_entry hh
      obtain ⟨g, hg, hg1, hgc⟩ := GlobalTheory.T.unitaryGroup_hensel_step_families L ϖ σ q hU hq n' JT hJT hJh {i // k < a i}
        (fun i => ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i.1) (fun i => z' i.1) k hk
        (fun i r => mulVec_int hHint (hz i.1) r) (fun i r => hz' i.1 r)
        (indepMod_sub (indepMod_mulVec hh hiz) (fun i => k < a i))
        (fun i r => by
          have h0 := hc i.1 r
          rw [min_eq_right i.2.le] at h0
          have h1 := dvdPow_neg h0
          rwa [neg_sub] at h1)
        (fun i j => by
          simp only [hform_unitary]
          exact dvdPow_mono hϖ (le_min i.2 j.2) (hG i.1 j.1))
      refine ⟨g * h, (Formalism.UG.GLint _ _).mul_mem hg hh, fun i r => ?_⟩
      have e : (((g * h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i
          = ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) := by
        simp [Matrix.mulVec_mulVec]
      rw [e]
      by_cases hki : k < a i
      · rw [min_eq_right (Nat.succ_le_of_lt hki)]
        exact hgc ⟨i, hki⟩ r
      · push_neg at hki
        rw [min_eq_left (by omega)]
        have h2 := hc i r
        rw [min_eq_left hki] at h2
        have h1 : DvdPow ϖ (a i) (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
            (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r) :=
          dvdPow_mono hϖ hki (dvdPow_mulVec (fun r s => by simpa [Matrix.sub_apply] using hg1 r s)
            (mulVec_int hHint (hz i)) r)
        have e2 : (((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r - z' i r
            = (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
              (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r)
              + ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
        rw [e2]; exact dvdPow_add h1 h2
  obtain ⟨h, hh, hc⟩ := key (1 + ∑ i, a i) (by omega)
  refine ⟨h, hh, fun i r => ?_⟩
  have h0 := hc i r
  have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  rwa [min_eq_left (by omega)] at h0

end GlobalTheory.Hk3.IntWittMod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittTheoremModUniformizerPowStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralWittTheorem_mod_uniformizerPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.IntWittMod.witt_mod_pow | exact GlobalTheory.Hk3.IntWittMod.witt_mod_pow | (intros; apply GlobalTheory.Hk3.IntWittMod.witt_mod_pow <;> assumption)
end
