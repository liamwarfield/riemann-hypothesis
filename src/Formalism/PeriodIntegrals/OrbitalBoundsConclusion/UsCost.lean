module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.EntryLeLsz
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Smooth
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZDeriv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZCostOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterC
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterB
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterA
open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.ZI

section quad

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem norm_iteratedFDeriv_le_of_fderiv_eq_quadratic
    (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  rcases a with _ | a
  · refine ⟨1, zero_le_one, fun z _ => ?_⟩
    rw [norm_iteratedFDeriv_zero, one_mul, zero_add, pow_one]
    exact le_max_right _ _
  · choose! K hK0 hK using ih
    refine ⟨‖Bi‖ * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * (K i * K (a - i)),
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i hi => ?_), fun z hz => ?_⟩
    · have hi' := Finset.mem_range.1 hi
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i (by omega)) (hK0 (a - i) (by omega)))
    · have hm : 1 ≤ max 1 ‖φ z‖ := le_max_left _ _
      have hm0 : 0 ≤ max 1 ‖φ z‖ := zero_le_one.trans hm
      have heq : Set.EqOn (fderiv ℝ φ) (fun y => Bi (φ y) (φ y)) U := fun y hy => hd y hy
      have e1 : ‖iteratedFDeriv ℝ (a + 1) φ z‖ =
          ‖iteratedFDerivWithin ℝ a (fun y => Bi (φ y) (φ y)) U z‖ := by
        rw [← norm_iteratedFDeriv_fderiv,
          ← (iteratedFDerivWithin_of_isOpen a hU hz :
            iteratedFDerivWithin ℝ a (fderiv ℝ φ) U z = iteratedFDeriv ℝ a (fderiv ℝ φ) z),
          iteratedFDerivWithin_congr heq hz]
      rw [e1]
      refine (Bi.norm_iteratedFDerivWithin_le_of_bilinear (hφ a) (hφ a) hU.uniqueDiffOn hz
        le_rfl).trans ?_
      rw [mul_assoc ‖Bi‖, Finset.sum_mul]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg _)
      have hi' := Finset.mem_range.1 hi
      rw [iteratedFDerivWithin_of_isOpen i hU hz, iteratedFDerivWithin_of_isOpen (a - i) hU hz]
      have h1 := hK i (by omega) z hz
      have h2 := hK (a - i) (by omega) z hz
      have hpow : max 1 ‖φ z‖ ^ (a + 1 + 1) =
          max 1 ‖φ z‖ ^ (i + 1) * max 1 ‖φ z‖ ^ (a - i + 1) := by
        rw [← pow_add]; congr 1; omega
      calc (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ z‖ * ‖iteratedFDeriv ℝ (a - i) φ z‖
          ≤ (a.choose i : ℝ) * (K i * max 1 ‖φ z‖ ^ (i + 1)) *
              (K (a - i) * max 1 ‖φ z‖ ^ (a - i + 1)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
            exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i (by omega)) (pow_nonneg hm0 _))
        _ = (a.choose i : ℝ) * (K i * K (a - i)) * max 1 ‖φ z‖ ^ (a + 1 + 1) := by
            rw [hpow]; ring

theorem quad_bound (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ∀ a ≤ n, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by
  choose K hK0 hK using norm_iteratedFDeriv_le_of_fderiv_eq_quadratic Bi hU hφ hd
  refine ⟨∑ a ∈ Finset.range (n + 1), K a, Finset.sum_nonneg fun a _ => hK0 a,
    fun z hz a ha => ?_⟩
  refine (hK a z hz).trans (mul_le_mul_of_nonneg_right ?_
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  exact Finset.single_le_sum (f := K) (fun b _ => hK0 b) (Finset.mem_range.2 (by omega))

end quad

section words

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

theorem norm_smulRightL_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖ContinuousLinearMap.smulRightL ℝ V E‖ ≤ 1 := by
  exact ContinuousLinearMap.norm_smulRightL_le

private theorem one_le_pow_of_one_le_real {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : 1 ≤ x ^ n := by
  exact one_le_pow₀ hx

private theorem pow_le_pow_right_of_one_le {x : ℝ} (hx : 1 ≤ x) {m n : ℕ} (h : m ≤ n) :
    x ^ m ≤ x ^ n := by
  exact pow_le_pow_right₀ hx h

private theorem mul_pow_mul_le_mul_pow_succ {Kc R β lam M : ℝ} {b j : ℕ} (hj : j ≤ b) (hKc : 0 ≤ Kc)
    (hR : 1 ≤ R) (hβ : 0 ≤ β) (hlam : 1 ≤ lam) (hM : 1 ≤ M) :
    Kc * M ^ (j + 1) * (R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j)) ≤
      Kc * R ^ b * β * (lam * M) ^ (b + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hL : 0 ≤ Kc * M ^ (j + 1) * (R ^ k * (β * lam) * (lam * M) ^ k) :=
    mul_nonneg (mul_nonneg hKc (pow_nonneg hM0 _))
      (mul_nonneg (mul_nonneg (pow_nonneg hR0 _) (mul_nonneg hβ hlam0))
        (pow_nonneg (mul_nonneg hlam0 hM0) _))
  have hX : 1 ≤ R ^ j * lam ^ j :=
    one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le_real hR j)
      (one_le_pow_of_one_le_real hlam j)
  calc _ ≤ Kc * M ^ (j + 1) * (R ^ k * (β * lam) * (lam * M) ^ k) * (R ^ j * lam ^ j) :=
        le_mul_of_one_le_right hL hX
    _ = _ := by ring

theorem iter_words (q : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {α E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Cls : ℕ → (α → E) → Prop)
      (Dop : I → (α → E) → (α → E)) (Γ : V → α) (U : Set V) (c : I → V → (V →L[ℝ] ℝ)) (z₀ : V)
      (M lam : ℝ),
      IsOpen U → z₀ ∈ U → 1 ≤ M → 1 ≤ lam →
      (∀ b H, Cls (b + 1) H → Cls b H) →
      (∀ b H i, Cls (b + 1) H → Cls b (Dop i H)) →
      (∀ b H, Cls b H → ∀ z ∈ U, ContDiffAt ℝ b (fun z => H (Γ z)) z) →
      (∀ b H, Cls (b + 1) H → ∀ z ∈ U,
        fderiv ℝ (fun z => H (Γ z)) z = ∑ i, (c i z).smulRight (Dop i H (Γ z))) →
      (∀ i (n : ℕ), ContDiffOn ℝ n (c i) U) →
      (∀ i, ∀ a ≤ q, ‖iteratedFDeriv ℝ a (c i) z₀‖ ≤ Kc * M ^ (a + 1)) →
      ∀ b ≤ q, ∀ (H : α → E) (β : ℝ), Cls b H →
        (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
        ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ C * β * (lam * M) ^ b := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ((Fintype.card I : ℝ) * Kc + 1) * 2 ^ q := ⟨_, rfl⟩
  have hNK : 0 ≤ (Fintype.card I : ℝ) * Kc := mul_nonneg (Nat.cast_nonneg _) hKc
  have hR : 1 ≤ R := by
    rw [hRdef]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow_of_one_le_real (by norm_num) q)
  have hR0 : 0 ≤ R := by linarith
  refine ⟨R ^ q, one_le_pow_of_one_le_real hR q, ?_⟩
  intro α E _ _ Cls Dop Γ U c z₀ M lam hU hz₀ hM hlam hdown hDop hsmooth hderiv hc hcb
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hmono : ∀ a b (H : α → E), a ≤ b → Cls b H → Cls a H := by
    intro a b H hab
    induction hab with
    | refl => exact id
    | step _ ih => exact fun h => ih (hdown _ _ h)
  have key : ∀ b, b ≤ q → ∀ (H : α → E) (β : ℝ), Cls b H →
      (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
      ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ R ^ b * β * (lam * M) ^ b := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
    intro hb H β hH hw
    have hβ0 : ‖H (Γ z₀)‖ ≤ β := by simpa using hw [] (Nat.zero_le _)
    have hβ : 0 ≤ β := (norm_nonneg _).trans hβ0
    rcases b with _ | b
    · simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, mul_one]
      exact hβ0
    · obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Kc * R ^ b * β * (lam * M) ^ (b + 1) := ⟨_, rfl⟩
      have hG : ∀ i, ContDiffOn ℝ b (fun z => Dop i H (Γ z)) U := fun i z hz =>
        (hsmooth b (Dop i H) (hDop b H i hH) z hz).contDiffWithinAt
      have hf : ∀ i, ContDiffOn ℝ b
          (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U := fun i =>
        ((ContinuousLinearMap.smulRightL ℝ V E).contDiff.comp_contDiffOn (hc i b)).clm_apply (hG i)
      have heq : Set.EqOn (fderiv ℝ (fun z => H (Γ z)))
          (∑ i, fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U := by
        intro z hz
        rw [Finset.sum_apply, hderiv b H hH z hz]
        rfl
      have hfi : ∀ i, ‖iteratedFDerivWithin ℝ b
          (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ ≤
            2 ^ b * T := by
        intro i
        refine ((ContinuousLinearMap.smulRightL ℝ V E).norm_iteratedFDerivWithin_le_of_bilinear
          (hc i b) (hG i) hU.uniqueDiffOn hz₀ le_rfl).trans ?_
        have hsum : ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ *
            ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖ ≤
              ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * T := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hcj : ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ ≤ Kc * M ^ (j + 1) := by
            rw [iteratedFDerivWithin_of_isOpen j hU hz₀]
            exact hcb i j (by omega)
          have hGj : ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖ ≤
              R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j) := by
            rw [iteratedFDerivWithin_of_isOpen (b - j) hU hz₀]
            refine ih (b - j) (by omega) (by omega) (Dop i H) (β * lam)
              (hmono _ _ _ (Nat.sub_le b j) (hDop b H i hH)) fun w hw' => ?_
            have h := hw (w ++ [i]) (by rw [List.length_append, List.length_singleton]; omega)
            simp only [List.foldr_append, List.foldr_cons, List.foldr_nil, List.length_append,
              List.length_singleton] at h
            calc _ ≤ β * lam ^ (w.length + 1) := h
              _ = β * lam * lam ^ w.length := by ring
          calc ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ *
                ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖
              ≤ (Kc * M ^ (j + 1)) * (R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j)) :=
                mul_le_mul hcj hGj (norm_nonneg _) (mul_nonneg hKc (pow_nonneg hM0 _))
            _ ≤ T := by
                rw [hT]
                exact mul_pow_mul_le_mul_pow_succ (by omega) hKc hR hβ hlam hM
        calc _ ≤ 1 * ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * T :=
              mul_le_mul (norm_smulRightL_le E) hsum
                (Finset.sum_nonneg fun j _ => by positivity) zero_le_one
          _ = 2 ^ b * T := by
              rw [one_mul, ← Finset.sum_mul]
              congr 1
              exact_mod_cast Nat.sum_range_choose b
      have hN : (Fintype.card I : ℝ) * Kc * 2 ^ b ≤ R := by
        have h2 : (2 : ℝ) ^ b ≤ 2 ^ q := pow_le_pow_right_of_one_le (by norm_num) (by omega)
        calc _ ≤ (Fintype.card I : ℝ) * Kc * 2 ^ q := mul_le_mul_of_nonneg_left h2 hNK
          _ ≤ R := by
              rw [hRdef, add_mul, one_mul]
              exact le_add_of_nonneg_right (pow_nonneg (by norm_num) q)
      have hX : 0 ≤ R ^ b * β * (lam * M) ^ (b + 1) :=
        mul_nonneg (mul_nonneg (pow_nonneg hR0 _) hβ) (pow_nonneg (mul_nonneg hlam0 hM0) _)
      calc ‖iteratedFDeriv ℝ (b + 1) (fun z => H (Γ z)) z₀‖
          = ‖iteratedFDerivWithin ℝ b
              (∑ i, fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z)))
              U z₀‖ := by
            rw [← norm_iteratedFDeriv_fderiv,
              ← (iteratedFDerivWithin_of_isOpen b hU hz₀ :
                iteratedFDerivWithin ℝ b (fderiv ℝ (fun z => H (Γ z))) U z₀ =
                  iteratedFDeriv ℝ b (fderiv ℝ (fun z => H (Γ z))) z₀),
              iteratedFDerivWithin_congr heq hz₀]
        _ = ‖∑ i, iteratedFDerivWithin ℝ b
              (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ := by
            rw [iteratedFDerivWithin_sum_apply hU.uniqueDiffOn hz₀ fun i _ => hf i z₀ hz₀]
        _ ≤ ∑ i, ‖iteratedFDerivWithin ℝ b
              (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : I, 2 ^ b * T := Finset.sum_le_sum fun i _ => hfi i
        _ = (Fintype.card I : ℝ) * (2 ^ b * T) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((Fintype.card I : ℝ) * Kc * 2 ^ b) * (R ^ b * β * (lam * M) ^ (b + 1)) := by
            rw [hT]; ring
        _ ≤ R * (R ^ b * β * (lam * M) ^ (b + 1)) := mul_le_mul_of_nonneg_right hN hX
        _ = R ^ (b + 1) * β * (lam * M) ^ (b + 1) := by ring
  intro b hb H β hH hw
  have h0 : ‖H (Γ z₀)‖ ≤ β := by simpa using hw [] (Nat.zero_le _)
  have hβ : 0 ≤ β := (norm_nonneg _).trans h0
  calc _ ≤ R ^ b * β * (lam * M) ^ b := key b hb H β hH hw
    _ ≤ R ^ q * β * (lam * M) ^ b :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right_of_one_le hR hb) hβ)
          (pow_nonneg (mul_nonneg hlam0 hM0) _)

end words

end PI.UnitaryGroupMassFormula.UsCost.ZI
end
end

open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.ZI

variable (s : ℕ)

abbrev En : Type := (Fin s → ℂ) →L[ℝ] (Fin s → ℂ)

def act (Z : Fin s → Fin s → ℂ) : En s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (Matrix.of Z).mulVec v
      map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }

theorem act_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : act s Z v = (Matrix.of Z).mulVec v := rfl

def eA : (Fin s → Fin s → ℂ) →L[ℝ] En s :=
  LinearMap.toContinuousLinearMap
    { toFun := act s
      map_add' := fun Z Z' => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.add_apply]
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c Z => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        exact Matrix.smul_mulVec c (Matrix.of Z) v }

theorem eA_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : eA s Z v = (Matrix.of Z).mulVec v := rfl

def invF (Z : Fin s → Fin s → ℂ) : Fin s → Fin s → ℂ := Matrix.of.symm (Matrix.of Z)⁻¹

theorem eA_mul_inv {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    eA s Z * eA s (invF s Z) = 1 ∧ eA s (invF s Z) * eA s Z = 1 := by
  have hu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr h
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := Matrix.of.apply_symm_apply _
  constructor <;> ext1 v <;>
    simp only [ContinuousLinearMap.mul_apply, eA_apply, ContinuousLinearMap.one_apply,
      Matrix.mulVec_mulVec, hinv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]

theorem isUnit_eA {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) : IsUnit (eA s Z) :=
  ⟨⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩, rfl⟩

theorem inverse_eA {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    Ring.inverse (eA s Z) = eA s (invF s Z) := by
  exact Ring.inverse_unit ⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩

def lamL (a b : Fin s) (ε : Bool) (T : En s) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W => if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im
      map_add' := fun W W' => by
        have : (fun c => (W + W') c b) = (fun c => W c b) + (fun c => W' c b) := rfl
        rw [this, map_add (f := _)]
        cases ε <;> simp
      map_smul' := fun r W => by
        have : (fun c => (r • W) c b) = r • (fun c => W c b) := rfl
        rw [this, map_smul]
        cases ε <;> simp }

theorem lamL_apply (a b : Fin s) (ε : Bool) (T : En s) (W : Fin s → Fin s → ℂ) :
    lamL s a b ε T W = if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im := rfl

def lamF (i : Fin s × Fin s × Bool) : En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => lamL s i.1 i.2.1 i.2.2 T
      map_add' := fun T T' => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.add_apply]
        cases i.2.2 <;> simp
      map_smul' := fun c T => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        cases i.2.2 <;> simp }

def cF (i : Fin s × Fin s × Bool) (Z : Fin s → Fin s → ℂ) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  lamF s i (Ring.inverse (eA s Z))

theorem cF_apply (i : Fin s × Fin s × Bool) {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0)
    (W : Fin s → Fin s → ℂ) :
    cF s i Z W = if i.2.2 then (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).re
      else (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).im := by
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := Matrix.of.apply_symm_apply _
  rw [cF, inverse_eA s h]
  show lamL s i.1 i.2.1 i.2.2 (eA s (invF s Z)) W = _
  rw [lamL_apply, eA_apply, hinv]
  have e : ((Matrix.of Z)⁻¹.mulVec fun c => W c i.2.1) i.1
      = ((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1 := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [e]

theorem isOpen_det : IsOpen {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det (by exact continuous_id)) continuous_const

theorem contDiffOn_cF (i : Fin s × Fin s × Bool) (n : ℕ) :
    ContDiffOn ℝ n (cF s i) {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} := by
  have hinv : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x | IsUnit x} := fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt
  exact (lamF s i).contDiff.comp_contDiffOn
    (hinv.comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ))

theorem contDiffOn_inv (n : ℕ) : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x : En s | IsUnit x} :=
  fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt

theorem norm_inverse_le {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    ‖Ring.inverse (eA s Z)‖ ≤ ‖eA s‖ * ‖invF s Z‖ := by
  rw [inverse_eA s h]
  exact (eA s).le_opNorm _

theorem cF_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : Fin s → Fin s → ℂ, (Matrix.of Z).det ≠ 0 → ∀ i, ∀ a ≤ n,
    ‖iteratedFDeriv ℝ a (cF s i) Z‖ ≤ K * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
  set U := {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} with hU_def
  have hUo : IsOpen U := isOpen_det s
  let φ : (Fin s → Fin s → ℂ) → En s := fun Z => Ring.inverse (eA s Z)
  let P : (En s →L[ℝ] En s) →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (Fin s → Fin s → ℂ) (En s) (En s)).flip (eA s)
  let Bi : En s →L[ℝ] En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (En s) (En s →L[ℝ] En s) _ (-P)).comp
      (ContinuousLinearMap.mulLeftRight ℝ (En s))
  have hφ : ∀ m : ℕ, ContDiffOn ℝ m φ U := fun m =>
    (contDiffOn_inv s m).comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ)
  have hd : ∀ Z ∈ U, fderiv ℝ φ Z = Bi (φ Z) (φ Z) := by
    intro Z hZ
    obtain ⟨u, hu⟩ := isUnit_eA s hZ
    have h0 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h0
    have h1 := h0.comp Z (eA s).hasFDerivAt
    have hinv : ((u⁻¹ : (En s)ˣ) : En s) = φ Z := by
      show _ = Ring.inverse (eA s Z)
      rw [← hu, Ring.inverse_unit u]
    rw [show φ = Ring.inverse ∘ (eA s) from rfl, h1.fderiv, hinv]
    ext W : 1
    simp only [Bi, P, φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      Function.comp_apply]
  obtain ⟨K0, hK0, hb⟩ := quad_bound Bi hUo hφ hd n
  refine ⟨(∑ j, ‖lamF s j‖) * K0,
    mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hK0, ?_⟩
  intro Z hZ i a ha
  have hZU : Z ∈ U := hZ
  have hcf : cF s i = (lamF s i) ∘ φ := rfl
  have e1 : iteratedFDeriv ℝ a (cF s i) Z = iteratedFDerivWithin ℝ a (cF s i) U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have e2 : iteratedFDeriv ℝ a φ Z = iteratedFDerivWithin ℝ a φ U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have h3 : ‖iteratedFDerivWithin ℝ a (cF s i) U Z‖
      ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := by
    rw [hcf]
    exact (lamF s i).norm_iteratedFDerivWithin_comp_left (hφ a Z hZU) hUo.uniqueDiffOn hZU le_rfl
  have hLi : ‖lamF s i‖ ≤ ∑ j, ‖lamF s j‖ :=
    Finset.single_le_sum (f := fun j => ‖lamF s j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hM0 : 0 ≤ max 1 ‖φ Z‖ := le_trans zero_le_one (le_max_left _ _)
  have hM : max 1 ‖φ Z‖ ≤ max 1 ‖eA s‖ * max 1 ‖φ Z‖ :=
    le_mul_of_one_le_left hM0 (le_max_left _ _)
  have hL0 : 0 ≤ ∑ j, ‖lamF s j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [e1]
  calc _ ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := h3
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * max 1 ‖φ Z‖ ^ (a + 1)) := by
        rw [← e2]
        exact mul_le_mul hLi (hb Z hZU a ha) (norm_nonneg _) hL0
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * (max 1 ‖eA s‖ * max 1 ‖φ Z‖) ^ (a + 1)) := by
        gcongr
    _ = (∑ j, ‖lamF s j‖) * K0 * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
        ring

end PI.UnitaryGroupMassFormula.UsCost.ZI
end
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem list_prod_le_pow (l : List ℝ) (lam : ℝ) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ lam) :
    l.prod ≤ lam ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hp : 0 ≤ l.prod := List.prod_nonneg (fun y hy => (h y (List.mem_cons_of_mem x hy)).1)
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul hx.2 ih' hp (hx.1.trans hx.2)

theorem max_one_le (c t : ℝ) (ht : 1 ≤ t) (x : ℝ) (hx : x ≤ c * t) : max 1 x ≤ (1 + |c|) * t := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0
  have h2 : 0 ≤ |c| * t := mul_nonneg (abs_nonneg c) ht0
  refine max_le ?_ ?_ <;> nlinarith

theorem zeta_cost_of_smooth_deriv (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost := by
  intro hSM hRP hSZ hDP hS21 k p s ρ σ d hd hs K hK hK0 q
  obtain ⟨C₁, hC₁⟩ := hDS hDP k p s ρ σ
  obtain ⟨C₂, hC₂⟩ := hS21 k p s ρ σ d hd hs K hK hK0
  obtain ⟨Kc, hKc0, hKc⟩ := ZI.cF_bound s q
  obtain ⟨C, hC1, hC⟩ := ZI.iter_words (V := G.Mat s) (I := Fin s × Fin s × Bool) q Kc hKc0
  have hE'0 : (0 : ℝ) ≤ max 1 ‖ZI.eA s‖ := zero_le_one.trans (le_max_left _ _)
  set A : ℝ := (1 + |(|C₁| * C₂ ^ 4)|) * (max 1 ‖ZI.eA s‖ * (1 + |‖ZI.eA s‖ * C₂|)) with hA
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (mul_nonneg hE'0 (by positivity))
  refine ⟨C * A ^ q, ?_⟩
  intro E _ _ H β hH ξ Z γ hZ hγ hKg hw
  have hZ' : (Matrix.of Z).det ≠ 0 := hZ
  refine ⟨(hS hSM hRP k p s ρ σ d hd E H q hH ξ Z γ hZ hγ).2.2, ?_⟩
  obtain ⟨hg1, -, hRn, -, -, -, hb, -, -, -, -, hinv⟩ := hC₂ ξ Z γ hγ hKg
  set g := gaXi k ρ σ d ξ Z γ with hg
  set lam := max 1 (C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) with hlam
  set M := max 1 ‖ZI.eA s‖ * max 1 ‖Ring.inverse (ZI.eA s Z)‖ with hM
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  have hβ : 0 ≤ β := by
    have := hw [] (by simp) (by simp)
    simp only [List.map_nil, List.prod_nil, mul_one] at this
    exact (norm_nonneg _).trans this
  have hlet : ∀ i, inLieP k (p + s) ρ (dirZ k ρ ξ i) ∧ lsz (dirZ k ρ ξ i) ≤ lam := fun i =>
    ⟨(hC₁ ξ i).1, (hC₁ ξ i).2.trans (le_max_right _ _)⟩
  have key := hC (α := B.Mat k (p + s + ρ)) (E := E)
    (fun b H' => B.CkOn (b : ℕ∞) (B.GV k (p + s + ρ)) H')
    (fun i H' => RdV (dirZ k ρ ξ i) H') (fun Z' => gaXi k ρ σ d ξ Z' γ)
    {Z' : G.Mat s | (Matrix.of Z').det ≠ 0} (fun i => ZI.cF s i) Z M lam
    (ZI.isOpen_det s) hZ' hM1 hlam1
    (fun b H' h => P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_succ b) h)
    (fun b H' i h => by
      have h' : B.CkOn ((b : ℕ∞) + 1) (B.GV k (p + s + ρ)) H' := by simpa using h
      have := P.BetaSesquilinearity.CkOn_Dx (x := (false, dirZ k ρ ξ i)) (hlet i).1.1 h'
      simpa [P.BetaSesquilinearity.Dx] using this)
    (fun b H' h z hz => (hS hSM hRP k p s ρ σ d hd E H' b h ξ z γ hz hγ).2.2)
    (fun b H' h z hz => by
      ext1 W
      rw [hD hSM hRP hSZ k p s ρ σ d hd E H'
        (P.BetaSesquilinearity.CkOn_mono (by exact_mod_cast Nat.le_add_left 1 b) h) ξ z γ hz hγ W]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZI.cF_apply s i hz]
      rfl)
    (fun i n => ZI.contDiffOn_cF s i n)
    (fun i a ha => hKc Z hZ' i a ha)
    q le_rfl H β hH (fun w hwl => by
      have e : w.foldr (fun i H' => RdV (dirZ k ρ ξ i) H') H = B.Rw (w.map (dirZ k ρ ξ)) H := by
        simp [B.Rw, List.foldr_map]
      rw [e]
      refine (hw (w.map (dirZ k ρ ξ)) (fun X hX => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
          exact (hlet i).1) (by rw [List.length_map]; exact hwl)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hβ
      have := list_prod_le_pow ((w.map (dirZ k ρ ξ)).map lsz) lam (by
        intro x hx
        obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
        exact ⟨zero_le_one.trans (le_max_left _ _), (hlet i).2⟩)
      simpa using this)

  have hg0 : 0 ≤ B.gN g := by linarith
  have hR0 : 0 ≤ B.gN (Rn k (p + s) ρ ξ.1.2) := Real.sqrt_nonneg _
  have hlamb : lam ≤ (1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p) := by
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    have h1 : B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 ≤ (C₂ * B.gN g ^ (p + s)) ^ 2 := pow_le_pow_left₀ hR0 hRn 2
    have h2 : (1 + ‖ξ.2.1.2‖) ^ 2 ≤ (C₂ * B.gN g ^ p) ^ 2 := pow_le_pow_left₀ (by positivity) hb 2
    have hpow : B.gN g ^ (2 * (p + s) + 2 * p) = (B.gN g ^ (p + s)) ^ 2 * (B.gN g ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    calc C₁ * B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2
        = C₁ * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) := by ring
      _ ≤ |C₁| * (B.gN (Rn k (p + s) ρ ξ.1.2) ^ 2 * (1 + ‖ξ.2.1.2‖) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₁| * ((C₂ * B.gN g ^ (p + s)) ^ 2 * (C₂ * B.gN g ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) (abs_nonneg _)
      _ = (|C₁| * C₂ ^ 4) * B.gN g ^ (2 * (p + s) + 2 * p) := by rw [hpow]; ring
  have hMb : M ≤ max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hE'0
    refine max_one_le _ _ (one_le_pow₀ hg1) _ ?_
    calc ‖Ring.inverse (ZI.eA s Z)‖ ≤ ‖ZI.eA s‖ * ‖ZI.invF s Z‖ := ZI.norm_inverse_le s hZ'
      _ ≤ ‖ZI.eA s‖ * (C₂ * B.gN g ^ (p + s - 1)) := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = ‖ZI.eA s‖ * C₂ * B.gN g ^ (p + s - 1) := by ring
  have hLM : lam * M ≤ A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by
    calc lam * M ≤ ((1 + |(|C₁| * C₂ ^ 4)|) * B.gN g ^ (2 * (p + s) + 2 * p)) *
          (max 1 ‖ZI.eA s‖ * ((1 + |‖ZI.eA s‖ * C₂|) * B.gN g ^ (p + s - 1))) :=
          mul_le_mul hlamb hMb (by linarith) (by positivity)
      _ = A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1)) := by rw [hA, pow_add]; ring
  have hexp : (2 * (p + s) + 2 * p + (p + s - 1)) * q ≤ 5 * (p + s + ρ) * q :=
    Nat.mul_le_mul_right q (by omega)
  have hrp : B.gN g ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) = B.gN g ^ (5 * (p + s + ρ) * q) := by
    rw [← Real.rpow_natCast]; congr 1; push_cast; ring
  rw [hrp]
  calc ‖iteratedFDeriv ℝ q (fun Z' => H (gaXi k ρ σ d ξ Z' γ)) Z‖ ≤ C * β * (lam * M) ^ q := key
    _ ≤ C * β * (A * B.gN g ^ (2 * (p + s) + 2 * p + (p + s - 1))) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hLM q) (by positivity)
    _ = C * β * (A ^ q * B.gN g ^ ((2 * (p + s) + 2 * p + (p + s - 1)) * q)) := by rw [mul_pow, pow_mul]
    _ ≤ C * β * (A ^ q * B.gN g ^ (5 * (p + s + ρ) * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg1 hexp) (by positivity))
          (by positivity)
    _ = C * A ^ q * β * B.gN g ^ (5 * (p + s + ρ) * q) := by ring

end PI.UnitaryGroupMassFormula.UsCost
end
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

namespace PI.UnitaryGroupMassFormula.UsCost

theorem zCost_of (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost :=
  zeta_cost_of_smooth_deriv hS hD hDS

end PI.UnitaryGroupMassFormula.UsCost
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.UnitarySumCostOfParts
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem top_prod_map_le {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x ∧ f x ≤ c) (hc : 0 ≤ c) : (l.map f).prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 0 ≤ f a ∧ f a ≤ c := hf a (by simp)
    have ht : ∀ x ∈ t, 0 ≤ f x ∧ f x ≤ c := fun x hx => hf x (by simp [hx])
    have h0 : 0 ≤ (t.map f).prod := by
      apply List.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (ht x hx).1
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul ha.2 (ih ht) h0 hc

theorem top_lsz_ge_one {k r : ℕ} (X : B.Mat k r) : 1 ≤ lsz X := by
  unfold lsz
  exact le_max_left _ _

theorem top_prod_lsz_nonneg {k r : ℕ} (l : List (B.Mat k r)) : 0 ≤ (l.map lsz).prod := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 ha
  exact le_trans zero_le_one (top_lsz_ge_one X)

theorem top_gN_nonneg {k r : ℕ} (g : B.Mat k r) : 0 ≤ B.gN g := by
  unfold B.gN
  exact Real.sqrt_nonneg _

theorem unitarySum_cost_of_parts (hW : WordsId) (hL : LetterSize) (hS : StarScale) (hC : CommLR) (hO : OffK)
    (hZS : ZSmooth) (hZ : ZCost) : DerivativeCostFromComponents := by
  intro hM hR hRt hLt hZt hD hS21
  intro k p s ρ σ d hd hs K hK hKpos Q
  obtain ⟨CL, hCL⟩ := hL k (p + s) ρ
  obtain ⟨CS, hCS⟩ := hS21 k p s ρ σ d hd hs K hK hKpos
  choose Cz hCz using fun q : ℕ => hZ hM hR hZt hD hS21 k p s ρ σ d hd hs K hK hKpos q
  set C1 : ℝ := max 1 (CL * CS ^ 2) with hC1def
  have hC1ge : 1 ≤ C1 := le_max_left _ _
  refine ⟨(∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q, ?_⟩
  intro E _ _ F₁ A₁ B₁ hStar ξ u v q hu hv hq Z γ hZdet hγ
  let u' := u.map (cj k (p + s) ρ ξ.1.1)
  let v' := v.map (cj k (p + s) ρ ξ.1.2)
  let H : B.Mat k (p + s + ρ) → E := B.dLR u' v' F₁
  have hfun : (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) =
      fun Z' => H (gaXi k ρ σ d ξ Z' γ) := by
    funext Z'
    exact congrFun (hW hLt hRt k p s ρ σ d ξ Z' E F₁ u v) γ
  rw [hfun]
  have hcjP : ∀ (x : RC k (p + s) ρ) (Y : B.Mat k ρ), B.unitLie k ρ Y →
      inLieP k (p + s) ρ (cj k (p + s) ρ x Y) :=
    fun x Y hY => (hD k (p + s) ρ x).1 Y hY.1
  have hu' : ∀ X ∈ u', inLieP k (p + s) ρ X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact hcjP _ Y (hu Y hY)
  have hv' : ∀ X ∈ v', inLieP k (p + s) ρ X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact hcjP _ Y (hv Y hY)
  have hwl : ∀ x ∈ wL u' ++ wR v', B.inLie k (p + s + ρ) x.2 := by
    intro x hx
    simp only [List.mem_append, wL, wR, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu' X hX).1
    · exact (hv' X hX).1
  have hHeq : H = Dw (wL u' ++ wR v') F₁ := dLR_eq _ _ _
  have hg0 : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) :=
    (hZS hM hR k p s ρ σ d hd E F₁ Q hStar.1 ξ Z γ hZdet hγ).1
  have hB₁ : 0 ≤ B₁ := by
    have h0 := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) _ hg0
    exact le_trans (mul_nonneg (Real.rpow_nonneg (top_gN_nonneg _) _) (norm_nonneg _)) h0
  have hC0 : 0 ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q :=
    mul_nonneg (Finset.sum_nonneg fun q _ => le_max_right _ _) (pow_nonneg (le_trans zero_le_one hC1ge) _)
  by_cases hKg : ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K
  · obtain ⟨hg1, hRn1, hRn2, -⟩ := hCS ξ Z γ hγ hKg
    set g0 := gaXi k ρ σ d ξ Z γ with hg0def
    set X0 := B.gN g0 with hX0def
    have hX0pos : 0 < X0 := lt_of_lt_of_le zero_lt_one hg1
    have hX0nn : 0 ≤ X0 := hX0pos.le
    have hCkH : B.CkOn (q : ℕ∞) (B.GV k (p + s + ρ)) H := by
      rw [hHeq]
      apply CkOn_Dw hwl
      apply sCkOn_mono _ hStar.1
      have hl : q + (u.length + v.length) ≤ Q := by omega
      simp only [List.length_append, wL, wR, List.length_map, u', v']
      exact_mod_cast hl
    let β : ℝ := B₁ * X0 ^ (-A₁) * ((u'.map lsz).prod * (v'.map lsz).prod)
    have hw : ∀ w : List (B.Mat k (p + s + ρ)), (∀ X ∈ w, inLieP k (p + s) ρ X) → w.length ≤ q →
        ‖B.Rw w H g0‖ ≤ β * (w.map lsz).prod := by
      intro w hwP hwl'
      have hcomm := hC k (p + s + ρ) E F₁ Q hStar.1 u' v' w (fun X hX => (hu' X hX).1)
        (fun X hX => (hv' X hX).1) (fun X hX => (hwP X hX).1)
        (by simp only [List.length_map, u', v']; omega) g0 hg0
      rw [hcomm]
      have hsc := hS k (p + s) ρ E F₁ A₁ Q B₁ K hStar u' (w ++ v') hu'
        (by
          intro X hX
          rcases List.mem_append.1 hX with h | h
          · exact hwP X h
          · exact hv' X h)
        (by simp only [List.length_append, List.length_map, u', v']; omega) g0 hg0
      have hprod : ((u' ++ (w ++ v')).map lsz).prod =
          (u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod) := by
        simp only [List.map_append, List.prod_append]
      rw [hprod] at hsc
      have hpowpos : 0 < X0 ^ A₁ := Real.rpow_pos_of_pos hX0pos _
      have hle : ‖B.dLR u' (w ++ v') F₁ g0‖ ≤
          B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁ := by
        rw [le_div_iff₀ hpowpos]
        linarith [hsc]
      calc ‖B.dLR u' (w ++ v') F₁ g0‖
          ≤ B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁ := hle
        _ = β * (w.map lsz).prod := by
          simp only [β]
          rw [Real.rpow_neg hX0nn]
          field_simp
    obtain ⟨hcd, hbd⟩ := hCz q E H β hCkH ξ Z γ hZdet hγ hKg hw
    refine ⟨hcd, le_trans hbd ?_⟩
    have hlet : ∀ x : RC k (p + s) ρ, B.gN (Rn k (p + s) ρ x) ≤ CS * X0 ^ (p + s) →
        ∀ Y, B.unitLie k ρ Y → lsz (cj k (p + s) ρ x Y) ≤ C1 * X0 ^ (2 * (p + s + ρ)) := by
      intro x hx Y hY
      have h1 := hCL x Y hY.2
      have hn0 : 0 ≤ B.gN (Rn k (p + s) ρ x) := top_gN_nonneg _
      have hl1 := top_lsz_ge_one (cj k (p + s) ρ x Y)
      have hCL0 : 0 ≤ CL := by nlinarith [sq_nonneg (B.gN (Rn k (p + s) ρ x))]
      have hsq : B.gN (Rn k (p + s) ρ x) ^ 2 ≤ (CS * X0 ^ (p + s)) ^ 2 := pow_le_pow_left₀ hn0 hx 2
      calc lsz (cj k (p + s) ρ x Y) ≤ CL * B.gN (Rn k (p + s) ρ x) ^ 2 := h1
        _ ≤ CL * (CS * X0 ^ (p + s)) ^ 2 := mul_le_mul_of_nonneg_left hsq hCL0
        _ = (CL * CS ^ 2) * X0 ^ (2 * (p + s)) := by ring
        _ ≤ C1 * X0 ^ (2 * (p + s + ρ)) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hg1 (by omega)) (pow_nonneg hX0nn _)
            (le_trans zero_le_one hC1ge)
    have hc : 0 ≤ C1 * X0 ^ (2 * (p + s + ρ)) :=
      mul_nonneg (le_trans zero_le_one hC1ge) (pow_nonneg hX0nn _)
    have hu'b : (u'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ u.length := by
      have h := top_prod_map_le u' lsz (C1 * X0 ^ (2 * (p + s + ρ)))
        (fun X hX => by
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact ⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn1 Y (hu Y hY)⟩) hc
      simpa only [List.length_map, u'] using h
    have hv'b : (v'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ v.length := by
      have h := top_prod_map_le v' lsz (C1 * X0 ^ (2 * (p + s + ρ)))
        (fun X hX => by
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact ⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn2 Y (hv Y hY)⟩) hc
      simpa only [List.length_map, v'] using h
    have hβ : β ≤ B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length))) := by
      have h1 : (u'.map lsz).prod * (v'.map lsz).prod ≤
          (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) := by
        rw [pow_add]
        exact mul_le_mul hu'b hv'b (top_prod_lsz_nonneg _) (pow_nonneg hc _)
      have h2 : (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) ≤
          C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)) := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1ge (by omega)) (pow_nonneg hX0nn _)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))
    have hβ0 : 0 ≤ β :=
      mul_nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))
        (mul_nonneg (top_prod_lsz_nonneg _) (top_prod_lsz_nonneg _))
    have hX5 : 0 ≤ X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) := Real.rpow_nonneg hX0nn _
    have hexp : X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) +
          2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) =
        X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) *
          X0 ^ (2 * (p + s + ρ) * (u.length + v.length)) := by
      rw [Real.rpow_add hX0pos, Real.rpow_add hX0pos, ← Real.rpow_natCast]
      congr 2
      push_cast
      ring
    have hmax : max (Cz q) 0 ≤ ∑ q ∈ Finset.range (Q + 1), max (Cz q) 0 :=
      Finset.single_le_sum (f := fun q => max (Cz q) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_range.mpr (by omega))
    calc Cz q * β * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ))
        ≤ max (Cz q) 0 * β * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hβ0) hX5
      _ ≤ max (Cz q) 0 * (B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)))) *
            X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (le_max_right _ _)) hX5
      _ = max (Cz q) 0 * C1 ^ Q * B₁ * (X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) *
            X0 ^ (2 * (p + s + ρ) * (u.length + v.length))) := by ring
      _ = max (Cz q) 0 * C1 ^ Q * B₁ * X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) +
            2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) := by rw [hexp]
      _ ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q * B₁ * X0 ^ (-A₁ +
            5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) + 2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0nn _)
          apply mul_le_mul_of_nonneg_right _ hB₁
          exact mul_le_mul_of_nonneg_right hmax (pow_nonneg (le_trans zero_le_one hC1ge) _)
  · have hcont : Continuous fun g : B.Mat k (p + s + ρ) => ‖DjU k (p + s) ρ g‖ := by
      have hZc : Continuous fun g : B.Mat k (p + s + ρ) => Zh k (p + s) ρ g :=
        continuous_pi fun a => continuous_pi fun b => (continuous_apply _).comp (continuous_apply _)
      exact hZc.matrix_det.norm
    have hOopen : IsOpen {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} :=
      hK.isClosed.isOpen_compl.preimage hcont
    have hF0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} →
        F₁ g = 0 := by
      intro g hg hgO
      by_contra hne
      exact hgO (hStar.2.1 g hg hne)
    have hH0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} →
        H g = 0 := by
      intro g hg hgO
      rw [hHeq]
      exact Dw_vanish hOopen hwl hF0 g hg hgO
    obtain ⟨hcd, hz⟩ := hO hM hR k p s ρ σ d hd E H _ hOopen hH0 ξ Z γ hZdet hγ hKg q
    refine ⟨hcd, ?_⟩
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 hB₁) (Real.rpow_nonneg (top_gN_nonneg _) _)

end PI.UnitaryGroupMassFormula.UsCost
end
end

theorem operator_word_cost : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents :=
  PI.UnitaryGroupMassFormula.UsCost.unitarySum_cost_of_parts PI.UnitaryGroupMassFormula.UsCost.wordsId PI.UnitaryGroupMassFormula.UsCost.letterSize PI.UnitaryGroupMassFormula.UsCost.starScale
    PI.UnitaryGroupMassFormula.UsCost.commLR PI.UnitaryGroupMassFormula.UsCost.offK PI.UnitaryGroupMassFormula.UsCost.zSmooth
    (PI.UnitaryGroupMassFormula.UsCost.zCost_of PI.UnitaryGroupMassFormula.UsCost.zSmooth PI.UnitaryGroupMassFormula.UsCost.zDeriv PI.UnitaryGroupMassFormula.UsCost.dirSize)
