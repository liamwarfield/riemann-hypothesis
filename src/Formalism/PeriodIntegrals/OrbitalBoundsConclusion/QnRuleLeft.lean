module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.MulApplyS

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.LeftMultiplicationRule
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.HasDerivAtPhase
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.ReflectionColumnDualIsotropic
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

lemma tau_val (i : Fin (2 * r + k + 1)) :
    (tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

lemma tau_e (l : Fin r) : tau k r (eI k r l) = esI k r l := by
  apply Fin.ext; rw [tau_val, eI_val, esI_val]; have := l.isLt; split_ifs <;> omega

lemma tau_es (l : Fin r) : tau k r (esI k r l) = eI k r l := by
  apply Fin.ext; rw [tau_val, eI_val, esI_val]; have := l.isLt; split_ifs <;> omega

lemma sgn_e (l : Fin r) : WeylGroupFacts.sgn k r (eI k r l) = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg]; rw [eI_val]; have := l.isLt; omega

lemma sgn_es (l : Fin r) : WeylGroupFacts.sgn k r (esI k r l) = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg]; rw [esI_val]; have := l.isLt; omega

lemma star_sgn (i : Fin (2 * r + k + 1)) : star (WeylGroupFacts.sgn k r i) = WeylGroupFacts.sgn k r i := by
  unfold WeylGroupFacts.sgn; split_ifs <;> simp

lemma e_ne_es (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h; have := congrArg Fin.val h; rw [eI_val, esI_val] at this; have := l.isLt; omega

lemma reflection_off_support (l : Fin r) (c : ℂ) (p q : Fin (2 * r + k + 1)) (hq1 : q ≠ eI k r l)
    (hq2 : q ≠ esI k r l) : w1 k r l c p q = if p = q then 1 else 0 := by
  unfold w1
  by_cases hpq : p = q
  · subst hpq; simp [hq1, hq2]
  · simp [hpq, hq1, hq2]

lemma reflection_off_support_row (l : Fin r) (c : ℂ) (p q : Fin (2 * r + k + 1)) (hp1 : p ≠ eI k r l)
    (hp2 : p ≠ esI k r l) : w1 k r l c p q = if p = q then 1 else 0 := by
  unfold w1
  by_cases hpq : p = q
  · subst hpq; simp [hp1, hp2]
  · simp [hpq, hp1, hp2]

lemma reflection_column_isotropic (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) :
    w1 k r l c p (eI k r l) = if p = esI k r l then c else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hp : p = esI k r l
  · subst hp; simp
  · by_cases hp' : p = eI k r l
    · subst hp'; simp [hp, hne]
    · simp [hp, hp']

lemma reflection_column_dual_isotropic (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) :
    w1 k r l c p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hp : p = eI k r l
  · subst hp; simp [hne.symm]
  · by_cases hp' : p = esI k r l
    · subst hp'; simp [hp, hne.symm]
    · simp [hp, hp']

lemma weyl_cell_apply_basis (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (eI k r l) q = if q = esI k r l then (star c)⁻¹ else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hq : q = esI k r l
  · subst hq; simp [hne]
  · simp [hq, hne]

lemma weyl_cell_apply_dual_basis (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (esI k r l) q = if q = eI k r l then c else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hq : q = eI k r l
  · subst hq; simp
  · simp [hq, hne.symm]

lemma reflection_mul_star (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c * w1 k r l (star c) = 1 := by
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [Finset.sum_eq_single (esI k r l)]
    · rw [reflection_column_isotropic, if_pos rfl, reflection_column_dual_isotropic]
      by_cases hp : p = eI k r l
      · rw [if_pos hp, if_pos hp, inv_mul_cancel₀ hsc]
      · rw [if_neg hp, if_neg hp, zero_mul]
    · intro t _ ht; rw [reflection_column_isotropic, if_neg ht, mul_zero]
    · simp
  · by_cases hq2 : q = esI k r l
    · subst hq2
      rw [Finset.sum_eq_single (eI k r l)]
      · rw [reflection_column_dual_isotropic, if_pos rfl, reflection_column_isotropic, star_star]
        by_cases hp : p = esI k r l
        · rw [if_pos hp, if_pos hp, mul_inv_cancel₀ hc]
        · rw [if_neg hp, if_neg hp, zero_mul]
      · intro t _ ht; rw [reflection_column_dual_isotropic, if_neg ht, mul_zero]
      · simp
    · rw [Finset.sum_eq_single q]
      · rw [reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one, reflection_off_support _ _ p q hq1 hq2]
      · intro t _ ht; rw [reflection_off_support _ _ t q hq1 hq2, if_neg ht, mul_zero]
      · simp

lemma weyl_cell_inv (l : Fin r) (c : ℂ) (hc : c ≠ 0) : (w1 k r l c)⁻¹ = w1 k r l (star c) :=
  Matrix.inv_eq_right_inv (reflection_mul_star l c hc)

lemma weyl_cell_mem_unitary (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  show (w1 k r l c)ᴴ * Hpk k r * w1 k r l c = Hpk k r
  ext p q
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [conjTranspose_apply, hpk_mul_apply]
  rw [hpk_row]
  by_cases hp1 : p = eI k r l
  · subst hp1
    rw [Finset.sum_eq_single (esI k r l)]
    · rw [reflection_column_isotropic, if_pos rfl, tau_es, sgn_es, weyl_cell_apply_basis, tau_e, sgn_e]
      by_cases hq : q = esI k r l
      · rw [if_pos hq, if_pos hq, one_mul, ← star_inv₀, ← star_mul, inv_mul_cancel₀ hc, star_one]
      · rw [if_neg hq, if_neg hq, mul_zero, mul_zero]
    · intro t _ ht; rw [reflection_column_isotropic, if_neg ht, star_zero, zero_mul]
    · simp
  · by_cases hp2 : p = esI k r l
    · subst hp2
      rw [Finset.sum_eq_single (eI k r l)]
      · rw [reflection_column_dual_isotropic, if_pos rfl, tau_e, sgn_e, weyl_cell_apply_dual_basis, tau_es, sgn_es]
        by_cases hq : q = eI k r l
        · rw [if_pos hq, if_pos hq, one_mul, star_inv₀, star_star, inv_mul_cancel₀ hc]
        · rw [if_neg hq, if_neg hq, mul_zero, mul_zero]
      · intro t _ ht; rw [reflection_column_dual_isotropic, if_neg ht, star_zero, zero_mul]
      · simp
    · have ht1 : tau k r p ≠ eI k r l := by
        intro h; apply hp2; rw [← tau_tau p, h, tau_e]
      have ht2 : tau k r p ≠ esI k r l := by
        intro h; apply hp1; rw [← tau_tau p, h, tau_es]
      rw [Finset.sum_eq_single p]
      · rw [reflection_off_support _ _ p p hp1 hp2, if_pos rfl, star_one, one_mul,
          reflection_off_support_row _ _ (tau k r p) q ht1 ht2]
        by_cases hq : q = tau k r p
        · rw [if_pos hq, if_pos hq.symm, mul_one]
        · rw [if_neg hq, if_neg (Ne.symm hq), mul_zero]
      · intro t _ ht; rw [reflection_off_support _ _ t p hp1 hp2, if_neg ht, star_zero, zero_mul]
      · simp

lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := isUnit_of_uh hg.1
  have key : ∀ b : Fin (2 * r + k + 1) → ℂ, g *ᵥ b = b → g⁻¹ *ᵥ b = b := by
    intro b hb
    calc g⁻¹ *ᵥ b = g⁻¹ *ᵥ (g *ᵥ b) := by rw [hb]
      _ = b := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hg.1, fun a ha => ⟨key _ (hg.2 a ha).1, key _ (hg.2 a ha).2⟩⟩

lemma glev_out {l : Fin r} {g : Mx k r} (hg : g ∈ Glev k r l.succ) (p : Fin (2 * r + k + 1))
    (hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val)) :
    (∀ q, g p q = if p = q then 1 else 0) ∧ (∀ q, g q p = if q = p then 1 else 0) := by
  have hl := l.isLt
  by_cases h1 : p.val ≤ l.val
  · let a : Fin r := ⟨p.val, by omega⟩
    have hpa : eI k r a = p := Fin.ext rfl
    have ha : a.val < l.succ.val := by simp [a]; omega
    have hc1 := col_of_fix (hg.2 a ha).1
    have hc2 := col_of_fix (hg.2 a ha).2
    have hrow := row_of_fixed_col hg.1 (esI k r a) hc2
    rw [tau_es, hpa] at hrow
    rw [hpa] at hc1
    exact ⟨hrow, hc1⟩
  · let a : Fin r := ⟨2 * r + k - p.val, by omega⟩
    have hpa : esI k r a = p := by apply Fin.ext; rw [esI_val]; simp [a]; omega
    have ha : a.val < l.succ.val := by simp [a]; omega
    have hc1 := col_of_fix (hg.2 a ha).1
    have hc2 := col_of_fix (hg.2 a ha).2
    have hrow := row_of_fixed_col hg.1 (eI k r a) hc1
    rw [tau_e, hpa] at hrow
    rw [hpa] at hc2
    exact ⟨hrow, hc2⟩

lemma reflection_fixes_basis_vector (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) (hq1 : q ≠ eI k r l)
    (hq2 : q ≠ esI k r l) : w1 k r l c *ᵥ bvec q = bvec q := by
  funext p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one]
  rw [reflection_off_support _ _ p q hq1 hq2, Pi.single_apply]

lemma wg_glev (l : Fin r) (c : ℂ) (hc : c ≠ 0) {g₁ : Mx k r} (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l c * g₁ ∈ Glev k r l.castSucc := by
  refine ⟨uh_mul (weyl_cell_mem_unitary l c hc) hg.1, fun a ha => ?_⟩
  have hal : a.val < l.val := by simpa using ha
  have ha' : a.val < l.succ.val := by simp; omega
  have hl := l.isLt
  obtain ⟨h1, h2⟩ := hg.2 a ha'
  constructor
  · rw [← Matrix.mulVec_mulVec, h1]
    apply reflection_fixes_basis_vector
    · intro h; have := congrArg Fin.val h; rw [eI_val, eI_val] at this; omega
    · intro h; have := congrArg Fin.val h; rw [eI_val, esI_val] at this; omega
  · rw [← Matrix.mulVec_mulVec, h2]
    apply reflection_fixes_basis_vector
    · intro h; have := congrArg Fin.val h; rw [esI_val, eI_val] at this; omega
    · intro h; have := congrArg Fin.val h; rw [esI_val, esI_val] at this; omega

lemma weyl_cell_mul_apply (l : Fin r) (c : ℂ) (A : Mx k r) (p q : Fin (2 * r + k + 1))
    (h1 : A (eI k r l) q = 0) (h2 : A (esI k r l) q = 0) : (w1 k r l c * A) p q = A p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · by_cases hp1 : p = eI k r l
    · subst hp1; rw [h1, mul_zero]
    · by_cases hp2 : p = esI k r l
      · subst hp2; rw [h2, mul_zero]
      · rw [reflection_off_support _ _ p p hp1 hp2, if_pos rfl, one_mul]
  · intro t _ ht
    by_cases ht1 : t = eI k r l
    · subst ht1; rw [h1, mul_zero]
    · by_cases ht2 : t = esI k r l
      · subst ht2; rw [h2, mul_zero]
      · rw [reflection_off_support _ _ p t ht1 ht2, if_neg (Ne.symm ht), zero_mul]
  · simp

lemma mul_weyl_cell_apply (l : Fin r) (c : ℂ) (A : Mx k r) (p q : Fin (2 * r + k + 1))
    (h1 : A p (eI k r l) = 0) (h2 : A p (esI k r l) = 0) : (A * w1 k r l c) p q = A p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · by_cases hq1 : q = eI k r l
    · subst hq1; rw [h1, zero_mul]
    · by_cases hq2 : q = esI k r l
      · subst hq2; rw [h2, zero_mul]
      · rw [reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one]
  · intro t _ ht
    by_cases ht1 : t = eI k r l
    · subst ht1; rw [h1, zero_mul]
    · by_cases ht2 : t = esI k r l
      · subst ht2; rw [h2, zero_mul]
      · rw [reflection_off_support_row _ _ t q ht1 ht2, if_neg ht, mul_zero]
  · simp

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
end
end

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

lemma hinv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)

lemma hH2 (X : Mx k r) : Hpk k r * (Hpk k r * X) = X := by
  rw [← mul_assoc, Formalism.QuantumDeterminants.GBasic.Hpk_sq k r, one_mul]

lemma uh_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [mul_assoc]
    _ = 1 := by rw [hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq k r]

lemma dag_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    g * (Hpk k r * Zᴴ * Hpk k r) * g⁻¹ = Hpk k r * (g * Z * g⁻¹)ᴴ * Hpk k r := by
  rw [uh_inv_eq hg]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc, hH2]

lemma hpart1_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    g * hpart1 (Hpk k r) Z * g⁻¹ = hpart1 (Hpk k r) (g * Z * g⁻¹) := by
  simp only [hpart1, hinv]
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, dag_conj hg]

lemma hpart2_conj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (Z : Mx k r) :
    g * hpart2 (Hpk k r) Z * g⁻¹ = hpart2 (Hpk k r) (g * Z * g⁻¹) := by
  simp only [hpart2, hinv]
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, dag_conj hg]

lemma dagdag (M : Mx k r) : Hpk k r * (Hpk k r * Mᴴ * Hpk k r)ᴴ * Hpk k r = M := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc, hH2,
    Formalism.QuantumDeterminants.GBasic.Hpk_sq, mul_one]

lemma hpart1_skew (Z : Mx k r) :
    Hpk k r * (hpart1 (Hpk k r) Z)ᴴ * Hpk k r = -hpart1 (Hpk k r) Z := by
  simp only [hpart1, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, dagdag]
  ext i j
  simp
  ring

lemma hpart2_skew (Z : Mx k r) :
    Hpk k r * (hpart2 (Hpk k r) Z)ᴴ * Hpk k r = -hpart2 (Hpk k r) Z := by
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg,
      one_div_neg_eq_neg_one_div]
  simp only [hpart2, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, dagdag, hc]
  rw [neg_smul, add_comm (Hpk k r * Zᴴ * Hpk k r) Z]

lemma exp_uh {Y : Mx k r} (hY : Hpk k r * Yᴴ * Hpk k r = -Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ UH (Hpk k r) := by
  have hH := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hU : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, hH, hH⟩, rfl⟩
  have hY' : Yᴴ = Hpk k r * -Y * Hpk k r := by
    rw [← hY]
    simp only [← mul_assoc, hH, one_mul]
    rw [mul_assoc, hH, mul_one]
  have hYH : ((t : ℂ) • Y)ᴴ = Hpk k r * -((t : ℂ) • Y) * (Hpk k r)⁻¹ := by
    rw [hinv, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hY']
    simp only [smul_neg, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  show (NormedSpace.exp ((t : ℂ) • Y))ᴴ * Hpk k r * NormedSpace.exp ((t : ℂ) • Y) = Hpk k r
  rw [← Matrix.exp_conjTranspose, hYH, Matrix.exp_conj _ _ hU, hinv]
  simp only [mul_assoc]
  rw [← mul_assoc (Hpk k r) (Hpk k r), hH, one_mul,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • Y))), neg_add_cancel,
    NormedSpace.exp_zero, mul_one]

lemma dag_apply (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Mᴴ * Hpk k r) p q =
      WeylGroupFacts.sgn k r p * (star (M (tau k r q) (tau k r p)) * WeylGroupFacts.sgn k r q) := by
  have hs : ∀ i, star (WeylGroupFacts.sgn k r i) = WeylGroupFacts.sgn k r i := by
    intro i; unfold WeylGroupFacts.sgn; split_ifs <;> simp
  have e : Mᴴ * Hpk k r = (Hpk k r * M)ᴴ := by
    rw [Matrix.conjTranspose_mul, Formalism.QuantumDeterminants.GBasic.Hpk_herm]
  rw [mul_assoc, hpk_mul_apply, e, Matrix.conjTranspose_apply, hpk_mul_apply, star_mul', hs]
  ring

lemma inS_dag {l : Fin r} {M : Mx k r} (hM : InS k r l M) : InS k r l (Hpk k r * Mᴴ * Hpk k r) := by
  unfold InS at hM ⊢
  intro p q hpq
  rw [dag_apply, hM (tau k r q) (tau k r p) ?_, star_zero, zero_mul, mul_zero]
  intro h
  apply hpq
  unfold SP at h ⊢
  simp only [tau, Fin.val_mk] at h
  have hl := l.isLt
  have hp := p.isLt
  have hq := q.isLt
  split_ifs at h <;> omega

lemma hasDerivAt_phase (A B : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (((cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B)).re : ℝ) : ℂ)))
      (Complex.I * (((cStd * A).re : ℝ) : ℂ)) 0 := by
  have e : ∀ t : ℝ, (cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B)).re = t * (cStd * A).re + t ^ 2 * (cStd * B).re := by
    intro t
    have h : cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B) = (t : ℂ) * (cStd * A) + ((t ^ 2 : ℝ) : ℂ) * (cStd * B) := by
      push_cast; ring
    rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp_rw [e]
  have ha : HasDerivAt (fun t : ℝ => t * (cStd * A).re) (1 * (cStd * A).re) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul_const _
  have hb : HasDerivAt (fun t : ℝ => t ^ 2 * (cStd * B).re) (((2 : ℕ) : ℝ) * (0 : ℝ) ^ (2 - 1) * (cStd * B).re) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  have h1 : HasDerivAt (fun t : ℝ => t * (cStd * A).re + t ^ 2 * (cStd * B).re) ((cStd * A).re) 0 :=
    (ha.add hb).congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul Complex.I).cexp
  exact h2.congr_deriv (by simp)

lemma rdV_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (X : Mx k r) (hS : InS k r l (g * X * g⁻¹))
    (hk : Hpk k r * (g * X * g⁻¹)ᴴ * Hpk k r = -(g * X * g⁻¹)) :
    RdV X f g = (Complex.I * (((cStd * ell k r z (g * X * g⁻¹)).re : ℝ) : ℂ)) • f g := by
  have ell_sm : ∀ (c : ℂ) (M : Mx k r), ell k r z (c • M) = c * ell k r z M := by
    intro c M
    simp only [ell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  obtain ⟨hgG, hgD⟩ := hg
  have hgU : g ∈ UH (Hpk k r) := by
    have h := hgG
    simp only [Glev, Set.mem_setOf_eq] at h
    exact h.1
  have hleft : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hgU
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [mul_assoc]
      _ = 1 := by rw [hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq k r]
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse hleft
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hdet
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  set Y := g * X * g⁻¹ with hYdef
  have hconj : ∀ u : ℝ, g * NormedSpace.exp ((u : ℂ) • X) = NormedSpace.exp ((u : ℂ) • Y) * g := by
    intro u
    have h1 : (u : ℂ) • Y = g * ((u : ℂ) • X) * g⁻¹ := by
      rw [hYdef, mul_smul_comm, smul_mul_assoc]
    rw [h1, Matrix.exp_conj _ _ hU, mul_assoc, hgi, mul_one]
  have hSu : ∀ u : ℝ, InS k r l ((u : ℂ) • Y) := fun u => inS_smul _ hS
  have hmemN : ∀ u : ℝ, NormedSpace.exp ((u : ℂ) • Y) ∈ Nlev k r l.castSucc := by
    intro u
    have hUu := exp_uh hk u
    rw [exp_S (hSu u)] at hUu ⊢
    exact memN_S (hSu u) hUu
  have hfe : ∀ u : ℝ, f (g * NormedSpace.exp ((u : ℂ) • X)) =
      psi k r z cStd (NormedSpace.exp ((u : ℂ) • Y)) • f g := by
    intro u
    rw [hconj u]
    exact hL g ⟨hgG, hgD⟩ _ (hmemN u)
  have hell : ∀ u : ℝ, ell k r z (NormedSpace.exp ((u : ℂ) • Y)) =
      (u : ℂ) * ell k r z Y + (u : ℂ) ^ 2 * ((1 / 2 : ℂ) * ell k r z (Y * Y)) := by
    intro u
    rw [exp_S (hSu u), ell_add, ell_add, ell_one z hz]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ell_sm]
    ring
  have hfun : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =
      fun u : ℝ => Complex.exp (Complex.I * (((cStd * ((u : ℂ) * ell k r z Y +
        (u : ℂ) ^ 2 * ((1 / 2 : ℂ) * ell k r z (Y * Y)))).re : ℝ) : ℂ)) • f g := by
    funext u
    rw [hfe u, ← hell u]
    rfl
  have hd := (hasDerivAt_phase (ell k r z Y) ((1 / 2 : ℂ) * ell k r z (Y * Y))).smul_const (f g)
  show deriv (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0 = _
  rw [hfun]
  exact hd.deriv

lemma phase_sum (A B : ℂ) :
    Complex.I * (((cStd * ((1 / 2 : ℂ) * (A - B))).re : ℝ) : ℂ) +
      Complex.I * (Complex.I * (((cStd * ((1 / (2 * Complex.I) : ℂ) * (A + B))).re : ℝ) : ℂ)) = A + star B := by
  have h1 : cStd * ((1 / 2 : ℂ) * (A - B)) = -Complex.I * (A - B) := by
    simp only [cStd]; ring
  have h2 : cStd * ((1 / (2 * Complex.I) : ℂ) * (A + B)) = -(A + B) := by
    simp only [cStd]; field_simp
  rw [h1, h2]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (a b : Fin (2 * r + k + 1))
    (hS : InS k r l (g * Matrix.single a b 1 * g⁻¹)) :
    EH k r a b f g = (ell k r z (g * Matrix.single a b 1 * g⁻¹) +
      star (ell k r z (Hpk k r * (g * Matrix.single a b 1 * g⁻¹)ᴴ * Hpk k r))) • f g := by
  have ell_sm : ∀ (c : ℂ) (M : Mx k r), ell k r z (c • M) = c * ell k r z M := by
    intro c M
    simp only [ell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  set W := g * Matrix.single a b 1 * g⁻¹ with hW
  have hgU : g ∈ UH (Hpk k r) := by
    have h := hg.1
    simp only [Glev, Set.mem_setOf_eq] at h
    exact h.1
  have hp1 : hpart1 (Hpk k r) W = (1 / 2 : ℂ) • (W - Hpk k r * Wᴴ * Hpk k r) := by
    simp only [hpart1, hinv]
  have hp2 : hpart2 (Hpk k r) W = (1 / (2 * Complex.I) : ℂ) • (W + Hpk k r * Wᴴ * Hpk k r) := by
    simp only [hpart2, hinv]
  have hS1 : InS k r l (g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart1_conj hgU, ← hW, hp1]
    exact inS_smul _ (inS_sub hS (inS_dag hS))
  have hS2 : InS k r l (g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart2_conj hgU, ← hW, hp2]
    exact inS_smul _ (inS_add hS (inS_dag hS))
  have hk1 : Hpk k r * (g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹)ᴴ * Hpk k r =
      -(g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart1_conj hgU]; exact hpart1_skew _
  have hk2 : Hpk k r * (g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹)ᴴ * Hpk k r =
      -(g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart2_conj hgU]; exact hpart2_skew _
  have r1 := rdV_left hz hL hg _ hS1 hk1
  have r2 := rdV_left hz hL hg _ hS2 hk2
  rw [hpart1_conj hgU, ← hW] at r1
  rw [hpart2_conj hgU, ← hW] at r2
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f g +
    Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f g = _
  rw [r1, r2, smul_smul, ← add_smul, hp1, hp2, ell_sm, ell_sm]
  congr 1
  have hsub : ell k r z (W - Hpk k r * Wᴴ * Hpk k r) = ell k r z W - ell k r z (Hpk k r * Wᴴ * Hpk k r) := by
    rw [sub_eq_add_neg, ell_add, ← neg_one_smul ℂ (Hpk k r * Wᴴ * Hpk k r), ell_sm]; ring
  rw [hsub, ell_add]
  exact phase_sum _ _

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
end
end

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

lemma single_conj (A B : Mx k r) (a b p q : Fin (2 * r + k + 1)) :
    ((A * Matrix.single a b 1 * B : Mx k r)) p q = A p a * B b q := by
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val]
  split_ifs <;> first | rfl | omega | norm_num

lemma hpkVec (u : Fin (2 * r + k + 1) → ℂ) (s : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) s = WeylGroupFacts.sgn k r s * u (tau k r s) := by
  simp only [Matrix.mulVec, dotProduct, hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma posL_in (l : Fin r) (j : Fin (mdim k r l.succ)) :
    l.val < (posL k r l.succ j).val ∧ (posL k r l.succ j).val < 2 * r + k - l.val := by
  have hj := j.isLt
  have hl := l.isLt
  unfold mdim at hj
  show l.val < j.val + l.succ.val ∧ j.val + l.succ.val < 2 * r + k - l.val
  simp only [Fin.val_succ] at hj ⊢
  omega

lemma fvec_es {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (l : Fin r) :
    fvec k r z l.succ (esI k r l) = 0 := by
  have hl := l.isLt
  unfold fvec
  split_ifs with h
  · simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h'
    have h'' := congrArg Fin.val h'
    simp only [eI, esI, Fin.val_succ] at h'' h
    omega
  · apply hz
    right
    show r + k < 2 * r + k - l.val
    omega

lemma ell_form {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {l : Fin r} {M : Mx k r}
    (hM : InS k r l M) : ell k r z M = ∑ q, M (eI k r l) q * fvec k r z l.succ q := by
  have hl := l.isLt
  unfold ell
  rw [Finset.sum_eq_single l]
  · split_ifs with h
    · unfold fvec
      rw [dite_eq_left (show l.succ.val < r by simp only [Fin.val_succ]; exact h)]
      simp only [bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · unfold fvec
      rw [dite_eq_right (show ¬ l.succ.val < r by simp only [Fin.val_succ]; exact h)]
      rfl
  · intro a _ hal
    have hal' : a.val ≠ l.val := Fin.val_ne_of_ne hal
    have hal2 := a.isLt
    split_ifs with h
    · apply hM
      intro hs
      unfold SP at hs
      simp only [eI] at hs
      omega
    · simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      have hq2 := q.isLt
      by_cases hq : r + k < q.val
      · rw [hz q (Or.inr hq), mul_zero]
      · rw [hM _ _ ?_, zero_mul]
        intro hs
        unfold SP at hs
        simp only [eI] at hs
        omega
  · intro h
    exact absurd (Finset.mem_univ l) h

private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val]
  split_ifs <;> omega

private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val]
  split_ifs <;> first | rfl | omega

private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', tau_tau_lemma]

private lemma hpk_mul_conjTranspose_mul_hpk_apply (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Mᴴ * Hpk k r) p q =
      WeylGroupFacts.sgn k r p * star (M (tau k r q) (tau k r p)) * WeylGroupFacts.sgn k r q := by
  rw [Matrix.mul_apply]
  have inner : ∀ y, (Hpk k r * Mᴴ) p y = WeylGroupFacts.sgn k r p * star (M y (tau k r p)) := fun y => by
    rw [Matrix.mul_apply]
    simp only [hpk_eq_lemma, Matrix.conjTranspose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [inner, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma sp_of_sp_tau {l : Fin r} {p q : Fin (2 * r + k + 1)}
    (h : SP k r l (tau k r q) (tau k r p)) : SP k r l p q := by
  have hl := l.isLt
  have hp := p.isLt
  have hq := q.isLt
  have e1 := tau_val (k := k) (r := r) p
  have e2 := tau_val (k := k) (r := r) q
  unfold SP at h ⊢
  split_ifs at e1 e2 <;> omega

lemma ell_dag_form {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {l : Fin r} {M : Mx k r}
    (hM : InS k r l M) : ell k r z (Hpk k r * Mᴴ * Hpk k r) =
      ∑ q, star (M (tau k r q) (esI k r l)) * WeylGroupFacts.sgn k r q * fvec k r z l.succ q := by
  have hN : InS k r l (Hpk k r * Mᴴ * Hpk k r) := by
    intro p q hpq
    rw [hpk_mul_conjTranspose_mul_hpk_apply, hM _ _ (fun h => hpq (sp_of_sp_tau h)), star_zero, mul_zero, zero_mul]
  rw [ell_form hz hN]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hpk_mul_conjTranspose_mul_hpk_apply, tau_e, sgn_e, one_mul]

section Cases

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
  {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} {c : ℂ} {g₁ : Mx k r}

lemma ginv_eq (hc : c ≠ 0) : (w1 k r l c * g₁)⁻¹ = g₁⁻¹ * w1 k r l (star c) := by
  rw [Matrix.mul_inv_rev, weyl_cell_inv l c hc]

lemma e_out (l : Fin r) : ¬ (l.val < (eI k r l).val ∧ (eI k r l).val < 2 * r + k - l.val) := by
  intro h
  exact absurd h.1 (lt_irrefl _)

lemma es_out (l : Fin r) : ¬ (l.val < (esI k r l).val ∧ (esI k r l).val < 2 * r + k - l.val) := by
  intro h
  exact absurd h.2 (lt_irrefl _)

lemma case1 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) (v : Fin (2 * r + k + 1))
    (hv : l.val < v.val ∧ v.val < 2 * r + k - l.val) :
    EH k r v (eI k r l) f (w1 k r l c * g₁) =
      (c⁻¹ * herm (Hpk k r) (g₁ *ᵥ bvec v) (fvec k r z l.succ)) • f (w1 k r l c * g₁) := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hv1 : v ≠ eI k r l := fun h => by rw [h] at hv; exact e_out l hv
  have hv2 : v ≠ esI k r l := fun h => by rw [h] at hv; exact es_out l hv
  have hre := (glev_out hg₁ (eI k r l) (e_out l)).1
  have hres := (glev_out hg₁ (esI k r l) (es_out l)).1
  have h0e : g₁ (eI k r l) v = 0 := by rw [hre, if_neg (Ne.symm hv1)]
  have h0es : g₁ (esI k r l) v = 0 := by rw [hres, if_neg (Ne.symm hv2)]
  have hcol : ∀ p, (w1 k r l c * g₁) p v = g₁ p v := fun p => weyl_cell_mul_apply l c g₁ p v h0e h0es
  have hire := (glev_out hinv (eI k r l) (e_out l)).1
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) (eI k r l) q = if q = esI k r l then c⁻¹ else 0 :=
    fun q => by
      rw [Matrix.mul_apply]
      simp only [hire, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [weyl_cell_apply_basis, star_star]
  have hMe : ∀ p q, (w1 k r l c * g₁ * Matrix.single v (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      g₁ p v * (if q = esI k r l then c⁻¹ else 0) := fun p q => by
    rw [ginv_eq hc, single_conj, hcol, hB]
  have hS : InS k r l (w1 k r l c * g₁ * Matrix.single v (eI k r l) 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hq : q = esI k r l
    · have hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val) :=
        fun hp => hpq (Or.inr ⟨by rw [hq]; rfl, hp.1, hp.2⟩)
      rw [(glev_out hg₁ p hp).1 v, if_neg (fun (h : p = v) => hp (h ▸ hv)), zero_mul]
    · rw [if_neg hq, mul_zero]
  rw [core hz hL hg v (eI k r l) hS, ell_form hz hS, ell_dag_form hz hS]
  congr 1
  simp only [hMe, h0e, zero_mul, Finset.sum_const_zero, zero_add, eq_self_iff_true, if_true]
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  simp only [hpkVec]
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [star_mul', star_star, star_sgn]
  ring

lemma case2 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) (v : Fin (2 * r + k + 1))
    (hv : l.val < v.val ∧ v.val < 2 * r + k - l.val) :
    EH k r (esI k r l) v f (w1 k r l c * g₁) =
      ((star c)⁻¹ * (g₁⁻¹ *ᵥ fvec k r z l.succ) v) • f (w1 k r l c * g₁) := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hv1 : v ≠ eI k r l := fun h => by rw [h] at hv; exact e_out l hv
  have hv2 : v ≠ esI k r l := fun h => by rw [h] at hv; exact es_out l hv
  have hces := (glev_out hg₁ (esI k r l) (es_out l)).2
  have hice := (glev_out hinv (eI k r l) (e_out l)).2
  have hices := (glev_out hinv (esI k r l) (es_out l)).2
  have hA : ∀ p, (w1 k r l c * g₁) p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 :=
    fun p => by
      rw [Matrix.mul_apply]
      simp only [hces, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [reflection_column_dual_isotropic]
  have h0 : g₁⁻¹ v (esI k r l) = 0 := by rw [hices, if_neg hv2]
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) v q = g₁⁻¹ v q := fun q =>
    mul_weyl_cell_apply l (star c) g₁⁻¹ v q (by rw [hice, if_neg hv1]) h0
  have hMe : ∀ p q, (w1 k r l c * g₁ * Matrix.single (esI k r l) v 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      (if p = eI k r l then (star c)⁻¹ else 0) * g₁⁻¹ v q := fun p q => by
    rw [ginv_eq hc, single_conj, hA, hB]
  have hS : InS k r l (w1 k r l c * g₁ * Matrix.single (esI k r l) v 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hp : p = eI k r l
    · have hq : ¬ (l.val < q.val ∧ q.val < 2 * r + k - l.val) :=
        fun hq => hpq (Or.inl ⟨by rw [hp]; rfl, hq.1, le_of_lt hq.2⟩)
      rw [(glev_out hinv q hq).2 v, if_neg (fun (h : v = q) => hq (h ▸ hv)), mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [core hz hL hg (esI k r l) v hS, ell_form hz hS, ell_dag_form hz hS]
  congr 1
  simp only [hMe, h0, mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero, eq_self_iff_true,
    if_true]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

lemma case3 (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) :
    EH k r (esI k r l) (eI k r l) f (w1 k r l c * g₁) = 0 := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hre := (glev_out hg₁ (eI k r l) (e_out l)).1
  have hces := (glev_out hg₁ (esI k r l) (es_out l)).2
  have hire := (glev_out hinv (eI k r l) (e_out l)).1
  have hA : ∀ p, (w1 k r l c * g₁) p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 :=
    fun p => by
      rw [Matrix.mul_apply]
      simp only [hces, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [reflection_column_dual_isotropic]
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) (eI k r l) q = if q = esI k r l then c⁻¹ else 0 :=
    fun q => by
      rw [Matrix.mul_apply]
      simp only [hire, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [weyl_cell_apply_basis, star_star]
  have hMe : ∀ p q,
      (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      (if p = eI k r l then (star c)⁻¹ else 0) * (if q = esI k r l then c⁻¹ else 0) := fun p q => by
    rw [ginv_eq hc, single_conj, hA, hB]
  have hS : InS k r l
      (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hp : p = eI k r l
    · by_cases hq : q = esI k r l
      · exfalso
        apply hpq
        left
        subst hp
        subst hq
        exact ⟨rfl, show l.val < 2 * r + k - l.val by omega, le_refl _⟩
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [core hz hL hg (esI k r l) (eI k r l) hS, ell_form hz hS, ell_dag_form hz hS]
  have h1 : ∑ q, (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r)
      (eI k r l) q * fvec k r z l.succ q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [hMe, if_pos rfl]
    by_cases hq : q = esI k r l
    · rw [hq, fvec_es hz l, mul_zero]
    · rw [if_neg hq, mul_zero, zero_mul]
  have h2 : ∑ q, star ((w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 *
      (w1 k r l c * g₁)⁻¹ : Mx k r) (tau k r q) (esI k r l)) * WeylGroupFacts.sgn k r q * fvec k r z l.succ q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : q = esI k r l
    · rw [hq, fvec_es hz l, mul_zero]
    · rw [hMe, if_neg (fun h => hq (by rw [← tau_tau_lemma q, h, tau_e])), zero_mul, star_zero,
        zero_mul, zero_mul]
  rw [h1, h2, star_zero, add_zero, zero_smul]

end Cases

theorem left_multiplication_rule : RuleLeft := by
  intro E _ _ k r z l D f hz _ _ _ hL c hc g₁ hg₁ hgD
  refine ⟨fun j => ?_, fun j => ?_, case3 hz hL hc hg₁ hgD⟩
  · exact case1 hz hL hc hg₁ hgD _ (posL_in l j)
  · exact case2 hz hL hc hg₁ hgD _ (posL_in l j)

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
end
end

theorem qnRuleLeft : Formalism.FourierDecayAlt.Q.RuleLeft := Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
