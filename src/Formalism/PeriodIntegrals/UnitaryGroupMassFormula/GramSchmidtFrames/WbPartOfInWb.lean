module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.LocBCore

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.PhiMulVec
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca

variable {k r : ℕ}

lemma aps {V : Type*} [AddCommGroup V] (a b : V) : a + (b - a) = b := by
  exact add_sub_cancel a b

def Rk (k r : ℕ) (p q : Fin (2 * r + k + 1) → ℂ) : B.Mat k r := vecMulVec p (star q ᵥ* Hpk k r)

lemma Rk_mulVec (p q v : Fin (2 * r + k + 1) → ℂ) : Rk k r p q *ᵥ v = herm (Hpk k r) v q • p := by
  unfold Rk
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.dotProduct_mulVec]
  rfl

def Dw (k r : ℕ) : B.Mat k r := diagonal fun i => if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

lemma Dw_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Dw k r *ᵥ v = wbPart k r v := by
  funext i
  simp [Dw, Matrix.mulVec_diagonal, wbPart]

def Pm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Dw k r + ((Tz k r z : ℂ))⁻¹ • (Rk k r z z * Dw k r)

lemma Pm_mulVec (z v : Fin (2 * r + k + 1) → ℂ) : Pm k r z *ᵥ v = prW k r z v := by
  unfold Pm
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Dw_mulVec, Rk_mulVec, smul_smul]
  unfold prW
  rw [div_eq_inv_mul]

def wv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ := fun a => herm (Hpk k r) (M *ᵥ u) (fvec k r z a)

def gam (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  (-((Zhat k r z z' M).det)⁻¹) • ((Zhat k r z z' M).adjugate *ᵥ wv k r z M u)

def Lm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  1 + ∑ c : Fin (r + 1), ∑ a : Fin (r + 1),
    (-((Zhat k r z z' M).det)⁻¹ * (Zhat k r z z' M).adjugate c a) • (Rk k r (fvec k r z' c) (fvec k r z a) * M)

lemma Lm_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Lm k r z z' M *ᵥ u = u + ∑ c, gam k r z z' M u c • fvec k r z' c := by
  unfold Lm gam wv
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Rk_mulVec, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

def Phi (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  Pm k r z * M * Lm k r z z' M

lemma Phi_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Phi k r z z' M *ᵥ u = prW k r z (M *ᵥ (Lm k r z z' M *ᵥ u)) := by
  unfold Phi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pm_mulVec]

lemma s_msmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ} {c : E → ℂ}
    {M : E → Matrix (Fin m) (Fin m) ℂ} (hc : Sm c s) (hM : Sm M s) : Sm (fun x => c x • M x) s :=
  sm_iff.2 fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; exact hc.mul (sm_iff.1 hM i j)

end loca

end PI.UnitaryGroupMassFormula.GsFr
end
end

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca2

variable {k r : ℕ}

lemma Wsp_sub {z p q : Fin (2 * r + k + 1) → ℂ} (hp : p ∈ Wsp k r z) (hq : q ∈ Wsp k r z) : p - q ∈ Wsp k r z := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  show inWb k r (p - q) ∧ herm (Hpk k r) (p - q) z = 0
  refine ⟨fun i hi => by simp [hp1 i hi, hq1 i hi], ?_⟩
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub] at hp2 hq2 ⊢
  rw [hp2, hq2, sub_zero]

lemma Wsp_smul {z p : Fin (2 * r + k + 1) → ℂ} (c : ℂ) (hp : p ∈ Wsp k r z) : c • p ∈ Wsp k r z := by
  obtain ⟨hp1, hp2⟩ := hp
  show inWb k r (c • p) ∧ herm (Hpk k r) (c • p) z = 0
  refine ⟨fun i hi => by simp [hp1 i hi], ?_⟩
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul] at hp2 ⊢
  rw [hp2, smul_zero]

lemma wbPart_of_inWb {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : wbPart k r v = v := by
  funext i
  unfold wbPart
  split_ifs with h
  · rfl
  · symm
    exact hv i (by omega)

lemma prW_of_mem {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) : prW k r z q = q := by
  obtain ⟨h1, h2⟩ := hq
  unfold prW
  rw [wbPart_of_inWb h1, h2, zero_div, zero_smul, add_zero]

lemma sub_prW_X {z q : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z)
    (hq : ∀ a, herm (Hpk k r) q (fvec k r z a) = 0) : q - prW k r z q ∈ Xsp k r := by
  obtain ⟨hzw, -⟩ := hz
  have hqz : herm (Hpk k r) q z = 0 := by
    have := hq (Fin.last r)
    simpa [fvec] using this
  have hX : ∀ a : Fin r, q (esI k r a) = 0 := by
    intro a
    have ha := a.isLt
    have h := hq ⟨a.val, by omega⟩
    have hf : fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
      simp [fvec, ha]
    rw [hf] at h
    have hc : herm (Hpk k r) q (bvec (eI k r a)) = q (esI k r a) := by
      simp only [herm, bvec, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (eI k r a)]
      · rw [Finset.sum_eq_single (esI k r a)]
        · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
          dsimp only [Hpk, eI, esI]
          rw [if_pos ⟨ha, by omega⟩, one_mul]
        · intro j _ hj
          have hj' : (j : ℕ) ≠ 2 * r + k - a := fun h => hj (Fin.ext h)
          have hjl := j.isLt
          dsimp only [Hpk, eI]
          split_ifs <;> first | (exfalso; omega) | simp
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hc] at h
    exact h
  have hwb : herm (Hpk k r) (wbPart k r q) z = 0 := by
    have h1 : herm (Hpk k r) (q - wbPart k r q) z = 0 :=
      herm_out_wb (fun i hi1 hi2 => by simp [wbPart, hi1, hi2]) hzw
    have h2 : herm (Hpk k r) (q - wbPart k r q) z =
        herm (Hpk k r) q z - herm (Hpk k r) (wbPart k r q) z := by
      simp [herm, Matrix.mulVec_sub, dotProduct_sub]
    rw [h2, hqz] at h1
    linear_combination -h1
  have hpr : prW k r z q = wbPart k r q := by
    unfold prW
    rw [hwb, zero_div, zero_smul, add_zero]
  rw [hpr]
  exact sub_wbPart_X hX

lemma lift_orth {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hd : (Zhat k r z z' y).det ≠ 0)
    (u : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    herm (Hpk k r) (y *ᵥ (Lm k r z z' y *ᵥ u)) (fvec k r z a) = 0 := by
  have hadd : ∀ v w f : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) (v + w) f = herm (Hpk k r) v f + herm (Hpk k r) w f := by
    intro v w f
    simp [herm, Matrix.mulVec_add, dotProduct_add]
  have hsmul : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hsum : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f := by
    intro g f
    simp [herm, Matrix.mulVec_sum, dotProduct_sum]
  rw [Lm_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, hadd, hsum]
  simp only [Matrix.mulVec_smul, hsmul]
  change wv k r z y u a + ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = 0
  have hZg : Zhat k r z z' y *ᵥ gam k r z z' y u = -wv k r z y u := by
    unfold gam
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, neg_mul, inv_mul_cancel₀ hd, neg_smul, one_smul]
  rw [show ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = (Zhat k r z z' y *ᵥ gam k r z z' y u) a by
    simp [Matrix.mulVec, dotProduct, mul_comm], hZg]
  simp

end loca2

end PI.UnitaryGroupMassFormula.GsFr
