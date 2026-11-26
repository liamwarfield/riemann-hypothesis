module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TensorV
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.MomentMatch

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PartialTrace
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def ptr (A : Module.End ℂ (Fin n → M)) : Module.End ℂ M :=
  ∑ c, (coordV c).comp (A.comp (LinearMap.single ℂ (fun _ : Fin n => M) c))

theorem ptr_apply (A : Module.End ℂ (Fin n → M)) (x : M) :
    ptr A x = ∑ c, A (Pi.single c x) c := by
  unfold ptr
  rw [LinearMap.sum_apply]
  rfl

theorem pow_single_of_mat (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) (c : Fin n) (x : M) :
    (A ^ k) (Pi.single c x) = fun s => ePow T k s c x := by
  induction k with
  | zero =>
    funext s
    simp only [pow_zero, ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, Module.End.one_apply]
    by_cases h : s = c
    · subst h; simp
    · simp [h]
  | succ k ih =>
    funext s
    rw [pow_succ', Module.End.mul_apply, ih, hA]
    simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply, LinearMap.sum_apply,
      Module.End.mul_apply]

theorem ePow_neg_equiv (F : Fin n → Fin n → Module.End ℂ M) (σ : Fin n ≃ Fin n) (k : ℕ) (a b : Fin n) :
    ePow (fun a b => -F (σ a) (σ b)) k a b = ((-1 : ℂ) ^ k) • ePow F k (σ a) (σ b) := by
  induction k generalizing a b with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply]
  | succ k ih =>
    have e1 : ∀ (G : Fin n → Fin n → Module.End ℂ M) (a b : Fin n),
        ePow G (k + 1) a b = ∑ r, ePow G k a r * G r b := by
      intro G a b
      simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ, Matrix.mul_apply, Matrix.of_apply]
    rw [e1, e1]
    simp_rw [ih]
    conv_rhs => rw [Finset.smul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [smul_mul_assoc, mul_neg, smul_neg, pow_succ, mul_neg_one, neg_smul, mul_one]

theorem ptr_eq_gelfand (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) : ptr (A ^ k) = gelfand T k := by
  ext x
  rw [ptr_apply]
  simp only [gelfand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_single_of_mat A T hA k c x]

theorem ptr_eeV_pow (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeV E ^ k) = ((-1 : ℂ) ^ k) • gelfand (antiE E) k := by
  have hA : ∀ f s, eeV E f s = ∑ r, (fun s r => E r s) s r (f r) := by
    intro f s
    simp [eeV, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  have key : ∀ a, ePow (antiE E) k a a =
      ((-1 : ℂ) ^ k) • ePow (fun s r => E r s) k (Fin.revPerm a) (Fin.revPerm a) := fun a =>
    ePow_neg_equiv (fun s r => E r s) Fin.revPerm k a a
  simp only [gelfand, key, Finset.smul_sum, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  exact (Equiv.sum_comp Fin.revPerm (fun a => ePow (fun s r => E r s) k a a)).symm

theorem ptr_eeVd_pow (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeVd E ^ k) = ((-1 : ℂ) ^ k) • gelfand E k := by
  have hA : ∀ f r, eeVd E f r = ∑ s, (fun r s => -E r s) r s (f s) := by
    intro f r
    simp [eeVd, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  simp only [gelfand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact ePow_neg_equiv E (Equiv.refl _) k a a

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.InhabCAR
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev Fock (n : ℕ) := ExteriorAlgebra ℂ (Fin n × Fin n → ℂ)

def cpFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single (i, a) (1 : ℂ)))

def cmFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) (i, a))

theorem isCAR_fock : IsCAR (cpFock (n := n)) cmFock := by
  intro i a j b
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cpFock, LinearMap.mulLeft_apply,
      LinearMap.zero_apply]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, LinearMap.zero_apply]
    rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]
  · refine LinearMap.ext fun z => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, cmFock, cpFock, LinearMap.mulLeft_apply]
    rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
    by_cases h : i = j ∧ a = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [if_neg h]
      have hne : (i, a) ≠ (j, b) := fun e => h ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
      simp [LinearMap.proj_apply, Pi.single_apply, hne]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandHW
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def hwShift (ν : Fin n → ℝ) : Fin n → ℂ := fun r => ((ν r : ℝ) : ℂ) + (((n - 1 - (r : ℕ) : ℕ) : ℝ) : ℂ)

theorem hwShift_eq_icShift (ν : Fin n → ℝ) : hwShift ν = icShift (ν + rho n) := by
  funext r
  have hr := r.isLt
  simp only [hwShift, icShift, rho, Pi.add_apply]
  rw [Nat.cast_sub (by omega : (r : ℕ) ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

theorem ePow_hw_lower {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (s r : Fin n) (hsr : s < r) : ePow E k s r v = 0 := by
  induction k generalizing s r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, hsr.ne]
  | succ k ih =>
    rw [show ePow E (k + 1) s r = ∑ c, E s c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro c _
    rw [Module.End.mul_apply]
    rcases lt_or_ge c r with hcr | hrc
    · rw [ih c r hcr, map_zero]
    · have hc := ePow_comm hE k s c c r
      rw [if_pos rfl, if_neg hsr.ne'] at hc
      have hc' := congrArg (fun f => f v) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply, sub_zero] at hc'
      rw [hv.2 s c (lt_of_lt_of_le hsr hrc), map_zero, sub_zero, ih s r hsr] at hc'
      exact hc'

theorem ePow_hw_diag {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (r : Fin n) : ePow E k r r v = gx (hwShift ν) k r • v := by
  induction k generalizing r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, gx]
  | succ k ih =>
    have key : ∀ c, E r c (ePow E k c r v) =
        ((if c = r then (ν r : ℂ) * gx (hwShift ν) k r else 0) +
         (if r < c then gx (hwShift ν) k r - gx (hwShift ν) k c else 0)) • v := by
      intro c
      rcases lt_trichotomy c r with h | h | h
      · rw [ePow_hw_lower hE hv k c r h, map_zero, if_neg h.ne, if_neg (not_lt.2 h.le)]
        simp
      · subst h
        rw [ih, LinearMap.map_smul, hv.1, smul_smul, if_pos rfl, if_neg (lt_irrefl _), add_zero,
          mul_comm]
      · have hc := ePow_comm hE k r c c r
        rw [if_pos rfl, if_pos rfl] at hc
        have hc' := congrArg (fun f => f v) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc'
        rw [hv.2 r c h, map_zero, sub_zero, ih, ih c] at hc'
        rw [if_neg h.ne', if_pos h, zero_add, sub_smul]
        exact hc'
    rw [show ePow E (k + 1) r r = ∑ c, E r c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    simp only [Module.End.mul_apply, key]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.sum_filter,
      Finset.sum_sub_distrib, Finset.sum_const]
    have hf : (univ.filter fun c => r < c) = Finset.Ioi r := by ext; simp
    rw [hf, Fin.card_Ioi, nsmul_eq_mul]
    simp only [gx, hwShift, hf]
    push_cast
    ring

theorem gelfand_hw {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) : gelfand E k v = gval (icShift (ν + rho n)) k • v := by
  unfold gelfand
  rw [LinearMap.sum_apply]
  simp only [ePow_hw_diag hE hv k, ← Finset.sum_smul, sum_gx_eq_gval, hwShift_eq_icShift]

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARKinv
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem carKinv_triple₁ {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = 0)
    (h2 : B * C + C * B = δ) : A * B * C - C * (A * B) = A * δ := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = A * δ := by rw [h1, h2]; noncomm_ring

theorem carKinv_triple₂ {R : Type*} [Ring R] (A B C δ : R) (h1 : C * A + A * C = δ)
    (h2 : B * C + C * B = 0) : A * B * C - C * (A * B) = -(δ * B) := by
  calc A * B * C - C * (A * B) = A * (B * C + C * B) - (C * A + A * C) * B := by noncomm_ring
    _ = -(δ * B) := by rw [h1, h2]; noncomm_ring

theorem carKinv_sum_mul_comm {R ι κ : Type*} [Ring R] (s : Finset ι) (t : Finset κ)
    (f : ι → κ → R) (X : R) (h : ∑ i ∈ s, ∑ c ∈ t, (f i c * X - X * f i c) = 0) :
    (∑ i ∈ s, ∑ c ∈ t, f i c) * X = X * ∑ i ∈ s, ∑ c ∈ t, f i c := by
  rw [← sub_eq_zero, ← h, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem carKinv_expand {R : Type*} [Ring R] (P Q A S : R) (hQA : Q * A = A * Q)
    (hPS : P * S = S * P) :
    P * Q * (A + S) - (A + S) * (P * Q) = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
  calc P * Q * (A + S) - (A + S) * (P * Q)
      = (P * A - A * P) * Q - P * (S * Q - Q * S) + P * (Q * A - A * Q) + (P * S - S * P) * Q := by
        noncomm_ring
    _ = (P * A - A * P) * Q - P * (S * Q - Q * S) := by
        rw [hQA, hPS, sub_self, sub_self, mul_zero, zero_mul, add_zero, add_zero]

theorem carKinv_E_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E c d * sgE ε cp cm a b = sgE ε cp cm a b * E c d := by
  have key : ∀ x y u v, E c d * (cp x y * cm u v) = cp x y * cm u v * E c d := by
    intro x y u v
    rw [← mul_assoc, (hEC c d x y).1, mul_assoc, (hEC c d u v).2, ← mul_assoc]
  unfold sgE
  split_ifs
  · rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => key _ _ _ _
  · rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun x _ => key _ _ _ _)
  · simp

theorem carKinv_sg_cp_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = if b = i then cp a c else 0 := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₁ _ _ _ _ (hC i c a x).1 (hC b x i c).2.2]
  by_cases hbi : b = i
  · subst hbi
    simp [mul_ite, Finset.sum_ite_eq', hcm]
  · simp [hbi]

theorem carKinv_sg_cp_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b = -(if a = c then cp i b else 0) := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₁ _ _ _ _ (hC i c y b).1 (hC y a i c).2.2]
  congr 1
  by_cases hac : a = c
  · subst hac
    simp [mul_ite, Finset.sum_ite_eq', hip]
  · simp [hac]

theorem carKinv_sg_cm_plus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = true) (hb : ε b = true) (hc : ε c = false) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = -(if i = a then cm b c else 0) := by
  have hs : sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by simp [sgE, ha, hb]
  have hcm : c ∈ minusIdx ε := by simp [minusIdx, hc]
  rw [hs, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => carKinv_triple₂ _ _ _ _ (hC i c a x).2.2 (hC b x i c).2.1,
    Finset.sum_neg_distrib]
  congr 1
  by_cases hia : i = a
  · subst hia
    simp [ite_mul, Finset.sum_ite_eq, hcm]
  · simp [hia]

theorem carKinv_sg_cm_minus {cp cm : Fin n → Fin n → Module.End ℂ W} (hC : IsCAR cp cm)
    (ε : Fin n → Bool) (a b i c : Fin n) (ha : ε a = false) (hb : ε b = false) (hi : ε i = true) :
    sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b = if c = b then cm i a else 0 := by
  have hs : sgE ε cp cm a b = -∑ y ∈ plusIdx ε, cp y b * cm y a := by simp [sgE, ha, hb]
  have hip : i ∈ plusIdx ε := by simp [plusIdx, hi]
  have e : ∀ S T : Module.End ℂ W, (-S) * T - T * (-S) = -(S * T - T * S) := fun S T => by noncomm_ring
  rw [hs, e, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun y _ => carKinv_triple₂ _ _ _ _ (hC i c y b).2.2 (hC y a i c).2.1,
    Finset.sum_neg_distrib, neg_neg]
  by_cases hcb : c = b
  · subst hcb
    simp [ite_mul, Finset.sum_ite_eq, hip]
  · simp [hcb]

theorem carKinv_term_d {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E c i * cp i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E c i * cp i c) =
      ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
        E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).1.symm (carKinv_E_sgE hEC ε a b c i), hE c i a b]

theorem carKinv_term_d' {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b i c : Fin n) :
    E i c * cm i c * diagE ε E cp cm a b - diagE ε E cp cm a b * (E i c * cm i c) =
      ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
        E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) := by
  unfold diagE
  rw [carKinv_expand _ _ _ _ (hEC a b i c).2.symm (carKinv_E_sgE hEC ε a b i c), hE i c a b]

theorem dOp_comm_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp ε E cp * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp ε E cp := by
  unfold dOp
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hia : i ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
          E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) =
        (if a = c then E a i * cp i b else 0) - (if b = c then E a i * cp i b else 0) by
      rw [carKinv_sg_cp_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hbc : b ≠ c := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if i = a then E c b else 0) - (if b = c then E a i else 0)) * cp i c -
          E c i * (sgE ε cp cm a b * cp i c - cp i c * sgE ε cp cm a b) =
        (if i = a then E c b * cp a c else 0) - (if b = i then E c b * cp a c else 0) by
      rw [carKinv_sg_cp_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]

theorem dOp'_comm_diagE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (hab : ε a = ε b) :
    dOp' ε E cm * diagE ε E cp cm a b = diagE ε E cp cm a b * dOp' ε E cm := by
  unfold dOp'
  rw [neg_mul, mul_neg, neg_inj]
  apply carKinv_sum_mul_comm
  simp_rw [carKinv_term_d' hE hEC]
  have hpl : ∀ x, x ∈ plusIdx ε ↔ ε x = true := fun x => by simp [plusIdx]
  have hmi : ∀ x, x ∈ minusIdx ε ↔ ε x = false := fun x => by simp [minusIdx]
  cases hεa : ε a
  ·
    have hεb : ε b = false := by rw [← hab]; exact hεa
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := (hpl i).1 hi
    have hib : b ≠ i := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun c _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if c = a then E i b * cm i a else 0) - (if c = b then E i b * cm i a else 0) by
      rw [carKinv_sg_cm_minus hC ε a b i c hεa hεb hi']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos ((hmi a).2 hεa),
      if_pos ((hmi b).2 hεb), sub_self]
  ·
    have hεb : ε b = true := by rw [← hab]; exact hεa
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := (hmi c).1 hc
    have hca : c ≠ a := by rintro rfl; simp_all
    rw [Finset.sum_congr rfl fun i _ => show
        ((if c = a then E i b else 0) - (if b = i then E a c else 0)) * cm i c -
          E i c * (sgE ε cp cm a b * cm i c - cm i c * sgE ε cp cm a b) =
        (if i = a then E a c * cm b c else 0) - (if b = i then E a c * cm b c else 0) by
      rw [carKinv_sg_cm_plus hC ε a b i c hεa hεb hc']
      split_ifs <;> subst_vars <;> (try simp_all) <;> (try noncomm_ring)]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hpl a).2 hεa),
      if_pos ((hpl b).2 hεb), sub_self]

end ReciprocityTheory.ChartRestriction.DS
end
end
