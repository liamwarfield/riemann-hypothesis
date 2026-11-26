module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Assemble

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.VanishExp
open MvPolynomial

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

def shiftPt (a b : Fin k) (s : K) (p : Fin k ⊕ Fin k → K) : Fin k ⊕ Fin k → K :=
  fun i => p i + s * eval p (Rop K k a b (X i))

lemma rop_apply (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

lemma rop_C (a b : Fin k) (r : K) : Rop K k a b (C r) = 0 := by
  simp [rop_apply]

lemma rop_mul (a b : Fin k) (f g : Pol K k) :
    Rop K k a b (f * g) = Rop K k a b f * g + f * Rop K k a b g := by
  rw [rop_apply, rop_apply, rop_apply]
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

lemma rop_rop_X (a b : Fin k) (hab : a ≠ b) (i : Fin k ⊕ Fin k) :
    Rop K k a b (Rop K k a b (X i)) = 0 := by
  rcases i with j | j
  · by_cases h : j = b
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]
  · by_cases h : j = a
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]

lemma rop_iter_mul_X (a b : Fin k) (hab : a ≠ b) (g : Pol K k) (i : Fin k ⊕ Fin k) (n : ℕ) :
    (Rop K k a b)^[n + 1] (g * X i) = (Rop K k a b)^[n + 1] g * X i
      + (n + 1) • ((Rop K k a b)^[n] g * Rop K k a b (X i)) := by
  induction n with
  | zero => simp [rop_mul]
  | succ n ih =>
    have e1 : (Rop K k a b)^[n + 1 + 1] (g * X i) = Rop K k a b ((Rop K k a b)^[n + 1] (g * X i)) :=
      Function.iterate_succ_apply' _ _ _
    have e2 : (Rop K k a b)^[n + 1 + 1] g = Rop K k a b ((Rop K k a b)^[n + 1] g) :=
      Function.iterate_succ_apply' _ _ _
    have e3 : (Rop K k a b)^[n + 1] g = Rop K k a b ((Rop K k a b)^[n] g) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, ih, map_add (f := _), map_nsmul, rop_mul, rop_mul, rop_rop_X a b hab i, e2, ← e3]
    rw [mul_zero, add_zero, succ_nsmul _ (n + 1)]
    abel

def ExpFormula (a b : Fin k) (s : K) (g : Pol K k) : Prop :=
  ∃ N : ℕ, (∀ n, N < n → (Rop K k a b)^[n] g = 0) ∧
    ∀ M, N ≤ M → ∀ p : Fin k ⊕ Fin k → K,
      eval (shiftPt a b s p) g =
        ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval p ((Rop K k a b)^[n] g)

theorem expFormula (a b : Fin k) (hab : a ≠ b) (s : K) (g : Pol K k) : ExpFormula a b s g := by
  unfold ExpFormula
  induction g using MvPolynomial.induction_on
  next r =>
    have hz : ∀ n, (Rop K k a b)^[n + 1] (C r) = 0 := by
      intro n
      rw [Function.iterate_succ_apply, rop_C]
      exact Function.iterate_fixed (map_zero _) n
    refine ⟨0, fun n hn => ?_, fun M _ x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact hz m
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro n _ hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hz m]
        simp
      · intro h
        simp at h
  next p q hp hq =>
    obtain ⟨N1, hz1, hs1⟩ := hp
    obtain ⟨N2, hz2, hs2⟩ := hq
    refine ⟨max N1 N2, fun n hn => ?_, fun M hM x => ?_⟩
    · rw [← Module.End.coe_pow, map_add (f := _), Module.End.coe_pow, hz1 n (by omega), hz2 n (by omega), add_zero]
    · rw [map_add (f := _), hs1 M (by omega) x, hs2 M (by omega) x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Module.End.coe_pow, map_add (f := _), map_add (f := _)]
      ring
  next p i hp =>
    obtain ⟨N, hz, hsum⟩ := hp
    refine ⟨N + 1, fun n hn => ?_, fun M hM x => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [rop_iter_mul_X a b hab p i m, hz (m + 1) (by omega), hz m (by omega)]
      simp
    · have hterm : ∀ m : ℕ, eval x ((Rop K k a b)^[m + 1] (p * X i)) =
          eval x ((Rop K k a b)^[m + 1] p) * x i +
            ((m : K) + 1) * (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) := by
        intro m
        rw [rop_iter_mul_X a b hab p i m, map_add (f := _), eval_mul, eval_X, map_nsmul, eval_mul, nsmul_eq_mul]
        push_cast
        ring
      have hTM : s ^ M / (M.factorial : K) * eval x ((Rop K k a b)^[M] p) = 0 := by
        rw [hz M (by omega), map_zero, mul_zero]
      have hfac : ∀ m : ℕ, s ^ (m + 1) / ((m + 1).factorial : K) * ((m : K) + 1) =
          s * (s ^ m / (m.factorial : K)) := by
        intro m
        have h1 : ((m : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        have h2 : (m.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        rw [Nat.factorial_succ, Nat.cast_mul]
        push_cast
        (try field_simp)
        (try ring)
      have hR : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] (p * X i)) =
          ∑ m ∈ Finset.range M, (s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) * x i +
            s * eval x (Rop K k a b (X i)) * (s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p))) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) * x i := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hterm]
          linear_combination (eval x ((Rop K k a b)^[m] p) * eval x (Rop K k a b (X i))) * hfac m
        · simp
      have hS1 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ (m + 1) / ((m + 1).factorial : K) * eval x ((Rop K k a b)^[m + 1] p) +
          s ^ 0 / ((0 : ℕ).factorial : K) * eval x ((Rop K k a b)^[0] p) := Finset.sum_range_succ' _ _
      have hS2 : ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval x ((Rop K k a b)^[n] p) =
          ∑ m ∈ Finset.range M, s ^ m / (m.factorial : K) * eval x ((Rop K k a b)^[m] p) := by
        rw [Finset.sum_range_succ, hTM, add_zero]
      have hxi : shiftPt a b s x i = x i + s * eval x (Rop K k a b (X i)) := rfl
      rw [hR, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← hS2, eval_mul, eval_X,
        hsum M (by omega) x, hxi, hS1]
      ring

end PI.OpWords
end
end

open MvPolynomial

noncomputable section

namespace PI.OpWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

lemma eval_eq_zero_of_support (g : Pol K k) (p : Fin k ⊕ Fin k → K)
    (h : ∀ m ∈ g.support, ∃ i, m i ≠ 0 ∧ p i = 0) : eval p g = 0 := by
  rw [eval_eq]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨i, hmi, hpi⟩ := h m hm
  rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hmi) (by rw [hpi]; exact zero_pow hmi), mul_zero]

lemma xdeg_of_bihom {d : ℕ} {g : Pol K k} (hg : g ∈ Bihom K k d) {m : Fin k ⊕ Fin k →₀ ℕ}
    (hm : m ∈ g.support) : ∑ a, m (Sum.inl a) = d := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hg
  have hx := (Submodule.mem_inf.1 hg').1
  rw [mem_weightedHomogeneousSubmodule] at hx
  have h1 := hx (MvPolynomial.mem_support_iff.1 hm)
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type] using h1

lemma eval_base {d c : ℕ} (hcd : c < d) (i0 : Fin k) {g : Pol K k} (hg : g ∈ Bihom K k d)
    (hw : WtLe K k c g) (p : Fin k ⊕ Fin k → K) (hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0)
    (hxi : p (Sum.inr i0) = 0) : eval p g = 0 := by
  apply eval_eq_zero_of_support
  intro m hm
  by_contra hne
  push_neg at hne
  have hzero : ∀ b, b ≠ i0 → m (Sum.inl b) = 0 := by
    intro b hb
    by_contra h0
    exact hne _ h0 (hx b hb)
  have hr : m (Sum.inr i0) = 0 := by
    by_contra h0
    exact hne _ h0 hxi
  have hsum := xdeg_of_bihom hg hm
  rw [Finset.sum_eq_single i0 (fun b _ hb => hzero b hb)
    (fun h => absurd (Finset.mem_univ i0) h)] at hsum
  have h2 := hw m hm i0
  omega

lemma iter_mem (W : Submodule K (Pol K k)) (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W)
    (a b : Fin k) {g : Pol K k} (hg : g ∈ W) (n : ℕ) : (Rop K k a b)^[n] g ∈ W := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hst _ ih a b

lemma vanish_at {d c : ℕ} (W : Submodule K (Pol K k)) (hW : W ≤ Bihom K k d)
    (hst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) (hwt : ∀ f ∈ W, WtLe K k c f) (hcd : c < d)
    (i0 : Fin k) (S : Finset (Fin k)) :
    ∀ p : Fin k ⊕ Fin k → K, p (Sum.inl i0) ≠ 0 → (∀ b, b ≠ i0 → p (Sum.inl b) ≠ 0 → b ∈ S) →
      ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → ∀ g ∈ W, eval p g = 0 := by
  classical
  induction S using Finset.induction_on
  next =>
    intro p hp0 hS hq g hg
    have hx : ∀ b, b ≠ i0 → p (Sum.inl b) = 0 := by
      intro b hb
      by_contra h
      exact absurd (hS b hb h) (by simp)
    have hxi : p (Sum.inr i0) = 0 := by
      rw [Finset.sum_eq_single i0 (fun b _ hb => by rw [hx b hb, zero_mul])
        (fun h => absurd (Finset.mem_univ i0) h)] at hq
      exact (mul_eq_zero.1 hq).resolve_left hp0
    exact eval_base hcd i0 (hW hg) (hwt g hg) p hx hxi
  next b S hbS ih =>
    intro p hp0 hS hq g hg
    by_cases hpb : p (Sum.inl b) = 0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · subst h
        exact absurd hpb hne
      · exact h
    by_cases hbi : b = i0
    · refine ih p hp0 ?_ hq g hg
      intro b' hb' hne
      rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
      · exact absurd (h.trans hbi) hb'
      · exact h
    have hib : i0 ≠ b := Ne.symm hbi
    have hshl : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inl j) = y (Sum.inl j) + t * (if j = b then y (Sum.inl i0) else 0) := by
      intro t y j
      by_cases h : j = b <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    have hshr : ∀ (t : K) (y : Fin k ⊕ Fin k → K) (j : Fin k),
        shiftPt i0 b t y (Sum.inr j) = y (Sum.inr j) - t * (if j = i0 then y (Sum.inr b) else 0) := by
      intro t y j
      by_cases h : j = i0 <;> simp [shiftPt, rop_apply, pderiv_X, Pi.single_apply, h] <;> ring
    obtain ⟨s, hs⟩ : ∃ s : K, s = -(p (Sum.inl b) / p (Sum.inl i0)) := ⟨_, rfl⟩
    have hq0 : shiftPt i0 b s p (Sum.inl i0) = p (Sum.inl i0) := by
      rw [hshl, if_neg hib, mul_zero, add_zero]
    have hqb : shiftPt i0 b s p (Sum.inl b) = 0 := by
      rw [hshl, if_pos rfl, hs, neg_mul, div_mul_cancel₀ _ hp0]
      ring
    have hqj : ∀ j, j ≠ b → shiftPt i0 b s p (Sum.inl j) = p (Sum.inl j) := by
      intro j hj
      rw [hshl, if_neg hj, mul_zero, add_zero]
    have hquad : ∑ i, shiftPt i0 b s p (Sum.inl i) * shiftPt i0 b s p (Sum.inr i) = 0 := by
      simp only [hshl, hshr, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hbi, hib, if_false, hq]
      ring
    have ihq : ∀ g ∈ W, eval (shiftPt i0 b s p) g = 0 := by
      refine ih _ (by rw [hq0]; exact hp0) ?_ hquad
      intro b' hb' hne
      by_cases hbb : b' = b
      · subst hbb
        exact absurd hqb hne
      · rw [hqj b' hbb] at hne
        rcases Finset.mem_insert.1 (hS b' hb' hne) with h | h
        · exact absurd h hbb
        · exact h
    have hback : shiftPt i0 b (-s) (shiftPt i0 b s p) = p := by
      funext v
      rcases v with j | j
      · by_cases h : j = b <;> simp [hshl, h, hib] <;> ring
      · by_cases h : j = i0 <;> simp [hshr, h, hbi] <;> ring
    have hE := expFormula i0 b hib (-s) g
    unfold ExpFormula at hE
    obtain ⟨N, _, hsum⟩ := hE
    rw [← hback, hsum N le_rfl]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [ihq _ (iter_mem W hst i0 b hg n), mul_zero]

theorem vanishingOnQuadric : Vanish := by
  intro K _ _ k d c W hW hst hwt hcd f hf p hp
  by_cases h : ∃ i0, p (Sum.inl i0) ≠ 0
  · obtain ⟨i0, hi0⟩ := h
    exact vanish_at W hW hst hwt hcd i0 Finset.univ p hi0 (fun b _ _ => Finset.mem_univ b) hp f hf
  · push_neg at h
    apply eval_eq_zero_of_support
    intro m hm
    have hsum := xdeg_of_bihom (hW hf) hm
    have hex : ∃ a, m (Sum.inl a) ≠ 0 := by
      by_contra h0
      push_neg at h0
      simp [h0] at hsum
      omega
    obtain ⟨a, ha⟩ := hex
    exact ⟨Sum.inl a, ha, h a⟩

end PI.OpWords
end
end

theorem operator_words_bound : Formalism.MainNotions.TestSideCounting.OpBound :=
  PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric
