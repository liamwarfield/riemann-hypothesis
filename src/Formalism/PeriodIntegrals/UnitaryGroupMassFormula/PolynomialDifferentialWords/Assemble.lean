module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaMain

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PolarizationBihomogeneous
open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

theorem rop_apply_eq (K : Type) [Field K] (k : ℕ) (a b : Fin k) (f : Pol K k) :
    Rop K k a b f = X (Sum.inl a) * pderiv (Sum.inl b) f - X (Sum.inr b) * pderiv (Sum.inr a) f := rfl

theorem pderiv_inl_tt (K : Type) [Field K] (k : ℕ) (b : Fin k) :
    pderiv (Sum.inl b) (tt K k) = X (Sum.inr b) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem pderiv_inr_tt (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    pderiv (Sum.inr a) (tt K k) = X (Sum.inl a) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem rttRelation : RTT := by
  intro K _ _ k a b g
  rw [rop_apply_eq, rop_apply_eq]
  simp only [Derivation.leibniz, pderiv_inl_tt, pderiv_inr_tt, smul_eq_mul]
  ring

theorem iwh_X_pderiv {σ : Type} {K : Type} [Field K] (w : σ → ℕ) (i j : σ) (hij : w i = w j)
    {f : MvPolynomial σ K} {n : ℕ} (hf : IsWeightedHomogeneous w f n) :
    IsWeightedHomogeneous w (X i * pderiv j f) n := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum, Finset.mul_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have hwm : weight w m = n := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [pderiv_monomial]
  by_cases hmj : m j = 0
  · simp [hmj, isWeightedHomogeneous_zero]
  · have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have hs : ∀ v, weight w (Finsupp.single v 1) = w v := by
      intro v
      simp [Finsupp.weight_apply, Finsupp.sum_single_index]
    have h1 : weight w (m - Finsupp.single j 1) + w j = n := by
      rw [← hs j, ← map_add (f := _), tsub_add_cancel_of_le hle, hwm]
    rw [X, monomial_mul, one_mul]
    apply isWeightedHomogeneous_monomial
    rw [map_add (f := _), hs i, hij, add_comm, h1]

theorem polarizationBihomogeneous : RBihom := by
  intro K _ _ k d a b f hf
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  show Rop K k a b f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  rw [rop_apply_eq]
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ ?_ ?_, Submodule.sub_mem _ ?_ ?_⟩ <;>
    rw [mem_weightedHomogeneousSubmodule]
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wx]) h1
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2
  · exact iwh_X_pderiv _ _ _ (by simp [wxi]) h2

theorem coeff_X_pderiv_self {σ : Type} {K : Type} [Field K] (i : σ) (f : MvPolynomial σ K)
    (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (X i * pderiv i f) m = AddMonoidAlgebra.coeff f m * (m i : K) := by
  classical
  induction f using MvPolynomial.induction_on'
  next u a =>
    rw [pderiv_monomial]
    by_cases hu : u i = 0
    · by_cases h : u = m
      · subst h
        simp [hu]
      · simp [hu, coeff_monomial, h]
    · have hle : Finsupp.single i 1 ≤ u := by
        rw [Finsupp.single_le_iff]
        omega
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, coeff_monomial, coeff_monomial]
      split_ifs with h
      · subst h
        rfl
      · simp
  next p q hp hq =>
    simp only [map_add (f := _), mul_add, MvPolynomial.coeff_add, hp, hq, add_mul]

theorem weightOfEigenvector : WtOfEig := by
  intro K _ _ k a w f h m hm
  have h1 := congrArg (AddMonoidAlgebra.coeff · m) h
  rw [rop_apply_eq, coeff_sub, coeff_X_pderiv_self, coeff_X_pderiv_self, coeff_smul] at h1
  have hc : AddMonoidAlgebra.coeff f m ≠ 0 := MvPolynomial.mem_support_iff.1 hm
  have h2 : (((m (Sum.inl a) : ℤ) - m (Sum.inr a) : ℤ) : K) = (w : K) := by
    apply mul_left_cancel₀ hc
    push_cast
    linear_combination h1
  exact_mod_cast h2

def va (k : ℕ) (a : Fin k) : Fin k ⊕ Fin k → ℤ :=
  Sum.elim (fun i => if i = a then 1 else 0) (fun i => if i = a then -1 else 0)

theorem weight_va (k : ℕ) (a : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) :
    weight (va k a) m = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, va, Fintype.sum_sum_type, sub_eq_add_neg]

theorem tt_va (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    IsWeightedHomogeneous (va k a) (tt K k) 0 := by
  show IsWeightedHomogeneous (va k a) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 0
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (va k a) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (va k a) (Sum.inr i))
  by_cases hi : i = a <;> simpa [va, hi] using h

theorem comp_mul_zero {σ : Type} {K : Type} [Field K] (w : σ → ℤ) {φ : MvPolynomial σ K}
    (hφ : IsWeightedHomogeneous w φ 0) (n : ℤ) (ψ : MvPolynomial σ K) :
    weightedHomogeneousComponent w n (φ * ψ) = φ * weightedHomogeneousComponent w n ψ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hd
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : AddMonoidAlgebra.coeff φ x.1 = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 = n := by
        rw [← hd, ← hsum, map_add (f := _), hx0, zero_add]
      rw [if_pos hw]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases h0 : AddMonoidAlgebra.coeff φ x.1 = 0
    · simp [h0]
    · have hx0 := hφ h0
      have hsum := by simpa using hx
      have hw : weight w x.2 ≠ n := by
        rw [← hsum, map_add (f := _), hx0, zero_add] at hd
        exact hd
      rw [if_neg hw, mul_zero]

theorem tt_ne_zero (K : Type) [Field K] [CharZero K] (k : ℕ) (hk : 0 < k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  simp [tt] at h1
  omega

theorem pairingWeightCancel : TTWt := by
  intro K _ _ k c g h m hm a
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := ⟨_, rfl⟩
  have hwm : weight (va k a) m = n := by rw [weight_va, hn]
  have hk : 0 < k := Fin.pos a
  have hcomp : weightedHomogeneousComponent (va k a) n g ≠ 0 := by
    intro h0
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hwm] at h3
    exact (MvPolynomial.mem_support_iff.1 hm) (by simpa using h3)
  have hprod : weightedHomogeneousComponent (va k a) n (tt K k * g) ≠ 0 := by
    rw [comp_mul_zero (va k a) (tt_va K k a) n g]
    exact mul_ne_zero (tt_ne_zero K k hk) hcomp
  apply hprod
  ext m'
  rw [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero]
  split_ifs with hw
  · by_contra hne
    have h4 := h m' (MvPolynomial.mem_support_iff.2 hne) a
    rw [weight_va] at hw
    omega
  · rfl

end PI.OpWords
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PairingPowMemSymbolRange
open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable (K : Type) [Field K] [CharZero K] (k d : ℕ)

def Sc (c : ℕ) : Submodule K (Pol K k) :=
  ((Wc K k d c).map (kappa K k d)).comap (LinearMap.mulLeft K (tt K k ^ (d - c)))

theorem mem_Sc (c : ℕ) (g : Pol K k) :
    g ∈ Sc K k d c ↔ tt K k ^ (d - c) * g ∈ (Wc K k d c).map (kappa K k d) := Iff.rfl

theorem Wc_mono {c c' : ℕ} (h : c ≤ c') : Wc K k d c ≤ Wc K k d c' := by
  unfold Wc
  apply Submodule.span_mono
  rintro Bx ⟨l, hl, rfl⟩
  exact ⟨l, le_trans hl h, rfl⟩

theorem Ed_mul_Wc (c : ℕ) (a b : Fin k) {B : Module.End K ↥(homogeneousSubmodule (Fin k) K d)}
    (hB : B ∈ Wc K k d c) : Formalism.MainNotions.TestSideCounting.Ed K k d a b * B ∈ Wc K k d (c + 1) := by
  unfold Wc at hB ⊢
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨(a, b) :: l, by simpa using hl, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

theorem wtXSum (m : Fin k ⊕ Fin k →₀ ℕ) : weight (wx k) m = ∑ i, m (Sum.inl i) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type]

theorem wtXiSum (m : Fin k ⊕ Fin k →₀ ℕ) : weight (wxi k) m = ∑ i, m (Sum.inr i) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type]

theorem bihom_zero_const (g : Pol K k) (hg : g ∈ Bihom K k 0) : ∃ r : K, g = C r := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) 0 ⊓ weightedHomogeneousSubmodule K (wxi k) 0 := hg
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hg'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  refine ⟨AddMonoidAlgebra.coeff g 0, ?_⟩
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [← hm]
  · by_contra hne
    apply hm
    have e1 := h1 hne
    have e2 := h2 hne
    rw [wtXSum] at e1
    rw [wtXiSum] at e2
    ext v
    rcases v with i | i
    · have h3 := (Finset.sum_eq_zero_iff.1 e1) i (Finset.mem_univ i)
      simp [h3]
    · have h3 := (Finset.sum_eq_zero_iff.1 e2) i (Finset.mem_univ i)
      simp [h3]

theorem bihom_le_Sc : ∀ c, c ≤ d → Bihom K k c ≤ Sc K k d c := by
  intro c
  induction c with
  | zero =>
    intro _ g hg
    obtain ⟨r, rfl⟩ := bihom_zero_const K k g hg
    rw [mem_Sc]
    refine ⟨(r * (d.factorial : K)) • 1, Submodule.smul_mem _ _
      (Submodule.subset_span ⟨[], by simp, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩), ?_⟩
    rw [map_smul, symbolMapOne, smul_smul, mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)), mul_one, Nat.sub_zero,
      smul_eq_C_mul, mul_comm]
  | succ c ih =>
    intro hc
    have IH := ih (by omega)
    obtain ⟨n, hn⟩ : ∃ n, d - c = n + 1 := ⟨d - c - 1, by omega⟩
    have hn2 : d - (c + 1) = n := by omega
    intro g hg
    have hg' := hg
    rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
      mem_weightedHomogeneousSubmodule] at hg'
    rw [as_sum g]
    apply Submodule.sum_mem
    intro m hmS
    have hne : AddMonoidAlgebra.coeff g m ≠ 0 := MvPolynomial.mem_support_iff.1 hmS
    have hw1 := hg'.1 hne
    have hw2 := hg'.2 hne
    rw [show monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one]]
    apply Submodule.smul_mem

    rw [wtXSum] at hw1
    rw [wtXiSum] at hw2
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; omega)
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw2]; omega)
    obtain ⟨m', rfl⟩ : ∃ m' : Fin k ⊕ Fin k →₀ ℕ,
        m = m' + single (Sum.inl a) 1 + single (Sum.inr b) 1 := by
      refine ⟨m - single (Sum.inl a) 1 - single (Sum.inr b) 1, ?_⟩
      ext i
      rcases i with i | i
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inl.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inr.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
    have hmono : X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K) =
        monomial (m' + single (Sum.inl a) 1 + single (Sum.inr b) 1) 1 := by
      simp only [X, monomial_mul, one_mul]
      congr 1
      abel
    have hw1' : weight (wx k) m' = c := by
      have := hw1
      rw [← wtXSum, map_add (f := _), map_add (f := _), weight_single, weight_single] at this
      have e1 : wx k (Sum.inl a) = 1 := rfl
      have e2 : wx k (Sum.inr b) = 0 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hw2' : weight (wxi k) m' = c := by
      have := hw2
      rw [← wtXiSum, map_add (f := _), map_add (f := _), weight_single, weight_single] at this
      have e1 : wxi k (Sum.inl a) = 0 := rfl
      have e2 : wxi k (Sum.inr b) = 1 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hh : monomial m' (1 : K) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule]
      exact ⟨isWeightedHomogeneous_monomial _ _ _ hw1', isWeightedHomogeneous_monomial _ _ _ hw2'⟩
    have hh' : X (Sum.inl a) * pderiv (Sum.inl b) (monomial m' (1 : K)) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule] at hh ⊢
      exact ⟨iwh_X_pderiv _ _ _ (by simp [wx]) hh.1, iwh_X_pderiv _ _ _ (by simp [wxi]) hh.2⟩
    obtain ⟨B, hB, hBk⟩ := (mem_Sc K k d c _).1 (IH hh)
    obtain ⟨B', hB', hB'k⟩ := (mem_Sc K k d c _).1 (IH hh')
    rw [hn] at hBk hB'k
    rw [mem_Sc, hn2, ← hmono]
    refine ⟨(((n + 1 : ℕ) : K)⁻¹) • (Formalism.MainNotions.TestSideCounting.Ed K k d a b * B - B'),
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (Ed_mul_Wc K k d c a b hB)
        (Wc_mono K k d (Nat.le_succ c) hB')), ?_⟩
    rw [map_smul, map_sub, symbolMapMulLeft, hBk, hB'k, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_inl_tt, Nat.add_sub_cancel, smul_eq_C_mul]
    simp only [smul_eq_mul, nsmul_eq_mul]
    have hC : (C (((n + 1 : ℕ) : K)⁻¹) : Pol K k) * ((n + 1 : ℕ) : Pol K k) = 1 := by
      rw [← map_natCast (C : K →+* Pol K k), ← map_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)), map_one]
    linear_combination (tt K k ^ n * (X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K))) * hC

theorem pairingPowMemSymbolRange : Surj := by
  intro K _ _ k d c hc g hg
  exact (mem_Sc K k d c g).1 (bihom_le_Sc K k d c hc hg)

end PI.OpWords
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.DivideAll
open MvPolynomial

noncomputable section

namespace PI.OpWords

theorem wtLe_span (K : Type) [Field K] (k : ℕ) (c : ℤ) (s : Set (Pol K k))
    (hs : ∀ f ∈ s, WtLe K k c f) : ∀ f ∈ Submodule.span K s, WtLe K k c f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm a
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hx m h a
    · exact hy m h a
  | smul r x _ hx =>
    intro m hm a
    exact hx m (support_smul hm) a

theorem kappa_ad (hL : KappaLeft) (hR : KappaRight) (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (a b : Fin k) (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A - A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) =
      Rop K k a b (kappa K k d A) := by
  rw [map_sub, hL K k d a b A, hR K k d a b A]
  rfl

theorem divide_all (hV : Vanish) (hD : DivT) (hRB : RBihom) (hRT : RTT) (hTW : TTWt)
    (K : Type) [Field K] [CharZero K] (k c : ℕ) : ∀ n : ℕ, ∀ (W : Submodule K (Pol K k)),
    W ≤ Bihom K k (c + n) → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) →
    ∀ f ∈ W, ∃ g ∈ Bihom K k c, f = tt K k ^ n * g := by
  intro n
  induction n with
  | zero =>
    intro W hW _ _ f hf
    exact ⟨f, by simpa using hW hf, by simp⟩
  | succ n ih =>
    intro W hW hst hwt f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hf' : f ∈ weightedHomogeneousSubmodule K (wx 0) (c + (n + 1)) ⊓
          weightedHomogeneousSubmodule K (wxi 0) (c + (n + 1)) := hW hf
      have h1 := (Submodule.mem_inf.1 hf').1
      rw [mem_weightedHomogeneousSubmodule] at h1
      rw [mul_zero]
      ext m
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_contra h
      have h2 := h1 h
      have h3 : m = 0 := by
        ext v
        rcases v with i | i <;> exact i.elim0
      rw [h3, map_zero] at h2
      omega
    · have htt : tt K k ≠ 0 := by
        intro h
        have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
        simp [tt] at h1
        omega
      have hdiv : ∀ f ∈ W, ∃ g ∈ Bihom K k (c + n), f = tt K k * g := by
        intro f hf
        have hv := hV K k (c + (n + 1)) c W hW hst hwt (by omega) f hf
        obtain ⟨g, hg, rfl⟩ := hD K k (c + (n + 1)) (by omega) f (hW hf) hv
        exact ⟨g, by simpa using hg, rfl⟩
      let W' : Submodule K (Pol K k) := W.comap (LinearMap.mulLeft K (tt K k))
      have hmem : ∀ g, g ∈ W' ↔ tt K k * g ∈ W := fun g => Iff.rfl
      have hW' : W' ≤ Bihom K k (c + n) := by
        intro g hg
        obtain ⟨g', hg', he⟩ := hdiv _ ((hmem g).1 hg)
        rw [mul_left_cancel₀ htt he]
        exact hg'
      have hst' : ∀ f ∈ W', ∀ a b, Rop K k a b f ∈ W' := by
        intro g hg a b
        rw [hmem, ← hRT K k a b g]
        exact hst _ ((hmem g).1 hg) a b
      have hwt' : ∀ f ∈ W', WtLe K k c f := by
        intro g hg
        exact hTW K k c g (hwt _ ((hmem g).1 hg))
      obtain ⟨g, hg, rfl⟩ := hdiv f hf
      obtain ⟨g'', hg'', rfl⟩ := ih W' hW' hst' hwt' g ((hmem g).2 hf)
      exact ⟨g'', hg'', by ring⟩

theorem opWords_of (hI : KappaInj) (hL : KappaLeft) (hR : KappaRight) (hB : KappaBihom)
    (hE : WtOfEig) (hRB : RBihom) (hRT : RTT) (hTW : TTWt) (hD : DivT) (hV : Vanish)
    (hS : Surj) : Formalism.MainNotions.TestSideCounting.OpBound := by
  intro K _ _ k d c WW Sg hst hspan heig A hA
  have key : ∃ c' : ℕ, c' ≤ c ∧ c' ≤ d ∧ ∃ g ∈ Bihom K k c', kappa K k d A = tt K k ^ (d - c') * g := by
    rcases Nat.lt_or_ge c d with hcd | hdc
    · let W : Submodule K (Pol K k) := WW.map (kappa K k d)
      have hW : W ≤ Bihom K k (c + (d - c)) := by
        have e : c + (d - c) = d := by omega
        rw [e]
        rintro f ⟨A', _, rfl⟩
        exact hB K k d A'
      have hWst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W := by
        rintro f ⟨A', hA', rfl⟩ a b
        rw [← kappa_ad hL hR K k d a b A']
        exact Submodule.mem_map_of_mem (hst A' hA' a b)
      have hWwt : ∀ f ∈ W, WtLe K k c f := by
        have hWeq : W = Submodule.span K (kappa K k d '' Sg) := by
          show WW.map (kappa K k d) = _
          rw [hspan, Submodule.map_span]
        rw [hWeq]
        apply wtLe_span
        rintro f ⟨A', hA', rfl⟩ m hm a
        obtain ⟨ω, hω, hωc⟩ := heig A' hA'
        have h1 : Rop K k a a (kappa K k d A') = (ω a : K) • kappa K k d A' := by
          rw [← kappa_ad hL hR K k d a a A', hω a, map_smul]
        have h2 := hE K k a (ω a) (kappa K k d A') h1 m hm
        rw [h2]
        exact_mod_cast hωc a
      obtain ⟨g, hg, he⟩ := divide_all hV hD hRB hRT hTW K k c (d - c) W hW hWst hWwt _
        (Submodule.mem_map_of_mem hA)
      exact ⟨c, le_rfl, hcd.le, g, hg, he⟩
    · exact ⟨d, hdc, le_rfl, kappa K k d A, hB K k d A, by simp⟩
  obtain ⟨c', hc'c, hc'd, g, hg, he⟩ := key
  have hsurj := hS K k d c' hc'd g hg
  rw [← he] at hsurj
  obtain ⟨B, hB', hBe⟩ := Submodule.mem_map.1 hsurj
  have hAB : B = A := hI K k d hBe
  subst hAB
  have hmono : Wc K k d c' ≤ Wc K k d c := by
    unfold Wc
    apply Submodule.span_mono
    rintro Bx ⟨l, hl, rfl⟩
    exact ⟨l, le_trans hl hc'c, rfl⟩
  exact hmono hB'

end PI.OpWords
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.IsWeightedHomogeneousPairingLeft
open MvPolynomial

noncomputable section

namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords

variable {K : Type} [Field K] [CharZero K] {k : ℕ}

theorem homog_of_mul {σ : Type} (w : σ → ℕ) {s g : MvPolynomial σ K} {n : ℕ}
    (hs : IsWeightedHomogeneous w s 1) (hs0 : s ≠ 0)
    (h : IsWeightedHomogeneous w (s * g) (1 + n)) : IsWeightedHomogeneous w g n := by
  classical
  have hA : ∀ j, weightedHomogeneousComponent w (1 + j) (s * g) = s * weightedHomogeneousComponent w j g := by
    intro j
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
    split_ifs with hd
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [coeff_weightedHomogeneousComponent]
      by_cases h0 : AddMonoidAlgebra.coeff s x.1 = 0
      · simp [h0]
      · have hx0 := hs h0
        have hsum : x.1 + x.2 = d := by simpa using hx
        have hw : Finsupp.weight w x.2 = j := by
          rw [← hsum, map_add (f := _), hx0] at hd
          omega
        rw [if_pos hw]
    · symm
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [coeff_weightedHomogeneousComponent]
      by_cases h0 : AddMonoidAlgebra.coeff s x.1 = 0
      · simp [h0]
      · have hx0 := hs h0
        have hsum : x.1 + x.2 = d := by simpa using hx
        have hw : Finsupp.weight w x.2 ≠ j := by
          rw [← hsum, map_add (f := _), hx0] at hd
          omega
        rw [if_neg hw, mul_zero]
  intro m hm
  by_contra hne
  have hc : weightedHomogeneousComponent w (Finsupp.weight w m) g ≠ 0 := by
    intro h0
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) h0
    simp only [coeff_weightedHomogeneousComponent, ite_eq_left rfl,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h3
    exact hm h3
  apply hc
  have h4 : s * weightedHomogeneousComponent w (Finsupp.weight w m) g = 0 := by
    rw [← hA]
    ext d
    simp only [coeff_weightedHomogeneousComponent, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply]
    split_ifs with hd
    · by_contra hne2
      have h5 := h hne2
      omega
    · rfl
  exact (mul_eq_zero.1 h4).resolve_left hs0

theorem isWeightedHomogeneous_pairing_left : IsWeightedHomogeneous (wx k) (tt K k) 1 := by
  show IsWeightedHomogeneous (wx k) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 1
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (wx k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (wx k) (Sum.inr i))
  simpa [wx] using h

theorem tt_homog_xi : IsWeightedHomogeneous (wxi k) (tt K k) 1 := by
  show IsWeightedHomogeneous (wxi k) (∑ i, X (Sum.inl i) * X (Sum.inr i) : Pol K k) 1
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X K (wxi k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X K (wxi k) (Sum.inr i))
  simpa [wxi] using h

theorem eval_tt (p : Fin k ⊕ Fin k → K) :
    eval p (tt K k) = ∑ i, p (Sum.inl i) * p (Sum.inr i) := by
  simp [tt]

theorem tt_ne_zero (hk : 1 ≤ k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  rw [eval_tt] at h1
  simp at h1
  omega

theorem not_X_dvd_tt (i0 j : Fin k) (hj : j ≠ i0) :
    ¬ (X (Sum.inl i0) : Pol K k) ∣ tt K k := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval (Sum.elim (fun i : Fin k => if i = j then (1 : K) else 0) (fun _ => 1))) hq
  rw [eval_tt] at h
  simp [Ne.symm hj] at h

theorem dvd_of_dvd_X_pow {i : Fin k ⊕ Fin k} {s f : Pol K k} (hs : ¬ (X i : Pol K k) ∣ s) :
    ∀ n : ℕ, s ∣ X i ^ n * f → s ∣ f
  | 0, h => by simpa using h
  | n + 1, h => by
    rw [pow_succ', mul_assoc] at h
    rcases dvd_X_mul_iff.1 h with h' | ⟨h', _⟩
    · exact dvd_of_dvd_X_pow hs n h'
    · exact absurd h' hs


variable (K) in
def chiF (K : Type) [Field K] (i0 : Fin k) : Fin k ⊕ Fin k → Pol K k :=
  Sum.elim (fun j => X (Sum.inl j)) (fun j => X (Sum.inl i0) * X (Sum.inr j))


variable (K) in
def tp (K : Type) [Field K] (i0 : Fin k) : Pol K k :=
  ∑ j ∈ Finset.univ.erase i0, X (Sum.inl j) * X (Sum.inr j)


variable (K) in
def psiF (K : Type) [Field K] (i0 : Fin k) : Fin k ⊕ Fin k → Pol K k :=
  Sum.elim (fun j => X (Sum.inl j))
    (fun j => if j = i0 then - tp K i0 else X (Sum.inl i0) * X (Sum.inr j))

theorem chiF_eq (i0 : Fin k) (v : Fin k ⊕ Fin k) :
    (chiF K i0 v : Pol K k) = X v * X (Sum.inl i0) ^ (wxi k v) := by
  rcases v with j | j <;> simp [chiF, wxi, mul_comm]

theorem chi_monomial (i0 : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) (c : K) :
    aeval (chiF K i0) (monomial m c : Pol K k) =
      X (Sum.inl i0) ^ (Finsupp.weight (wxi k) m) * monomial m c := by
  rw [aeval_monomial, monomial_eq, Finsupp.weight_apply, algebraMap_eq]
  simp only [chiF_eq, mul_pow, Finsupp.prod_mul, ← pow_mul']
  simp only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  ring

theorem chi_eq (i0 : Fin k) (d : ℕ) (f : Pol K k) (hf : IsWeightedHomogeneous (wxi k) f d) :
    aeval (chiF K i0) f = X (Sum.inl i0) ^ d * f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [chi_monomial, hf (mem_support_iff.1 hm)]

theorem chi_psi_dvd (i0 : Fin k) (f : Pol K k) :
    tt K k ∣ aeval (chiF K i0) f - aeval (psiF K i0) f := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have key : (Ideal.Quotient.mkₐ K (Ideal.span {tt K k})).comp (aeval (chiF K i0)) =
      (Ideal.Quotient.mkₐ K (Ideal.span {tt K k})).comp (aeval (psiF K i0)) := by
    ext v
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rcases v with j | j
    · simp [chiF, psiF]
    · by_cases hj : j = i0
      · subst hj
        simp only [chiF, psiF, Sum.elim_inr, if_true, eq_self_iff_true]
        have e : X (Sum.inl j) * X (Sum.inr j) - -tp K j = tt K k := by
          rw [sub_neg_eq_add, tp, tt, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        rw [e]
      · simp [chiF, psiF, hj]
  exact AlgHom.congr_fun key f

theorem eval_aeval' (g : Fin k ⊕ Fin k → Pol K k) (p : Fin k ⊕ Fin k → K) (f : Pol K k) :
    eval p (aeval g f) = eval (fun v => eval p (g v)) f := by
  induction f using MvPolynomial.induction_on <;> simp_all

theorem psi_zero (i0 : Fin k) (f : Pol K k)
    (hv : ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) :
    aeval (psiF K i0) f = 0 := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply MvPolynomial.funext
  intro p
  rw [eval_aeval', map_zero]
  apply hv
  have key : ∀ i, eval p (psiF K i0 (Sum.inr i)) =
      if i = i0 then -(∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j))
      else p (Sum.inl i0) * p (Sum.inr i) := by
    intro i
    by_cases h : i = i0
    · subst h
      simp [psiF, tp]
    · simp [psiF, h]
  have key2 : ∀ i, eval p (psiF K i0 (Sum.inl i)) = p (Sum.inl i) := by
    intro i
    simp [psiF]
  simp only [key, key2]
  have h3 : ∑ i ∈ Finset.univ.erase i0, p (Sum.inl i) *
      (if i = i0 then -(∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j))
        else p (Sum.inl i0) * p (Sum.inr i))
      = p (Sum.inl i0) * ∑ j ∈ Finset.univ.erase i0, p (Sum.inl j) * p (Sum.inr j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), h3, if_pos rfl]
  ring

theorem dvd_pow_mul (i0 : Fin k) (d : ℕ) (f : Pol K k) (hf : f ∈ Bihom K k d)
    (hv : ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) :
    tt K k ∣ X (Sum.inl i0) ^ d * f := by
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  have hfxi : IsWeightedHomogeneous (wxi k) f d := by
    have h2 := (Submodule.mem_inf.1 hf').2
    rwa [mem_weightedHomogeneousSubmodule] at h2
  have h := chi_psi_dvd i0 f
  rw [psi_zero i0 f hv, sub_zero, chi_eq i0 d f hfxi] at h
  exact h

theorem divT_one (d : ℕ) (hd : 1 ≤ d) (f : Pol K 1) (hf : f ∈ Bihom K 1 d) : tt K 1 ∣ f := by
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx 1) d ⊓ weightedHomogeneousSubmodule K (wxi 1) d := hf
  have hx := (Submodule.mem_inf.1 hf').1
  have hxi := (Submodule.mem_inf.1 hf').2
  rw [mem_weightedHomogeneousSubmodule] at hx hxi
  obtain ⟨s, hs⟩ : ∃ s : Fin 1 ⊕ Fin 1 →₀ ℕ,
      s = Finsupp.single (Sum.inl 0) 1 + Finsupp.single (Sum.inr 0) 1 := ⟨_, rfl⟩
  rw [f.as_sum]
  refine Finset.dvd_sum fun m hm => ?_
  have h1 := hx (mem_support_iff.1 hm)
  have h2 := hxi (mem_support_iff.1 hm)
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, wxi, Fintype.sum_sum_type] at h1 h2
  have hsm : s ≤ m := by
    rw [hs, Finsupp.le_def]
    intro v
    rcases v with i | i <;> obtain rfl := Subsingleton.elim i 0 <;> simp <;> omega
  have key : monomial m (AddMonoidAlgebra.coeff f m) = tt K 1 * monomial (m - s) (AddMonoidAlgebra.coeff f m) := by
    simp only [tt, Fin.sum_univ_one, X, monomial_mul, one_mul]
    rw [← hs, add_tsub_cancel_of_le hsm]
  rw [key]
  exact dvd_mul_right _ _

theorem divT : PI.OpWords.DivT := by
  intro K _ _ k d hd f hf hv
  have hf' : f ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d := hf
  have hfx : IsWeightedHomogeneous (wx k) f d := by
    have h1 := (Submodule.mem_inf.1 hf').1
    rwa [mem_weightedHomogeneousSubmodule] at h1
  have hfxi : IsWeightedHomogeneous (wxi k) f d := by
    have h2 := (Submodule.mem_inf.1 hf').2
    rwa [mem_weightedHomogeneousSubmodule] at h2
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [mul_zero]
    ext m
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_contra h
    have h1 := hfx h
    have h2 : m = 0 := by
      ext v
      rcases v with i | i <;> exact i.elim0
    rw [h2, map_zero] at h1
    omega
  · have hdvd : tt K k ∣ f := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · obtain rfl : k = 1 := by omega
        exact divT_one d hd f hf
      · exact dvd_of_dvd_X_pow (not_X_dvd_tt (⟨0, by omega⟩ : Fin k) ⟨1, by omega⟩
          (by simp [Fin.ext_iff])) d (dvd_pow_mul _ d f hf hv)
    obtain ⟨g, rfl⟩ := hdvd
    have e : 1 + (d - 1) = d := by omega
    refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
    · rw [mem_weightedHomogeneousSubmodule]
      exact homog_of_mul (wx k) isWeightedHomogeneous_pairing_left (tt_ne_zero hk1) (by rw [e]; exact hfx)
    · rw [mem_weightedHomogeneousSubmodule]
      exact homog_of_mul (wxi k) tt_homog_xi (tt_ne_zero hk1) (by rw [e]; exact hfxi)

end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords

theorem PI.OpWords.pairingDivisibility : PI.OpWords.DivT := PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.divT
end
end

namespace PI.OpWords

theorem opBound_of_vanish (hV : Vanish) : Formalism.MainNotions.TestSideCounting.OpBound :=
  opWords_of symbolMapInjective symbolMapMulLeft symbolMapMulRight symbolMapBihomogeneous weightOfEigenvector
    polarizationBihomogeneous rttRelation pairingWeightCancel pairingDivisibility hV pairingPowMemSymbolRange

end PI.OpWords
