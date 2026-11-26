module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoeffSmulX

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FunctionalRepresentationByContraction
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.XPderivMono
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContractionFirstOperatorAdjoint
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivZeroSecondFamily
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool) where
  toFun k := (k.1, k.2.1, !k.2.2)
  invFun k := (k.1, k.2.1, !k.2.2)
  left_inv k := by simp
  right_inv k := by simp

@[simp] theorem pE_apply (k : Fin m × Fin n × Bool) : pE k = (k.1, k.2.1, !k.2.2) := rfl

@[simp] theorem pE_pE (k : Fin m × Fin n × Bool) : pE (pE k) = k := by simp

theorem pE_symm : (pE : (Fin m × Fin n × Bool) ≃ (Fin m × Fin n × Bool)).symm = pE := rfl

theorem first_family_partner_iff (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) : inF1 ε (pE k) ↔ ¬ inF1 ε k := by
  obtain ⟨a, i, b⟩ := k; simp only [pE_apply, inF1]; cases b <;> cases ε a <;> simp

theorem mem_first_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F1 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, inF1 ε k := by
  unfold F1
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (MvPolynomial.mem_vars_iff_mem_support k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (MvPolynomial.mem_vars_iff_mem_support k).mp hk; exact h s hs k hk'

theorem mem_second_family_iff (ε : Fin m → Bool) (p : PX m n) : p ∈ F2 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, ¬ inF1 ε k := by
  unfold F2
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (MvPolynomial.mem_vars_iff_mem_support k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (MvPolynomial.mem_vars_iff_mem_support k).mp hk; exact h s hs k hk'

theorem pderiv_mem_supported (S : Set (Fin m × Fin n × Bool)) (k) {p : PX m n} (hp : p ∈ supported ℂ S) :
    pderiv k p ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, _, rfl⟩ := hx
    rw [pderiv_X]
    rcases eq_or_ne j k with rfl | h
    · simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subalgebra.zero_mem _
  | algebraMap r => simp [Subalgebra.zero_mem]
  | add x y _ _ hx hy => rw [map_add (f := pderiv k)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hx'' : x ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hx'
    have hy'' : y ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hy'
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx'' hy) (Subalgebra.mul_mem _ hy'' hx)

theorem partial_deriv_mem_first_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p ∈ F1 ε :=
  pderiv_mem_supported _ k hp

theorem partial_deriv_mem_second_family (ε : Fin m → Bool) (k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p ∈ F2 ε :=
  pderiv_mem_supported _ k hp

theorem variable_mul_mem_first_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : X k * p ∈ F1 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

theorem variable_mul_mem_second_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : X k * p ∈ F2 ε :=
  Subalgebra.mul_mem _ (MvPolynomial.X_mem_supported.mpr hk) hp

theorem partial_deriv_zero_first_family (ε : Fin m → Bool) {k} (hk : ¬ inF1 ε k) {p : PX m n} (hp : p ∈ F1 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (MvPolynomial.mem_vars_iff_mem_support k).mp hv
  exact hk ((mem_first_family_iff ε p).mp hp s hs k hks)

theorem partial_deriv_zero_second_family (ε : Fin m → Bool) {k} (hk : inF1 ε k) {p : PX m n} (hp : p ∈ F2 ε) : pderiv k p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨s, hs, hks⟩ := (MvPolynomial.mem_vars_iff_mem_support k).mp hv
  exact (mem_second_family_iff ε p).mp hp s hs k hks hk

def piC (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false)))

def Bal (s : Fin m × Fin n × Bool →₀ ℕ) : Prop := ∀ a i, s (a, i, false) = s (a, i, true)

instance (s : Fin m × Fin n × Bool →₀ ℕ) : Decidable (Bal s) := by unfold Bal; infer_instance

theorem contr_eqS (c : ℝ) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) {p : PX m n} (hp : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, if Bal s then p.coeff s * piC c s else 0 := by
  unfold contr
  refine Finset.sum_subset hp fun s _ hs => ?_
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eqS c (p.support ∪ q.support) MvPolynomial.support_add, contr_eqS c (p.support ∪ q.support) Finset.subset_union_left,
    contr_eqS c (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [MvPolynomial.coeff_add, add_mul]

theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eqS c p.support MvPolynomial.support_smul, contr_eqS c p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [coeff_smul, mul_assoc]

theorem contr_sum (c : ℝ) {ι : Type} (I : Finset ι) (f : ι → PX m n) : contr c (∑ i ∈ I, f i) = ∑ i ∈ I, contr c (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [contr]
  | insert a I ha ih => rw [Finset.sum_insert ha, contr_add, ih, Finset.sum_insert ha]

theorem contr_neg (c : ℝ) (p : PX m n) : contr c (-p) = -contr c p := by
  rw [show -p = (-1 : ℂ) • p by simp, contr_smul]; ring

theorem contr_sub (c : ℝ) (p q : PX m n) : contr c (p - q) = contr c p - contr c q := by
  rw [sub_eq_add_neg, contr_add, contr_neg]; ring

theorem contr_monomial (c : ℝ) (v : Fin m × Fin n × Bool →₀ ℕ) (d : ℂ) :
    contr c (monomial v d) = if Bal v then d * piC c v else 0 := by
  classical
  rw [contr_eqS c {v} ((support_monomial_subset).trans (by simp)), Finset.sum_singleton]
  simp [coeff_monomial]

theorem bal_iff (ε : Fin m → Bool) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) : Bal (s + u) ↔ s = u.mapDomain pE := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  constructor
  · intro hb
    ext ⟨a, i, b⟩
    rw [Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply]
    have hb' := hb a i
    simp only [Finsupp.add_apply] at hb'
    cases b <;> cases hεa : ε a
    · have h1 := hs0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, true) (by simp [inF1, hεa])
      simp only [Bool.not_false]; omega
    · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hs0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
    · have h1 := hs0 (a, i, true) (by simp [inF1, hεa])
      have h2 := hu0 (a, i, false) (by simp [inF1, hεa])
      simp only [Bool.not_true]; omega
  · intro h a i
    rw [h]
    simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
    ring

theorem piC_eq_wt (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ}
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (h : s = u.mapDomain pE) : piC c (s + u) = (wt c s : ℂ) := by
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  rw [wt_univ]
  push_cast
  rw [Fintype.prod_prod_type]
  unfold piC
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_bool]
  subst h
  simp only [Finsupp.add_apply, Finsupp.mapDomain_equiv_apply, pE_symm, pE_apply, Bool.not_false, Bool.not_true]
  cases hεa : ε a
  · have h1 := hu0 (a, i, true) (by simp [inF1, hεa])
    rw [h1]; simp
  · have h1 := hu0 (a, i, false) (by simp [inF1, hεa])
    rw [h1]; simp [mul_comm]

theorem contr_mono (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (a b : ℂ) :
    contr c (monomial s a * monomial u b) = if s = u.mapDomain pE then a * b * (wt c s : ℂ) else 0 := by
  rw [monomial_mul, contr_monomial]
  by_cases h : s = u.mapDomain pE
  · rw [if_pos ((bal_iff ε hs hu).mpr h), if_pos h, piC_eq_wt ε c hu h]
  · rw [if_neg (fun hb => h ((bal_iff ε hs hu).mp hb)), if_neg h]

theorem contr_eq_bf (ε : Fin m → Bool) (c : ℝ) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (h * g) = bf (fun s => (wt c s : ℂ)) h (rename pE g) := by
  conv_lhs => rw [h.as_sum, g.as_sum, Finset.sum_mul_sum, contr_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [h.as_sum, g.as_sum, map_sum, bf_sum_left]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [contr_sum, bf_sum_right]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [contr_mono ε c ((mem_first_family_iff ε h).mp hh s hs) ((mem_second_family_iff ε g).mp hg u hu), rename_monomial, bf_monomial]

theorem T1 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X k * h * g) = ((2 * c : ℝ) : ℂ) * contr c (h * pderiv (pE k) g) := by
  rw [contr_eq_bf ε c (variable_mul_mem_first_family ε hk hh) hg, contr_eq_bf ε c hh (partial_deriv_mem_second_family ε _ hg), bf_X_mul _ (wt_step c)]
  congr 2
  have := pderiv_rename (R := ℂ) (τ := Fin m × Fin n × Bool) (σ := Fin m × Fin n × Bool) pE.injective (pE k) g
  rw [pE_pE] at this
  exact this

theorem T2 (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) * contr c (pderiv k h * g) = contr c (h * (X (pE k) * g)) := by
  rw [contr_eq_bf ε c (partial_deriv_mem_first_family ε _ hh) hg,
    contr_eq_bf ε c hh (variable_mul_mem_second_family ε (fun h' => (first_family_partner_iff ε k).mp h' hk) hg), bf_pderiv _ (wt_step c)]
  congr 1
  rw [map_mul, rename_X, pE_pE]

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem tA (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * pderiv (b, i, false) h * g) = contr c (h * (X (b, i, true) * pderiv (a, i, true) g)) := by
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (partial_deriv_mem_first_family ε (b, i, false) hh) hg
  have h2 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false] at h1 h2
  rw [h1, h2]

theorem tB (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (b, i, true) * pderiv (a, i, true) h * g) = contr c (h * (X (a, i, false) * pderiv (b, i, false) g)) := by
  have h1 := T1 ε (c := c) (k := (b, i, true)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (partial_deriv_mem_second_family ε (b, i, false) hg)
  simp only [pE_apply, Bool.not_true] at h1 h2
  rw [h1, h2]

theorem tC (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * X (b, i, true) * h * g) =
      ((2 * c : ℝ) : ℂ) ^ 2 * contr c (h * pderiv (b, i, false) (pderiv (a, i, true) g)) := by
  have hbT : inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (variable_mul_mem_first_family ε hbT hh) hg
  have h2 := T1 ε (c := c) (k := (b, i, true)) hbT hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [mul_assoc (X (a, i, false)), h1, h2]; ring

theorem tD (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) ^ 2 * contr c (pderiv (b, i, false) (pderiv (a, i, true) h) * g) =
      contr c (h * (X (a, i, false) * X (b, i, true) * g)) := by
  have hbT : ¬ inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (variable_mul_mem_second_family ε hbT hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [pow_two, mul_assoc, h1, h2, mul_assoc]

theorem contraction_first_operator_adjoint (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (a b : Fin m) {h g : PX m n} (hh : h ∈ F1 ε)
    (hg : g ∈ F2 ε) : contr c (D1 ε c a b h * g) = -contr c (h * D2 ε c a b g) := by
  have hc2 : ((2 * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * c) ≠ 0)
  unfold D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_mul, contr_sum, mul_neg, contr_neg, Finset.mul_sum, contr_sum, neg_neg]
      exact Finset.sum_congr rfl fun i _ => tB ε hc ha hb i hh hg
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      rw [neg_mul, contr_neg, Finset.sum_mul, contr_sum, Finset.mul_sum, contr_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => tA ε hc ha hb i hh hg
  · rw [if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [← tD ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [tC ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem dop_split (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) :
    Dop ε c a b (f * g) = D1 ε c a b f * g + f * D2 ε c a b g := by
  have hL : ∀ k, pderiv k (f * g) = f * pderiv k g + g * pderiv k f := fun k => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hL2 : ∀ k (p q : PX m n), pderiv k (p * q) = p * pderiv k q + q * pderiv k p := fun k p q => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  unfold Dop D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf]
      ring
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul, mul_neg, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      ring
  · rw [if_neg hab, if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, map_add (f := _), hL2 _ f, hL2 _ g, partial_deriv_zero_second_family ε (k := (a, i, true)) (by simp [inF1, ha]) hg,
        partial_deriv_zero_second_family ε (k := (b, i, false)) (by simp [inF1, hb]) hg]
      simp only [mul_zero, zero_add, add_zero, zero_mul, map_zero, smul_eq_C_mul]
      ring
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, neg_mul, mul_neg,
        neg_smul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hL, partial_deriv_zero_first_family ε (k := (a, i, true)) (by simp [inF1, ha]) hf, mul_zero, add_zero, hL2 _ f,
        partial_deriv_zero_first_family ε (k := (b, i, false)) (by simp [inF1, hb]) hf, mul_zero, add_zero]
      simp only [smul_eq_C_mul]
      ring

theorem X_pderiv_mono (k : Fin m × Fin n × Bool) (v : Fin m × Fin n × Bool →₀ ℕ) :
    (X k * pderiv k (monomial v (1 : ℂ)) : PX m n) = ((v k : ℕ) : ℂ) • monomial v 1 := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : v k = 0
  · simp [h0]
  · rw [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)), smul_monomial, smul_eq_mul,
      mul_one]

theorem centre (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k)
    (hr : rdeg ε s ≠ rdeg ε (u.mapDomain pE)) : Λ (monomial s 1 * monomial u 1) = 0 := by
  have hs0 : ∀ k, ¬ inF1 ε k → s k = 0 := fun k hk => by
    by_contra h; exact hk (hs k (Finsupp.mem_support_iff.mpr h))
  have hu0 : ∀ k, inF1 ε k → u k = 0 := fun k hk => by
    by_contra h; exact hu k (Finsupp.mem_support_iff.mpr h) hk
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hr
  rw [monomial_mul, one_mul]
  have hD : Dop ε c a a (monomial (s + u) (1 : ℂ)) =
      ((∑ i, ((s + u) (a, i, true) : ℂ)) - ∑ i, ((s + u) (a, i, false) : ℂ)) • monomial (s + u) 1 := by
    unfold Dop
    rw [if_pos rfl]
    simp only [X_pderiv_mono, ← Finset.sum_sub_distrib, Finset.sum_smul, sub_smul]
  have h0 := hΛ a a (monomial (s + u) 1)
  rw [hD, map_smul, smul_eq_mul] at h0
  refine (mul_eq_zero.mp h0).resolve_left ?_
  have hm (k : Fin m × Fin n × Bool) : (u.mapDomain pE) k = u (pE.symm k) :=
    Finsupp.mapDomain_equiv_apply u k
  simp only [rdeg] at ha
  simp only [hm] at ha
  simp only [pE_symm, pE_apply, Bool.not_not] at ha
  rw [← ne_eq, sub_ne_zero]
  simp only [Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  cases hεa : ε a
  · have e1 : ∀ i, u (a, i, true) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, false) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_false] at ha
    intro h; apply ha; exact_mod_cast h
  · have e1 : ∀ i, u (a, i, false) = 0 := fun i => hu0 _ (by simp [inF1, hεa])
    have e2 : ∀ i, s (a, i, true) = 0 := fun i => hs0 _ (by simp [inF1, hεa])
    simp only [e1, e2, Nat.cast_zero, Finset.sum_const_zero, add_zero, zero_add]
    rw [hεa] at ha
    simp only [Bool.not_true] at ha
    intro h; apply ha; exact_mod_cast h.symm

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

def cand (ε : Fin m → Bool) (r : Fin m → ℕ) : Finset (Fin m × Fin n × Bool →₀ ℕ) :=
  ((Fintype.piFinset fun _ : Fin m × Fin n × Bool => Finset.range (∑ a, r a + 1)).image
    Finsupp.equivFunOnFinite.symm).filter (fun t => (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r)

theorem le_rdeg (ε : Fin m → Bool) (t : Fin m × Fin n × Bool →₀ ℕ) (k) (hk : inF1 ε k) : t k ≤ rdeg ε t k.1 := by
  obtain ⟨a, i, b⟩ := k
  simp only [inF1] at hk
  subst hk
  unfold rdeg
  exact Finset.single_le_sum (f := fun i' => t (a, i', !ε a)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem mem_cand (ε : Fin m → Bool) (r : Fin m → ℕ) (t : Fin m × Fin n × Bool →₀ ℕ) :
    t ∈ cand ε r ↔ (∀ k ∈ t.support, inF1 ε k) ∧ rdeg ε t = r := by
  unfold cand
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_image]
  refine ⟨⇑t, ?_, by simp⟩
  rw [Fintype.mem_piFinset]
  intro k
  rw [Finset.mem_range, Nat.lt_succ_iff]
  by_cases hk : inF1 ε k
  · calc t k ≤ rdeg ε t k.1 := le_rdeg ε t k hk
      _ = r k.1 := by rw [h.2]
      _ ≤ ∑ a, r a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  · have : t k = 0 := by
      by_contra h0; exact hk (h.1 k (Finsupp.mem_support_iff.mpr h0))
    rw [this]; exact Nat.zero_le _

def Bm (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  if ∀ k ∈ s.support, inF1 ε k then
    ∑ t ∈ cand ε (rdeg ε s), (Λ (monomial s 1 * monomial (t.mapDomain pE) 1) / (wt c t : ℂ)) • monomial t 1
  else 0

def Bop (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) : Module.End ℂ (PX m n) :=
  (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr ℂ (Bm ε c Λ)

theorem Bop_mono (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    Bop ε c Λ (monomial s 1) = Bm ε c Λ s := by
  have := (MvPolynomial.basisMonomials (Fin m × Fin n × Bool) ℂ).constr_basis ℂ (Bm ε c Λ) s
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem as_sum' (p : PX m n) : p = ∑ s ∈ p.support, p.coeff s • monomial s (1 : ℂ) := by
  conv_lhs => rw [p.as_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem monomial_mem_first_family (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F1 ε := by
  rw [mem_first_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, if_neg (Ne.symm h)])
  subst this; exact ht

theorem monomial_mem_second_family (ε : Fin m → Bool) {t : Fin m × Fin n × Bool →₀ ℕ} (ht : ∀ k ∈ t.support, ¬ inF1 ε k) (d : ℂ) :
    (monomial t d : PX m n) ∈ F2 ε := by
  rw [mem_second_family_iff]
  intro s hs
  have : s = t := by
    by_contra h; exact (MvPolynomial.mem_support_iff.mp hs) (by rw [coeff_monomial, if_neg (Ne.symm h)])
  subst this; exact ht

theorem representing_monomial_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (s) : Bm ε c Λ s ∈ F1 ε := by
  unfold Bm
  split_ifs
  · exact Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (monomial_mem_first_family ε ((mem_cand ε _ t).mp ht).1 1)
  · exact Submodule.zero_mem _

theorem representing_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (p : PX m n) : Bop ε c Λ p ∈ F1 ε := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [as_sum' p, map_sum]
  exact Submodule.sum_mem _ fun s _ => by rw [map_smul, Bop_mono]; exact Submodule.smul_mem _ _ (representing_monomial_mem_first_family ε c Λ s)

theorem mapDomain_pE_pE (u : Fin m × Fin n × Bool →₀ ℕ) : (u.mapDomain pE).mapDomain pE = u := by
  rw [← Finsupp.mapDomain_comp]
  have h : (pE : Fin m × Fin n × Bool → Fin m × Fin n × Bool) ∘ pE = id := by
    funext k
    exact pE_pE k
  rw [h, Finsupp.mapDomain_id]

theorem partner_support_first_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff, not_not] at this

theorem partner_support_second_family (ε : Fin m → Bool) {u : Fin m × Fin n × Bool →₀ ℕ} (hu : ∀ k ∈ u.support, inF1 ε k) :
    ∀ k ∈ (u.mapDomain pE).support, ¬ inF1 ε k := by
  intro k hk
  rw [Finsupp.mem_support_iff, Finsupp.mapDomain_equiv_apply, pE_symm] at hk
  have := hu (pE k) (Finsupp.mem_support_iff.mpr hk)
  rwa [first_family_partner_iff] at this

theorem key_mono (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    Λ (monomial s 1 * monomial u 1) = contr c (Bm ε c Λ s * monomial u 1) := by
  unfold Bm
  rw [if_pos hs, Finset.sum_mul, contr_sum]
  simp_rw [smul_mul_assoc, contr_smul]
  have e : ∀ t ∈ cand ε (rdeg ε s), contr c (monomial t 1 * monomial u 1) =
      if t = u.mapDomain pE then (wt c t : ℂ) else 0 := fun t ht => by
    rw [contr_mono ε c ((mem_cand ε _ t).mp ht).1 hu]; simp
  rw [Finset.sum_congr rfl fun t ht => by rw [e t ht]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rw [mapDomain_pE_pE, div_mul_cancel₀]
    exact_mod_cast (wt_pos hc _).ne'
  · refine centre ε c Λ hΛ hs hu fun h => hmem ?_
    rw [mem_cand]; exact ⟨partner_support_first_family ε hu, h.symm⟩

theorem functional_representation_by_contraction (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {f g : PX m n} (hf : f ∈ F1 ε) (hg : g ∈ F2 ε) : Λ (f * g) = contr c (Bop ε c Λ f * g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [as_sum' f, as_sum' g, Finset.sum_mul_sum, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [as_sum' f, map_sum, as_sum' g, Finset.sum_mul_sum, contr_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, contr_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, Bop_mono, smul_mul_smul_comm, map_smul, smul_mul_smul_comm, contr_smul,
    key_mono ε hc Λ hΛ ((mem_first_family_iff ε f).mp hf s hs) ((mem_second_family_iff ε g).mp hg u hu), smul_eq_mul]

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem first_operator_mem_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {f : PX m n} (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  unfold D1
  split_ifs with hab ha ha
  · refine (F1 ε).neg_mem ((F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ha]) (partial_deriv_mem_first_family ε _ hf))
  · exact (F1 ε).sum_mem fun i _ => variable_mul_mem_first_family ε (by simp [inF1, ← hab]; simpa using ha) (partial_deriv_mem_first_family ε _ hf)
  · have hb : ε b = false := by cases h' : ε b <;> simp_all
    refine (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_first_family ε (by simp [inF1, ha]) (variable_mul_mem_first_family ε (by simp [inF1, hb]) hf)
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    exact (F1 ε).smul_mem _ ((F1 ε).sum_mem fun i _ => partial_deriv_mem_first_family ε _ (partial_deriv_mem_first_family ε _ hf))

theorem second_operator_mem_second_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) {g : PX m n} (hg : g ∈ F2 ε) : D2 ε c a b g ∈ F2 ε := by
  unfold D2
  split_ifs with hab ha ha
  · exact (F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1, ← hab, ha]) (partial_deriv_mem_second_family ε _ hg)
  · refine (F2 ε).neg_mem ((F2 ε).sum_mem fun i _ => variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha)
      (partial_deriv_mem_second_family ε _ hg))
  · exact (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => partial_deriv_mem_second_family ε _ (partial_deriv_mem_second_family ε _ hg))
  · have hb : ε b = true := by cases h' : ε b <;> simp_all
    refine (F2 ε).smul_mem _ ((F2 ε).sum_mem fun i _ => ?_)
    rw [mul_assoc]
    exact variable_mul_mem_second_family ε (by simp [inF1]; simpa using ha) (variable_mul_mem_second_family ε (by simp [inF1, hb]) hg)

theorem bf_mono_right (w : (Fin m × Fin n × Bool →₀ ℕ) → ℂ) (p : PX m n) (t : Fin m × Fin n × Bool →₀ ℕ) :
    bf w p (monomial t 1) = p.coeff t * w t := by
  classical
  rw [bf_eq w (p.support ∪ {t}) Finset.subset_union_left ((support_monomial_subset).trans Finset.subset_union_right)]
  rw [Finset.sum_eq_single t]
  · simp [coeff_monomial]
  · intro s _ hs; simp [coeff_monomial, Ne.symm hs]
  · intro h; simp [coeff_monomial]; left; by_contra h'; exact h (Finset.mem_union_left _
      (MvPolynomial.mem_support_iff.mpr h'))

theorem nondeg (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {h : PX m n} (hh : h ∈ F1 ε)
    (h0 : ∀ u : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ u.support, ¬ inF1 ε k) → contr c (h * monomial u 1) = 0) : h = 0 := by
  ext s
  change h.coeff s = 0
  by_cases hs : ∀ k ∈ s.support, inF1 ε k
  · have hu := partner_support_second_family ε hs
    have := h0 (s.mapDomain pE) hu
    rw [contr_eq_bf ε c hh (monomial_mem_second_family ε hu 1), rename_monomial, mapDomain_pE_pE, bf_mono_right] at this
    exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast (wt_pos hc s).ne')
  · by_contra hne
    exact hs ((mem_first_family_iff ε h).mp hh s (MvPolynomial.mem_support_iff.mpr hne))

theorem Bop_box (ε : Fin m → Bool) (c : ℝ) (Λ : PX m n →ₗ[ℂ] ℂ) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, Bop ε c Λ f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => Bop ε c Λ x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    rw [Bop_mono]
    unfold Bm
    rw [if_pos hs]
    refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨htF, htr⟩ := (mem_cand ε _ t).mp ht
    exact ⟨t, htF, by rw [htr]; exact hR, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

end CoreC

open CoreC in
theorem repB : RepB := by
  intro m n ε c hc Λ hΛ
  refine ⟨Bop ε c Λ, fun R f hf => Bop_box ε c Λ R f hf, fun f hf g hg => functional_representation_by_contraction ε hc Λ hΛ hf hg, ?_⟩
  intro a b f hf
  have hB1 : Bop ε c Λ (D1 ε c a b f) ∈ F1 ε := representing_operator_mem_first_family ε c Λ _
  have hB2 : D1 ε c a b (Bop ε c Λ f) ∈ F1 ε := first_operator_mem_first_family ε c a b (representing_operator_mem_first_family ε c Λ f)
  rw [← sub_eq_zero]
  refine nondeg ε hc (Submodule.sub_mem _ hB1 hB2) fun u hu => ?_
  have hg : (monomial u (1 : ℂ) : PX m n) ∈ F2 ε := monomial_mem_second_family ε hu 1
  rw [sub_mul, contr_sub, ← functional_representation_by_contraction ε hc Λ hΛ (first_operator_mem_first_family ε c a b hf) hg,
    contraction_first_operator_adjoint ε hc a b (representing_operator_mem_first_family ε c Λ f) hg, ← functional_representation_by_contraction ε hc Λ hΛ hf (second_operator_mem_second_family ε c a b hg), sub_neg_eq_add,
    ← map_add, ← dop_split ε c a b hf hg, hΛ]

end PositivityTheory.Rg.Sw.LC
