module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PairSym

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FirstFamilySymbolMulVariablePow
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ComapDomainInlAdd
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool

abbrev Dk (k : Ix m n) : Module.End ℂ (PX m n) := (pderiv (R := ℂ) k).toLinearMap

theorem pderiv_comm (i j : Ix m n) (p : PX m n) : pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have hc : ∀ a b : Ix m n, pderiv a (pderiv b (X k : PX m n)) = 0 := by
      intro a b; rw [pderiv_X]; by_cases h : b = k
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [pderiv_mul, map_add (f := _), hp, hc, mul_zero, add_zero]
    ring

theorem dk_comm (i j : Ix m n) : Commute (Dk i) (Dk j) :=
  LinearMap.ext fun p => pderiv_comm i j p

def dvE (e : Ix m n → ℕ) : Module.End ℂ (PX m n) :=
  ((Finset.univ : Finset (Ix m n)).toList.map fun k => Dk k ^ e k).prod

theorem list_dv_mul (l : List (Ix m n)) (a b : Ix m n → ℕ) :
    (l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod = (l.map fun k => Dk k ^ (a k + b k)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hc : Commute (l.map fun k => Dk k ^ a k).prod (Dk x ^ b x) := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨z, -, rfl⟩ := hy
      exact ((dk_comm x z).pow_pow _ _)
    calc Dk x ^ a x * (l.map fun k => Dk k ^ a k).prod * (Dk x ^ b x * (l.map fun k => Dk k ^ b k).prod)
        = Dk x ^ a x * ((l.map fun k => Dk k ^ a k).prod * Dk x ^ b x) * (l.map fun k => Dk k ^ b k).prod := by
          simp only [mul_assoc]
      _ = Dk x ^ a x * (Dk x ^ b x * (l.map fun k => Dk k ^ a k).prod) * (l.map fun k => Dk k ^ b k).prod := by
          rw [hc.eq]
      _ = Dk x ^ (a x + b x) * ((l.map fun k => Dk k ^ a k).prod * (l.map fun k => Dk k ^ b k).prod) := by
          simp only [pow_add, mul_assoc]
      _ = _ := by rw [ih]

theorem dvE_mul (a b : Ix m n → ℕ) : dvE a * dvE b = dvE (a + b) := by
  unfold dvE; rw [list_dv_mul]; rfl

theorem dvE_single (k : Ix m n) : dvE (Pi.single k 1) = Dk k := by
  unfold dvE
  rw [List.prod_map_eq_pow_single k]
  · simp only [Pi.single_eq_same, pow_one]
    convert pow_one (Dk k)
    exact @List.count_eq_one_of_mem _ instBEqOfDecidableEq inferInstance _ _ (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ k))
  · intro a' ha' _
    simp [Pi.single_apply, ha']

theorem opMono_eq (t : Ix m n ⊕ Ix m n →₀ ℕ) (f : PX m n) :
    opMono t f = monomial (t.comapDomain Sum.inl Sum.inl_injective.injOn) 1 * dvE (fun k => t (Sum.inr k)) f := rfl

theorem opMono_add (t : Ix m n ⊕ Ix m n →₀ ℕ) (f g : PX m n) : opMono t (f + g) = opMono t f + opMono t g := by
  simp only [opMono_eq, map_add (f := _), mul_add]

theorem opMono_smul (t : Ix m n ⊕ Ix m n →₀ ℕ) (a : ℂ) (f : PX m n) : opMono t (a • f) = a • opMono t f := by
  simp only [opMono_eq, map_smul, mul_smul_comm]

theorem op_eq_of_subset (s : Sym m n) (S : Finset (Ix m n ⊕ Ix m n →₀ ℕ)) (h : s.support ⊆ S) (f : PX m n) :
    op s f = ∑ t ∈ S, s.coeff t • opMono t f := by
  unfold op
  apply Finset.sum_subset h
  intro t _ ht
  rw [MvPolynomial.notMem_support_iff.1 ht, zero_smul]

theorem op_add (u v : Sym m n) (f : PX m n) : op (u + v) f = op u f + op v f := by
  classical
  rw [op_eq_of_subset (u + v) (u.support ∪ v.support) MvPolynomial.support_add,
    op_eq_of_subset u (u.support ∪ v.support) Finset.subset_union_left,
    op_eq_of_subset v (u.support ∪ v.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [MvPolynomial.coeff_add, add_smul]

theorem op_smul (a : ℂ) (u : Sym m n) (f : PX m n) : op (a • u) f = a • op u f := by
  classical
  rw [op_eq_of_subset (a • u) u.support MvPolynomial.support_smul, op, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_smul]

theorem op_zero (f : PX m n) : op (0 : Sym m n) f = 0 := by simp [op]

theorem op_sum {ι : Type*} (S : Finset ι) (u : ι → Sym m n) (f : PX m n) : op (∑ i ∈ S, u i) f = ∑ i ∈ S, op (u i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add, ih]

theorem op_monomial (t : Ix m n ⊕ Ix m n →₀ ℕ) (a : ℂ) (f : PX m n) : op (monomial t a) f = a • opMono t f := by
  classical
  rw [op_eq_of_subset _ {t} (MvPolynomial.support_monomial_subset), Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem op_add_f (u : Sym m n) (f g : PX m n) : op u (f + g) = op u f + op u g := by
  simp only [op, opMono_add, smul_add, Finset.sum_add_distrib]

theorem op_smul_f (u : Sym m n) (a : ℂ) (f : PX m n) : op u (a • f) = a • op u f := by
  simp only [op, opMono_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_comm]

theorem op_zero_f (u : Sym m n) : op u 0 = 0 := by simp [op, opMono_eq]

theorem dvE_zero : dvE (0 : Ix m n → ℕ) = 1 := by
  unfold dvE; simp

theorem op_C (a : ℂ) (f : PX m n) : op (C a : Sym m n) f = a • f := by
  rw [← monomial_zero', op_monomial, opMono_eq]
  have h0 : (fun k : Ix m n => (0 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) = 0 := by ext; simp
  rw [h0, dvE_zero, Finsupp.comapDomain_zero]
  simp

theorem comapDomain_inl_add (t s : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t + s).comapDomain Sum.inl Sum.inl_injective.injOn =
      t.comapDomain Sum.inl Sum.inl_injective.injOn + s.comapDomain Sum.inl Sum.inl_injective.injOn := by
  ext k; simp [Finsupp.comapDomain_apply]

theorem opMono_add_inl (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inl k) 1) f = X k * opMono t f := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inl k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn =
      Finsupp.single k 1 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inl k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) = fun j => t (Sum.inr j) := by
    ext j; simp [Finsupp.single_apply]
  rw [h1, h2, monomial_add_single, pow_one]
  ring

theorem opMono_add_inr (t : Ix m n ⊕ Ix m n →₀ ℕ) (k : Ix m n) (f : PX m n) :
    opMono (t + Finsupp.single (Sum.inr k) 1) f = opMono t (pderiv k f) := by
  rw [opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, Finsupp.single_apply]
  have h2 : (fun j : Ix m n => (t + Finsupp.single (Sum.inr k) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr j)) =
      (fun j => t (Sum.inr j)) + Pi.single k 1 := by
    ext j; simp [Finsupp.single_apply, Pi.single_apply, eq_comm]
  rw [h1, add_zero, h2, ← dvE_mul, dvE_single]
  rfl

theorem op_mul_inl (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inl k)) f = X k * op u f := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inl, mul_smul_comm]

theorem op_mul_inr (u : Sym m n) (k : Ix m n) (f : PX m n) : op (u * X (Sum.inr k)) f = op u (pderiv k f) := by
  classical
  conv_lhs => rw [u.as_sum, Finset.sum_mul]
  rw [op_sum]
  conv_rhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [X, monomial_mul, mul_one, op_monomial, opMono_add_inr]

theorem op_X_mul (u : Sym m n) : ∀ (k : Ix m n) (g : PX m n),
    op u (X k * g) = X k * op u g + op (pderiv (Sum.inr k) u) g := by
  induction u using MvPolynomial.induction_on with
  | C a => intro k g; simp [op_C, op_zero, mul_smul_comm]
  | add p q hp hq => intro k g; rw [op_add, op_add, hp, hq, map_add (f := _), op_add]; ring
  | mul_X p j hp =>
    intro k g
    rcases j with j | j
    · rw [op_mul_inl, op_mul_inl, hp, pderiv_mul, pderiv_X, op_add, op_mul_inl]
      simp only [Pi.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, mul_zero, op_zero, add_zero]
      ring
    · rw [op_mul_inr, op_mul_inr, pderiv_mul, pderiv_mul, pderiv_X, pderiv_X, op_add_f, op_add, hp, op_mul_inr]
      by_cases h : j = k
      · subst h
        simp only [Pi.single_apply, if_true, mul_one, one_mul]
        ring
      · have h' : (Sum.inr k : Ix m n ⊕ Ix m n) ≠ Sum.inr j := fun e => h (Sum.inr_injective e).symm
        have e1 : ¬ (k = j) := fun e => h e.symm
        have e2 : ¬ ((Sum.inr j : Ix m n ⊕ Ix m n) = Sum.inr k) := fun e => h (Sum.inr_injective e)
        simp only [Pi.single_apply, e1, e2, if_false, zero_mul, mul_zero, op_zero, add_zero, op_zero_f, zero_add]

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

def Good (ε : Fin m → Bool) (d : ℕ) (r : Sym m n) : Prop := SymbolInFirstFamily ε r ∧ EtaLt r d

theorem good_zero (d : ℕ) : Good ε d (0 : Sym m n) := by
  constructor <;> intro t ht <;> simp at ht

theorem good_add {d : ℕ} {r₁ r₂ : Sym m n} (h₁ : Good ε d r₁) (h₂ : Good ε d r₂) : Good ε d (r₁ + r₂) := by
  classical
  constructor
  · intro t ht k hk
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.1 t h k hk
    · exact h₂.1 t h k hk
  · intro t ht
    rcases Finset.mem_union.1 (MvPolynomial.support_add ht) with h | h
    · exact h₁.2 t h
    · exact h₂.2 t h

theorem good_smul {d : ℕ} {r : Sym m n} (a : ℂ) (h : Good ε d r) : Good ε d (a • r) :=
  ⟨fun t ht => h.1 t (MvPolynomial.support_smul ht), fun t ht => h.2 t (MvPolynomial.support_smul ht)⟩

theorem good_sum {ι : Type*} (S : Finset ι) {d : ℕ} (r : ι → Sym m n) (h : ∀ i ∈ S, Good ε d (r i)) :
    Good ε d (∑ i ∈ S, r i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using good_zero d
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact good_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_support_mul_monomial {p : Sym m n} {s t' : Ix m n ⊕ Ix m n →₀ ℕ} {a : ℂ}
    (h : t' ∈ (p * monomial s a).support) : ∃ t ∈ p.support, t' = t + s := by
  rw [MvPolynomial.mem_support_iff, coeff_mul_monomial'] at h
  split_ifs at h with hs
  · refine ⟨t' - s, ?_, (tsub_add_cancel_of_le hs).symm⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0; rw [h0, zero_mul] at h; exact h rfl
  · exact absurd rfl h

theorem good_mul_monomial {d e : ℕ} {r : Sym m n} (h : Good ε d r) (s : Ix m n ⊕ Ix m n →₀ ℕ)
    (hs : ∀ k, (s (Sum.inl k) ≠ 0 ∨ s (Sum.inr k) ≠ 0) → inF1 ε k) (he : (∑ k, s (Sum.inr k)) ≤ e) :
    Good ε (d + e) (r * monomial s 1) := by
  constructor
  · intro t' ht' k hk
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t (Sum.inl k) ≠ 0 ∨ t (Sum.inr k) ≠ 0
    · exact h.1 t ht k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := mem_support_mul_monomial ht'
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    exact add_lt_add_of_lt_of_le (h.2 t ht) he

theorem mem_support_pderiv {u : Sym m n} {i : Ix m n ⊕ Ix m n} {t' : Ix m n ⊕ Ix m n →₀ ℕ}
    (h : t' ∈ (pderiv i u).support) : ∃ t ∈ u.support, t i ≠ 0 ∧ t = t' + Finsupp.single i 1 := by
  classical
  have hu : pderiv i u = ∑ t ∈ u.support, monomial (t - Finsupp.single i 1) (AddMonoidAlgebra.coeff u t * (t i : ℂ)) := by
    conv_lhs => rw [u.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  rw [MvPolynomial.mem_support_iff, hu, coeff_sum] at h
  obtain ⟨t, ht, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_monomial] at hne
  split_ifs at hne with heq
  · have hti : t i ≠ 0 := by
      intro h0; rw [h0] at hne; simp at hne
    refine ⟨t, ht, hti, ?_⟩
    rw [← heq, tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]; omega
  · exact absurd rfl hne

theorem good_pderiv {d : ℕ} {u : Sym m n} (hu : SymbolInFirstFamily ε u) (hue : EtaLe u d) (k : Ix m n) :
    Good ε d (pderiv (Sum.inr k) u) := by
  constructor
  · intro t' ht' j hj
    obtain ⟨t, ht, -, rfl⟩ := mem_support_pderiv ht'
    apply hu _ ht j
    simp only [Finsupp.add_apply, ne_eq] at hj ⊢
    omega
  · intro t' ht'
    obtain ⟨t, ht, hti, rfl⟩ := mem_support_pderiv ht'
    have h1 := hue _ ht
    have h3 : ∑ j, t' (Sum.inr j) + 1 ≤ d := by
      simpa [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply] using h1
    omega

theorem good_le {d : ℕ} {r : Sym m n} (h : Good ε d r) : EtaLe r d := fun t ht => (h.2 t ht).le

theorem first_family_symbol_mul_variable_pow {u : Sym m n} (hu : SymbolInFirstFamily ε u) {a : Ix m n} (ha : inF1 ε a) (b : ℕ) :
    SymbolInFirstFamily ε (u * X (Sum.inl a) ^ b) ∧ ∀ d, EtaLe u d → EtaLe (u * X (Sum.inl a) ^ b) d := by
  have hs : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
      (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
    intro k hk
    simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
    split_ifs at hk with h
    · subst h; exact ha
    · exact absurd rfl hk
  have h0 : (∑ k, (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ 0 := by
    simp [Finsupp.single_apply]
  rw [X_pow_eq_monomial]
  refine ⟨?_, fun d hd => ?_⟩
  · intro t ht k hk
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, ne_eq, Nat.add_eq_zero_iff, not_and_or] at hk
    by_cases h1 : t0 (Sum.inl k) ≠ 0 ∨ t0 (Sum.inr k) ≠ 0
    · exact hu t0 ht0 k h1
    · push_neg at h1
      apply hs k
      rcases hk with hk | hk
      · rcases hk with hk | hk
        · exact absurd h1.1 hk
        · exact Or.inl hk
      · rcases hk with hk | hk
        · exact absurd h1.2 hk
        · exact Or.inr hk
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := mem_support_mul_monomial ht
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    calc _ ≤ d + 0 := add_le_add (hd t0 ht0) h0
      _ = d := add_zero d

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators
end
end

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

theorem op_sum_f (u : Sym m n) {ι : Type*} (S : Finset ι) (c : ι → ℂ) (h : ι → PX m n) :
    op u (∑ i ∈ S, c i • h i) = ∑ i ∈ S, c i • op u (h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_f, op_smul_f, ih]

theorem kpow {a : Ix m n} (ha : inF1 ε a) (b : ℕ) : ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (X a ^ b * g) = op (u * X (Sum.inl a) ^ b) g + op r g := by
  induction b with
  | zero => intro d u _ _; exact ⟨0, good_zero d, fun g => by simp [op_zero]⟩
  | succ b ih =>
    intro d u hu hue
    obtain ⟨r₁, hr₁, e₁⟩ := ih d u hu hue
    have hdu := good_pderiv hu hue a
    obtain ⟨r₂, hr₂, e₂⟩ := ih d (pderiv (Sum.inr a) u) hdu.1 (good_le hdu)
    have hX : ∀ k, ((Finsupp.single (Sum.inl a) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (Finsupp.single (Sum.inl a) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
      split_ifs at hk with h
      · subst h; exact ha
      · exact absurd rfl hk
    have hXb : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
      split_ifs at hk with h
      · subst h; exact ha
      · exact absurd rfl hk
    have g1 : Good ε d (r₁ * X (Sum.inl a)) := by
      have := good_mul_monomial (e := 0) hr₁ _ hX (by simp [Finsupp.single_apply])
      simpa [X] using this
    have g2 : Good ε d (pderiv (Sum.inr a) u * X (Sum.inl a) ^ b) := by
      have := good_mul_monomial (e := 0) hdu _ hXb (by simp [Finsupp.single_apply])
      simpa [X_pow_eq_monomial] using this
    refine ⟨r₁ * X (Sum.inl a) + pderiv (Sum.inr a) u * X (Sum.inl a) ^ b + r₂, good_add (good_add g1 g2) hr₂, fun g => ?_⟩
    rw [pow_succ', mul_assoc, op_X_mul, e₁, e₂, op_add, op_add, op_mul_inl, pow_succ, ← mul_assoc, op_mul_inl]
    ring

theorem mapDomain_inl_inl (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) = γ k :=
  Finsupp.mapDomain_apply_of_injective Sum.inl_injective γ k

theorem mapDomain_inl_inr (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) = 0 :=
  Finsupp.mapDomain_notin_range γ _ (by simp)

theorem mapDomain_inr_inr (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) = γ k :=
  Finsupp.mapDomain_apply_of_injective Sum.inr_injective γ k

theorem mapDomain_inr_inl (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) = 0 :=
  Finsupp.mapDomain_notin_range γ _ (by simp)

theorem k2 (γ : Ix m n →₀ ℕ) : (∀ k ∈ γ.support, inF1 ε k) → ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (monomial γ 1 * g) = op (u * monomial (γ.mapDomain Sum.inl) 1) g + op r g := by
  induction γ using Finsupp.induction with
  | zero => intro _ d u _ _; exact ⟨0, good_zero d, fun g => by simp [monomial_zero', op_zero]⟩
  | single_add a b f haf hb ih =>
    intro hsup d u hu hue
    have hsf : ∀ k ∈ f.support, inF1 ε k := by
      intro k hk
      apply hsup k
      have hka : k ≠ a := fun h => haf (h ▸ hk)
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa [Finsupp.single_apply, Ne.symm hka] using hk
    have hai : inF1 ε a := by
      apply hsup a
      rw [Finsupp.mem_support_iff]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.1 haf, add_zero]
      exact hb
    obtain ⟨r₁, hr₁, e₁⟩ := kpow hai b d u hu hue
    have hu' := first_family_symbol_mul_variable_pow hu hai b
    obtain ⟨r₂, hr₂, e₂⟩ := ih hsf d (u * X (Sum.inl a) ^ b) hu'.1 (hu'.2 d hue)
    obtain ⟨r₃, hr₃, e₃⟩ := ih hsf d r₁ hr₁.1 (good_le hr₁)
    have hM : ∀ k, ((f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inl_inl, mapDomain_inl_inr] at hk
      exact hsf k (Finsupp.mem_support_iff.2 (by tauto))
    have g3 : Good ε d (r₁ * monomial (f.mapDomain Sum.inl) 1) := by
      have := good_mul_monomial (e := 0) hr₁ _ hM (by simp [mapDomain_inl_inr])
      simpa using this
    refine ⟨r₂ + r₁ * monomial (f.mapDomain Sum.inl) 1 + r₃, good_add (good_add hr₂ g3) hr₃, fun g => ?_⟩
    rw [monomial_single_add, mul_assoc, e₁, e₂, e₃, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      monomial_single_add, op_add, op_add]
    have : u * (X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1) =
        u * X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1 := by ring
    rw [this]
    ring

theorem op_dvE (w : Sym m n) (δ : Ix m n →₀ ℕ) (f : PX m n) :
    op w (dvE (fun k => δ k) f) = op (w * monomial (δ.mapDomain Sum.inr) 1) f := by
  classical
  conv_rhs => rw [w.as_sum, Finset.sum_mul, op_sum]
  conv_lhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [monomial_mul, mul_one, op_monomial, opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, mapDomain_inr_inl]
  have h2 : (fun k : Ix m n => (t + δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) =
      (fun k => t (Sum.inr k)) + fun k => δ k := by
    ext j; simp [mapDomain_inr_inr]
  rw [h1, add_zero, h2, ← dvE_mul]
  rfl

theorem decomp (t : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t.comapDomain Sum.inl Sum.inl_injective.injOn).mapDomain Sum.inl +
      (t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr = t := by
  ext j
  rcases j with j | j
  · simp [mapDomain_inl_inl, mapDomain_inr_inl, Finsupp.comapDomain_apply]
  · simp [mapDomain_inl_inr, mapDomain_inr_inr, Finsupp.comapDomain_apply]

theorem compSt : CompSt := by
  intro m n ε u v d₁ d₂ hu hv hue hve
  classical
  have key : ∀ t ∈ v.support, ∃ r, Good ε (d₁ + d₂) r ∧
      ∀ f, op u (opMono t f) = op (u * monomial t 1) f + op r f := by
    intro t ht
    have hγ : ∀ k ∈ (t.comapDomain Sum.inl Sum.inl_injective.injOn).support, inF1 ε k := by
      intro k hk
      apply hv t ht k
      left
      simpa [Finsupp.comapDomain_apply] using hk
    obtain ⟨r, hr, e⟩ := k2 _ hγ d₁ u hu hue
    have hs : ∀ k, (((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ)
        (Sum.inl k) ≠ 0 ∨ ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
          Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inr_inl, mapDomain_inr_inr] at hk
      apply hv t ht k
      right
      simpa [Finsupp.comapDomain_apply] using hk
    have he : (∑ k, ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
        Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ d₂ := by
      simp only [mapDomain_inr_inr, Finsupp.comapDomain_apply]
      exact hve t ht
    refine ⟨r * monomial ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr) 1,
      good_mul_monomial hr _ hs he, fun f => ?_⟩
    rw [opMono_eq, e]
    have hδ : (fun k : Ix m n => t (Sum.inr k)) =
        fun k => (t.comapDomain Sum.inr Sum.inr_injective.injOn) k := by
      ext k; simp [Finsupp.comapDomain_apply]
    rw [hδ, op_dvE, op_dvE, mul_assoc, monomial_mul, mul_one, decomp]
  choose! R hR using key
  refine ⟨∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • R t, ?_, ?_, fun f => ?_⟩
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).1
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).2
  · rw [show op v f = ∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • opMono t f from rfl, op_sum_f]
    have huv : u * v = ∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • (u * monomial t 1) := by
      conv_lhs => rw [v.as_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    rw [huv, op_sum, op_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(hR t ht).2, op_smul, op_smul, smul_add]

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

theorem PositivityTheory.Rg.Sw.LC.compSt : PositivityTheory.Rg.Sw.LC.CompSt := PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.compSt
