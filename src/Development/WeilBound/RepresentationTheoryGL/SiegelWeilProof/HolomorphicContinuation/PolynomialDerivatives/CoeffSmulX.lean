module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.BfSmulRight
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC.CoreC.G

variable {τ : Type} [Fintype τ] [DecidableEq τ]

def gf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, star (p.coeff s) * q.coeff s * w s

variable (w : (τ →₀ ℕ) → ℂ)

theorem gf_eq (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S) (hq : q.support ⊆ S) :
    gf w p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * w s := by
  unfold gf
  refine Finset.sum_subset (Finset.union_subset hp hq) fun s _ hs => ?_
  simp only [Finset.mem_union, not_or] at hs
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs.1 (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem gf_add_left (p p' q : MvPolynomial τ ℂ) : gf w (p + p') q = gf w p q + gf w p' q := by
  classical
  have h1 := support_add (p := p) (q := p')
  rw [gf_eq w (p.support ∪ p'.support ∪ q.support) (h1.trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_left).trans Finset.subset_union_left)
      Finset.subset_union_right,
    gf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_right).trans Finset.subset_union_left)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [MvPolynomial.coeff_add, star_add]; ring

theorem gf_add_right (p q q' : MvPolynomial τ ℂ) : gf w p (q + q') = gf w p q + gf w p q' := by
  classical
  have h1 := support_add (p := q) (q := q')
  rw [gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left (h1.trans Finset.subset_union_right),
    gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_left).trans Finset.subset_union_right),
    gf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_right).trans Finset.subset_union_right), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [MvPolynomial.coeff_add]; ring

theorem gf_smul_left (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w (r • p) q = star r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) ((MvPolynomial.support_smul).trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_smul, star_mul]; ring

theorem gf_smul_right (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w p (r • q) = r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) Finset.subset_union_left ((MvPolynomial.support_smul).trans Finset.subset_union_right),
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_smul]; ring

theorem gf_neg_left (p q : MvPolynomial τ ℂ) : gf w (-p) q = -gf w p q := by
  rw [show -p = (-1 : ℂ) • p by simp, gf_smul_left]; simp

theorem gf_neg_right (p q : MvPolynomial τ ℂ) : gf w p (-q) = -gf w p q := by
  rw [show -q = (-1 : ℂ) • q by simp, gf_smul_right]; simp

theorem gf_sub_left (p p' q : MvPolynomial τ ℂ) : gf w (p - p') q = gf w p q - gf w p' q := by
  rw [sub_eq_add_neg, gf_add_left, gf_neg_left, ← sub_eq_add_neg]

theorem gf_sub_right (p q q' : MvPolynomial τ ℂ) : gf w p (q - q') = gf w p q - gf w p q' := by
  rw [sub_eq_add_neg, gf_add_right, gf_neg_right, ← sub_eq_add_neg]

theorem gf_sum_left {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    gf w (∑ i ∈ I, f i) q = ∑ i ∈ I, gf w (f i) q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_left, ih, Finset.sum_insert ha]

theorem gf_sum_right {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    gf w p (∑ i ∈ I, f i) = ∑ i ∈ I, gf w p (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_right, ih, Finset.sum_insert ha]

theorem gf_monomial (s t : τ →₀ ℕ) (a b : ℂ) :
    gf w (monomial s a) (monomial t b) = if s = t then star a * b * w s else 0 := by
  classical
  rw [gf_eq w {s, t} ((support_monomial_subset).trans (by simp)) ((support_monomial_subset).trans (by simp))]
  by_cases h : s = t
  · subst h; simp [coeff_monomial]
  · rw [Finset.sum_pair h]; simp [coeff_monomial, h, Ne.symm h]

theorem gf_induction {P : MvPolynomial τ ℂ → MvPolynomial τ ℂ → Prop}
    (hm : ∀ s t (a b : ℂ), P (monomial s a) (monomial t b))
    (hl : ∀ p p' q, P p q → P p' q → P (p + p') q) (hr : ∀ p q q', P p q → P p q' → P p (q + q')) :
    ∀ p q, P p q := by
  intro p q
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    induction q using MvPolynomial.induction_on' with
    | monomial t b => exact hm s t a b
    | add q q' h1 h2 => exact hr _ _ _ h1 h2
  | add p p' h1 h2 => exact hl _ _ _ h1 h2

variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw

theorem gf_X_mul (k : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * p) q = κ * gf w p (pderiv k q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, gf_monomial, gf_monomial]
    by_cases h : Finsupp.single k 1 + s = t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _).symm, hw]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s = t - Finsupp.single k 1
      · rw [if_pos h']
        have : t k = 0 := by
          by_contra h0
          apply h
          rw [h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [mul_add, gf_add_left, gf_add_left, h1, h2, mul_add]
  · rw [gf_add_right, map_add (f := _), gf_add_right, h1, h2, mul_add]

theorem gf_pderiv (k : τ) (p q : MvPolynomial τ ℂ) : κ * gf w (pderiv k p) q = gf w p (X k * q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, gf_monomial, gf_monomial]
    by_cases h : s = Finsupp.single k 1 + t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _), hw, add_tsub_cancel_left]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, star_mul]
      push_cast
      simp only [Complex.star_def, Complex.conj_natCast, map_add (f := _), map_one]
      ring
    · rw [if_neg h]
      by_cases h' : s - Finsupp.single k 1 = t
      · rw [if_pos h']
        have : s k = 0 := by
          by_contra h0
          apply h
          rw [← h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [map_add (f := _), gf_add_left, gf_add_left, ← h1, ← h2, mul_add]
  · rw [gf_add_right, mul_add, mul_add, gf_add_right, h1, h2]

theorem gf_adj (k l : τ) (p q : MvPolynomial τ ℂ) : gf w (X k * pderiv l p) q = gf w p (X l * pderiv k q) := by
  rw [gf_X_mul κ hw, gf_pderiv κ hw]

omit hw

variable (w) in
theorem gf_herm (hs : ∀ s, star (w s) = w s) (p q : MvPolynomial τ ℂ) : gf w q p = star (gf w p q) := by
  unfold gf
  rw [Finset.union_comm, star_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [star_mul, star_mul, star_star, hs]; ring

variable (w) in
theorem gf_pos (hs : ∀ s, star (w s) = w s) (hp : ∀ s, 0 < (w s).re) (p : MvPolynomial τ ℂ) (h : p ≠ 0) :
    0 < (gf w p p).re := by
  unfold gf
  rw [Finset.union_self, Complex.re_sum]
  obtain ⟨s, hs0⟩ := (MvPolynomial.ne_zero_iff).mp h
  have hmem : s ∈ p.support := MvPolynomial.mem_support_iff.mpr hs0
  have key : ∀ t, (star (p.coeff t) * p.coeff t * w t).re = Complex.normSq (p.coeff t) * (w t).re := by
    intro t
    have hw' : (w t).im = 0 := by
      have := congrArg Complex.im (hs t); simp at this; linarith
    rw [show star (p.coeff t) * p.coeff t = (Complex.normSq (p.coeff t) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; rfl]
    simp [Complex.mul_re, hw']
  refine Finset.sum_pos' (fun t _ => ?_) ⟨s, hmem, ?_⟩
  · rw [key]; exact mul_nonneg (Complex.normSq_nonneg _) (hp t).le
  · rw [key]; exact mul_pos (Complex.normSq_pos.mpr hs0) (hp s)

omit [Fintype τ] in
theorem pderiv_X' (v u : τ) : pderiv v (X u : MvPolynomial τ ℂ) = if v = u then 1 else 0 := by
  rw [pderiv_X]; by_cases h : v = u
  · subst h; simp
  · simp [Pi.single_apply, Ne.symm h, h]

theorem der_expand (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, D (X v) * pderiv v p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p u hp =>
    rw [Derivation.leibniz, hp]
    simp only [smul_eq_mul, Derivation.leibniz, pderiv_X', mul_add, Finset.sum_add_distrib]
    have h1 : ∑ v, D (X v) * (p * (if v = u then (1 : MvPolynomial τ ℂ) else 0)) = p * D (X u) := by
      simp [mul_ite]; ring
    have h2 : ∑ v, D (X v) * (X u * pderiv v p) = X u * ∑ v, D (X v) * pderiv v p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1, h2]

theorem der_expand2 (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, ∑ u, (D (X v)).coeff (Finsupp.single u 1) • (X u * pderiv v p) := by
  rw [der_expand D p]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_lhs => rw [hlin v]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_mul_assoc]

theorem der_adj {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (D D' : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u)
    (hlin' : ∀ v, D' (X v) = ∑ u, (D' (X v)).coeff (Finsupp.single u 1) • X u)
    (htr : ∀ v u, (D' (X u)).coeff (Finsupp.single v 1) = star ((D (X v)).coeff (Finsupp.single u 1)))
    (p q : MvPolynomial τ ℂ) : gf w (D p) q = gf w p (D' q) := by
  rw [der_expand2 D hlin p, der_expand2 D' hlin' q]
  simp_rw [gf_sum_left, gf_sum_right, gf_smul_left, gf_smul_right, gf_adj κ hw, htr]
  rw [Finset.sum_comm]

def bf (w : (τ →₀ ℕ) → ℂ) (p q : MvPolynomial τ ℂ) : ℂ :=
  ∑ s ∈ p.support ∪ q.support, p.coeff s * q.coeff s * w s

theorem bf_eq (w : (τ →₀ ℕ) → ℂ) (S : Finset (τ →₀ ℕ)) {p q : MvPolynomial τ ℂ} (hp : p.support ⊆ S)
    (hq : q.support ⊆ S) : bf w p q = ∑ s ∈ S, p.coeff s * q.coeff s * w s := by
  unfold bf
  refine Finset.sum_subset (Finset.union_subset hp hq) fun s _ hs => ?_
  simp only [Finset.mem_union, not_or] at hs
  have h0 : p.coeff s = 0 := by
    by_contra h; exact hs.1 (MvPolynomial.mem_support_iff.mpr h)
  simp [h0]

theorem bf_add_left (w : (τ →₀ ℕ) → ℂ) (p p' q : MvPolynomial τ ℂ) : bf w (p + p') q = bf w p q + bf w p' q := by
  classical
  have h1 := support_add (p := p) (q := p')
  rw [bf_eq w (p.support ∪ p'.support ∪ q.support) (h1.trans Finset.subset_union_left) Finset.subset_union_right,
    bf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_left).trans Finset.subset_union_left)
      Finset.subset_union_right,
    bf_eq w (p.support ∪ p'.support ∪ q.support) ((Finset.subset_union_right).trans Finset.subset_union_left)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [MvPolynomial.coeff_add]; ring

theorem bf_add_right (w : (τ →₀ ℕ) → ℂ) (p q q' : MvPolynomial τ ℂ) : bf w p (q + q') = bf w p q + bf w p q' := by
  classical
  have h1 := support_add (p := q) (q := q')
  rw [bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left (h1.trans Finset.subset_union_right),
    bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_left).trans Finset.subset_union_right),
    bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_right).trans Finset.subset_union_right), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [MvPolynomial.coeff_add]; ring

theorem bf_monomial (w : (τ →₀ ℕ) → ℂ) (s t : τ →₀ ℕ) (a b : ℂ) :
    bf w (monomial s a) (monomial t b) = if s = t then a * b * w s else 0 := by
  classical
  rw [bf_eq w {s, t} ((support_monomial_subset).trans (by simp)) ((support_monomial_subset).trans (by simp))]
  by_cases h : s = t
  · subst h; simp [coeff_monomial]
  · rw [Finset.sum_pair h]; simp [coeff_monomial, h, Ne.symm h]

theorem bf_X_mul {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : bf w (X k * p) q = κ * bf w p (pderiv k q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, bf_monomial, bf_monomial]
    by_cases h : Finsupp.single k 1 + s = t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _).symm, hw]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s = t - Finsupp.single k 1
      · rw [if_pos h']
        have : t k = 0 := by
          by_contra h0
          apply h
          rw [h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [mul_add, bf_add_left, bf_add_left, h1, h2, mul_add]
  · rw [bf_add_right, map_add (f := _), bf_add_right, h1, h2, mul_add]

theorem bf_pderiv {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (k : τ) (p q : MvPolynomial τ ℂ) : κ * bf w (pderiv k p) q = bf w p (X k * q) := by
  revert p q
  refine gf_induction (fun s t a b => ?_) (fun p p' q h1 h2 => ?_) (fun p q q' h1 h2 => ?_)
  · rw [X, monomial_mul, one_mul, pderiv_monomial, bf_monomial, bf_monomial]
    by_cases h : s = Finsupp.single k 1 + t
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_left _ _), hw, add_tsub_cancel_left]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast; ring
    · rw [if_neg h]
      by_cases h' : s - Finsupp.single k 1 = t
      · rw [if_pos h']
        have : s k = 0 := by
          by_contra h0
          apply h
          rw [← h', add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0))]
        simp [this]
      · rw [if_neg h']; ring
  · rw [map_add (f := _), bf_add_left, bf_add_left, ← h1, ← h2, mul_add]
  · rw [bf_add_right, mul_add, mul_add, bf_add_right, h1, h2]

theorem bf_sum_left (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    bf w (∑ i ∈ I, f i) q = ∑ i ∈ I, bf w (f i) q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bf]
  | insert a I ha ih => rw [Finset.sum_insert ha, bf_add_left, ih, Finset.sum_insert ha]

theorem bf_sum_right (w : (τ →₀ ℕ) → ℂ) {ι : Type} (I : Finset ι) (p : MvPolynomial τ ℂ) (f : ι → MvPolynomial τ ℂ) :
    bf w p (∑ i ∈ I, f i) = ∑ i ∈ I, bf w p (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bf]
  | insert a I ha ih => rw [Finset.sum_insert ha, bf_add_right, ih, Finset.sum_insert ha]

end PositivityTheory.Rg.Sw.LC.CoreC.G
end
end

noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem fform_eq_gf (c : ℝ) (p q : PX m n) : fform c p q = gf (fun s => (wt c s : ℂ)) p q := rfl

theorem wt_univ (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) :
    wt c s = ∏ k, ((s k).factorial : ℝ) * (2 * c) ^ (s k) := by
  unfold wt
  refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
  have : s k = 0 := by simpa [Finsupp.mem_support_iff] using hk
  simp [this]

theorem wt_pos {c : ℝ} (hc : 0 < c) (s : Fin m × Fin n × Bool →₀ ℕ) : 0 < wt c s := by
  rw [wt_univ]
  exact Finset.prod_pos fun k _ => mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (by linarith) _)

theorem wt_step (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (wt c (Finsupp.single k 1 + s) : ℂ) = ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (wt c s : ℂ) := by
  have h : wt c (Finsupp.single k 1 + s) = (2 * c) * ((s k : ℝ) + 1) * wt c s := by
    rw [wt_univ, wt_univ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((s j).factorial : ℝ) * (2 * c) ^ (s j)) (Finset.mem_univ k)]
    have hrest : ∏ j ∈ Finset.univ.erase k, (((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j).factorial : ℝ) *
          (2 * c) ^ ((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j) =
        ∏ j ∈ Finset.univ.erase k, ((s j).factorial : ℝ) * (2 * c) ^ (s j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [Finsupp.single_apply, Ne.symm hjk]
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [add_comm 1 (s k), Nat.factorial_succ, pow_succ]
    push_cast; ring
  rw [h]; push_cast; ring

theorem KopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) p := by
  simp [KopL, LinearMap.sub_apply, LinearMap.sum_apply]

theorem rdeg_add (ε : Fin m → Bool) (s t : Fin m × Fin n × Bool →₀ ℕ) : rdeg ε (s + t) = rdeg ε s + rdeg ε t := by
  funext a; simp [rdeg, Finset.sum_add_distrib]

theorem rdeg_single (ε : Fin m → Bool) (k : Fin m × Fin n × Bool) (hk : inF1 ε k) :
    rdeg ε (Finsupp.single k 1) = fun a => if a = k.1 then 1 else 0 := by
  funext a
  unfold rdeg
  obtain ⟨a0, i0, b0⟩ := k
  simp only [inF1] at hk
  subst hk
  by_cases ha : a = a0
  · subst ha
    rw [if_pos rfl, Finset.sum_eq_single i0]
    · simp
    · intro i _ hi; simp [Finsupp.single_apply, Ne.symm hi]
    · simp
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ha (congrArg Prod.fst h).symm

theorem term_mem_box (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) (k l : Fin m × Fin n × Bool)
    (hk : inF1 ε k) (hl : inF1 ε l) (hkl : k.1 = l.1) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) :
    X k * pderiv l (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [pderiv_monomial, X, monomial_mul, one_mul, one_mul]
  by_cases h0 : s l = 0
  · simp [h0]
  · rw [show (monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) ((s l : ℕ) : ℂ) : PX m n) =
        ((s l : ℕ) : ℂ) • monomial (Finsupp.single k 1 + (s - Finsupp.single l 1)) (1 : ℂ) by
        rw [smul_monomial, smul_eq_mul, mul_one]]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun k' hk' => ?_, ?_, rfl⟩)
    · rcases Finset.mem_union.mp (Finsupp.support_add hk') with h | h
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h; rw [h]; exact hk
      · exact hs k' (Finsupp.support_tsub h)
    · have hle : Finsupp.single l 1 ≤ s := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h0)
      have e1 : rdeg ε (Finsupp.single k 1) = rdeg ε (Finsupp.single l 1) := by
        rw [rdeg_single ε k hk, rdeg_single ε l hl, hkl]
      rw [rdeg_add, e1, ← rdeg_add, add_tsub_cancel_of_le hle]
      exact hR

theorem gen_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) : KopL ε i j (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [KopL_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun a ha => ?_) (Submodule.sum_mem _ fun a ha => ?_)
  · have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, i, false) (a, j, false) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR
  · have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, j, true) (a, i, true) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR

theorem box_stable (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) :
    ∀ f ∈ box (n := n) ε R, KopL ε i j f ∈ box ε R := by
  intro f hf
  refine Submodule.span_induction (p := fun x _ => KopL ε i j x ∈ box ε R) ?_ ?_ ?_ ?_ hf
  · rintro x ⟨s, hs, hR, rfl⟩
    exact gen_stable ε i j R s hs hR
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro r x _ hx; rw [map_smul]; exact Submodule.smul_mem _ r hx

def symW (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) : ℂ := ∏ k ∈ u.support, ((u k).factorial : ℂ)

theorem symW_step (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (k) :
    symW (Finsupp.single k 1 + u) = 1 * ((u k : ℂ) + 1) * symW u := by
  have hu : ∀ v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ,
      symW v = ∏ k, ((v k).factorial : ℂ) := fun v => by
    unfold symW
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have : v k = 0 := by simpa [Finsupp.mem_support_iff] using hk
    simp [this]
  rw [hu, hu, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => ((u j).factorial : ℂ)) (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k,
      (((Finsupp.single k 1 + u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) j).factorial : ℂ) =
      ∏ j ∈ Finset.univ.erase k, ((u j).factorial : ℂ) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Finsupp.single_apply, Ne.symm hjk]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1 (u k), Nat.factorial_succ]
  push_cast; ring

theorem coeff_smul_X {τ : Type} [DecidableEq τ] (c : ℂ) (w0 u : τ) :
    (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) = if w0 = u then c else 0 := by
  rw [coeff_smul, coeff_X']
  by_cases h : w0 = u
  · subst h; simp
  · rw [if_neg (fun e => h ((Finsupp.single_left_inj one_ne_zero).mp e)), if_neg h]; simp

theorem expand_lin {τ : Type} [Fintype τ] [DecidableEq τ] (c : ℂ) (w0 : τ) :
    (c • X w0 : MvPolynomial τ ℂ) = ∑ u, (c • X w0 : MvPolynomial τ ℂ).coeff (Finsupp.single u 1) • X u := by
  simp_rw [coeff_smul_X, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]; simp

theorem symK_lin (ε : Fin m → Bool) (i j : Fin n) (v) :
    ∃ (c : ℂ) (w0 : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)), symK ε i j (X v : Sym m n) = c • X w0 := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;>
    first
    | exact ⟨1, _, (one_smul _ _).symm⟩
    | exact ⟨-1, _, by rw [neg_smul, one_smul]⟩
    | exact ⟨0, Sum.inl (a, i', b), (zero_smul _ _).symm⟩

theorem symK_hlin (ε : Fin m → Bool) (i j : Fin n) (v) :
    symK ε i j (X v : Sym m n) = ∑ u, (symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1) • X u := by
  obtain ⟨c, w0, h⟩ := symK_lin ε i j v
  rw [h]; exact expand_lin c w0

theorem symK_tr (ε : Fin m → Bool) (i j : Fin n) (v u) :
    (symK ε j i (X u : Sym m n)).coeff (Finsupp.single v 1) = star ((symK ε i j (X v : Sym m n)).coeff (Finsupp.single u 1)) := by
  rcases v with ⟨a, i', b⟩ | ⟨a, i', b⟩ <;> rcases u with ⟨a', i'', b'⟩ | ⟨a', i'', b'⟩ <;>
    simp only [symK, mkDerivation_X, Sum.elim_inl, Sum.elim_inr] <;>
    split_ifs <;> simp_all [coeff_X', Finsupp.single_left_inj, coeff_neg] <;> aesop

end CoreC

open CoreC CoreC.G in
theorem formFacts : FormFacts := by
  intro m n ε c hc
  have hw : ∀ (s : Fin m × Fin n × Bool →₀ ℕ) k, (fun s => (wt c s : ℂ)) (Finsupp.single k 1 + s) =
      ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (fun s => (wt c s : ℂ)) s := fun s k => wt_step c s k
  have hst : ∀ s : Fin m × Fin n × Bool →₀ ℕ, star ((fun s => (wt c s : ℂ)) s) = (fun s => (wt c s : ℂ)) s :=
    fun s => Complex.conj_ofReal _
  have hpos : ∀ s : Fin m × Fin n × Bool →₀ ℕ, 0 < ((fun s => (wt c s : ℂ)) s).re := fun s => by
    simpa using wt_pos hc s
  refine ⟨fun p q => gf_herm _ hst p q, fun p hp => gf_pos _ hst hpos p hp, fun i j p q => ?_,
    fun i j R f hf => box_stable ε i j R f hf, fun i j s t => ⟨by simp [fform], ?_⟩⟩
  · rw [fform_eq_gf, fform_eq_gf, KopL_apply, KopL_apply, gf_sub_left, gf_sub_right, gf_sum_left, gf_sum_left,
      gf_sum_right, gf_sum_right]
    congr 1 <;> exact Finset.sum_congr rfl fun a _ => gf_adj _ hw _ _ _ _
  · exact der_adj (w := symW) 1 symW_step (symK ε i j) (symK ε j i) (symK_hlin ε i j) (symK_hlin ε j i)
      (symK_tr ε i j) s t

end PositivityTheory.Rg.Sw.LC
