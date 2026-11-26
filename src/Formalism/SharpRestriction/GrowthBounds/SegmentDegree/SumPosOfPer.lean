module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopDegreeComparison

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumTotalLoss
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumMemLaSet
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FamilyDegreesAdmissible
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FactorialMulChooseEqProdRange
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset

theorem sum_card_tuples (k n : ℕ) (hk : 0 < k) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card = (n + k - 1).choose (k - 1) := by
  have h1 : (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card =
      ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).card := by
    refine Finset.card_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f) (fun f _ => ⇑f) ?_ ?_ ?_ ?_ <;>
      simp [Finset.mem_finsuppAntidiag]
  rw [h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
  have h2 : k + n - 1 = n + (k - 1) := by omega
  have h3 : n + k - 1 = n + (k - 1) := by omega
  rw [h2, h3]
  exact Nat.choose_symm_add

theorem sum_digit_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    (n + k - 1).choose (k - 1) ≤ ∑ v ∈ S, ((n - ∑ c, v c) / P + k - 1).choose (k - 1) := by
  classical
  rw [← sum_card_tuples k n hk]
  have hdec : ∀ w : Fin k → ℕ, ∑ c, w c = P * ∑ c, w c / P + ∑ c, w c % P := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (Nat.div_add_mod (w c) P).symm
  have hmaps : ∀ w ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n, (fun c => w c % P) ∈ S := by
    intro w hw
    have hw' : ∑ c, w c = n := by simpa using hw
    have hd := hdec w
    refine hS _ (fun c => Nat.mod_lt _ hP) ?_ ?_
    · rw [← hw', hd]; exact Nat.le_add_left _ _
    · rw [← hw', hd, Nat.mul_add_mod]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← sum_card_tuples k _ hk]
  refine Finset.card_le_card_of_injOn (fun w c => w c / P) ?_ ?_
  · intro w hw
    have hw1 := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hw' : ∑ c, w c = n := by simpa using hw1.1
    have hv : (fun c => w c % P) = v := hw1.2
    have hd := hdec w
    have hv' : ∑ c, w c % P = ∑ c, v c := by rw [← hv]
    simp only [Finset.mem_coe, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]
    rw [← hw', hd, hv', Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP]
  · intro w hw w' hw' hww
    have hw1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    have hw2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
    funext c
    have e1 := congrFun hww c
    have e2 := congrFun (hw1.trans hw2.symm) c
    simp only at e1 e2
    rw [← Nat.div_add_mod (w c) P, ← Nat.div_add_mod (w' c) P, e1, e2]

theorem sum_label_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (hn : k * P ≤ n) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    P ^ (k - 1) ≤ S.card := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hc : (Finset.univ : Finset (Fin m → Fin P)).card = P ^ (m + 1 - 1) := by
    simp
  rw [← hc]
  let g : (Fin m → Fin P) → (Fin (m + 1) → ℕ) := fun u =>
    Fin.cons ((n + (P - 1) * ∑ i, (u i : ℕ)) % P) (fun i => (u i : ℕ))
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro u _
    have hlt : ∀ c, g u c < P := by
      intro c
      refine Fin.cases ?_ (fun i => ?_) c
      · simp only [g, Fin.cons_zero]; exact Nat.mod_lt _ hP
      · simp only [g, Fin.cons_succ]; exact (u i).isLt
    refine Finset.mem_coe.mpr (hS _ hlt ?_ ?_)
    · calc ∑ c, g u c ≤ ∑ _c : Fin (m + 1), P := Finset.sum_le_sum fun c _ => (hlt c).le
        _ = (m + 1) * P := by simp
        _ ≤ n := hn
    · rw [Fin.sum_univ_succ]
      simp only [g, Fin.cons_zero, Fin.cons_succ]
      set s := ∑ i, (u i : ℕ)
      rw [Nat.mod_add_mod]
      have : n + (P - 1) * s + s = n + P * s := by
        obtain ⟨P', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hP.ne'
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        ring
      rw [this, Nat.add_mul_mod_self_left]
  · intro u _ u' _ huu
    funext i
    have := congrFun huu i.succ
    simp only [g, Fin.cons_succ] at this
    exact Fin.ext this

theorem factorial_mul_choose_eq_prod_range (x M : ℕ) :
    ((M.factorial : ℕ) : ℝ) * (((x + M).choose M : ℕ) : ℝ) = ∏ l ∈ Finset.range M, ((x : ℝ) + 1 + l) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose x M
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h' : ((∏ i ∈ Finset.range M, (x + 1 + i) : ℕ) : ℝ) = ((M.factorial * (x + M).choose M : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  rw [← h']

theorem choose_add_mul_one_sub_le_pow_mul_choose_add (x y M : ℕ) (s θ : ℝ) (h1 : θ ≤ 1)
    (h : ∀ l < M, ((y : ℝ) + 1 + l) * (1 - θ) ≤ s * ((x : ℝ) + 1 + l)) :
    (((y + M).choose M : ℕ) : ℝ) * (1 - M * θ) ≤ s ^ M * (((x + M).choose M : ℕ) : ℝ) := by
  have hf : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast M.factorial_pos
  have hb : 1 - (M : ℝ) * θ ≤ (1 - θ) ^ M := by
    have := one_add_mul_le_pow (a := -θ) (by linarith) M
    calc 1 - (M : ℝ) * θ = 1 + (M : ℝ) * (-θ) := by ring
      _ ≤ (1 + -θ) ^ M := this
      _ = (1 - θ) ^ M := by ring_nf
  have hy : (0 : ℝ) ≤ (((y + M).choose M : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hb hy) ?_
  refine le_of_mul_le_mul_left ?_ hf
  have e1 : (M.factorial : ℝ) * ((((y + M).choose M : ℕ) : ℝ) * (1 - θ) ^ M) =
      ∏ l ∈ Finset.range M, (((y : ℝ) + 1 + l) * (1 - θ)) := by
    rw [← mul_assoc, factorial_mul_choose_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have e2 : (M.factorial : ℝ) * (s ^ M * (((x + M).choose M : ℕ) : ℝ)) =
      ∏ l ∈ Finset.range M, (s * ((x : ℝ) + 1 + l)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← factorial_mul_choose_eq_prod_range]
    ring
  rw [e1, e2]
  refine Finset.prod_le_prod₀ (fun l _ => ?_) fun l hl => h l (Finset.mem_range.mp hl)
  have : (0 : ℝ) ≤ (y : ℝ) + 1 + l := by positivity
  exact mul_nonneg this (by linarith)

theorem prod_range_shift_of_periodic (φ : ℤ → ℝ) (J : ℕ) (hJ : 1 ≤ J) (hφ : ∀ j, φ (j + J) = φ j) :
    ∏ j ∈ Finset.range J, φ ((j : ℤ) + 1) = ∏ j ∈ Finset.range J, φ (j : ℤ) := by
  obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun j : ℕ => φ (j : ℤ))]
  have h := hφ 0
  push_cast at h ⊢
  rw [zero_add] at h
  rw [h]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumBin (r K n : ℕ) : ℝ := ((Nat.choose (n + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

theorem sum_one_le_bin (r K n : ℕ) : 1 ≤ sumBin r K n := by
  unfold sumBin
  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos (by omega))

theorem sum_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

theorem sum_single_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) {a : ι} (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  have h2 : (1 : ℝ) ≤ ∏ i ∈ s.erase a, f i := sum_one_le_prod _ _ fun i hi => h1 i (Finset.mem_of_mem_erase hi)
  have h3 : 0 ≤ f a := le_trans zero_le_one (h1 a ha)
  nlinarith

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def sumTset (la : Fin n' → Fin (r + K) → ℕ) (j : ℤ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = X.nz p K la j (X.F.fr j i.val) % X.Qc p K j

def sumhT (t : Fin n') (v : Fin (r + K) → ℕ) : ℝ :=
  ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ),
    if posOf n' x = t then sumBin r K ((X.a' p K t - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1

def sumSt (t : Fin n') : ℝ := ∑ v ∈ X.laSet p K t, X.sumhT p K t v


omit [NeZero n'] in
def firstSumFactor : ℝ := 1 - 1 / X.a ^ (X.Ns ^ 2)

def sumWf (j : ℤ) : ℝ := ∏ i : Fin r, sumBin r K ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat)

def sumTf (j : ℤ) : ℝ := (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

theorem sum_segBound_eq (j : ℤ) (b : ℤ → ℕ) :
    X.segBound p K j b = (X.firstSumFactor * X.sumWf p K j * X.sumTf p K j) * ∏ x ∈ X.F.LLset j, sumBin r K (b x) := by
  unfold segBound firstSumFactor sumWf sumTf sumBin
  ring

end Dat

structure SumFacts {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  tiling : ∀ φ : Fin n' → ℝ,
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x)
  split : ∀ (j : ℤ) (ψ : ℤ → ℝ),
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val)
  LLsub : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j ∧ x < X.F.fr j 0
  frlate : ∀ j (i : Fin r), X.F.fr j i.val ∈ X.toLate j
  uniqP : ∀ j j' x x', x ∈ X.toLate j → x' ∈ X.toLate j' → posOf n' x = posOf n' x' →
    X.Pz p K j x = X.Pz p K j' x'
  kP : ∀ j x, x ∈ X.toLate j → (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x)
  compA : ∀ t ∈ X.F.TT, sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t)
  compW : ∀ j (i : Fin r), sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  prodQ : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n'
  perW : ∀ j (i : Fin r),
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val)
  JN : X.F.J ≤ X.F.TT.card
  a32 : 32 * X.Y ≤ X.a

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

omit [NeZero n'] in
theorem sum_eZ_val (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) : X.eZ e (j.val : ℤ) = e j := by
  have hJ : 0 < X.F.J := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  unfold Dat.eZ
  rw [dite_eq_left hJ]
  congr 1
  apply Fin.ext
  have h1 : ((j.val : ℤ) % (X.F.J : ℤ)) = j.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [h1, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt j.isLt

theorem sum_late_mem {j x : ℤ} (hx : x ∈ X.toLate j) :
    x ∈ X.F.letters j ∧ ¬ X.F.IsW j x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have hx' := Finset.mem_filter.mp hx
  have h2 := Finset.mem_filter.mp hx'.1
  exact ⟨hx'.1, hx'.2, (Finset.mem_Icc.mp h2.1).2, h2.2⟩

theorem sum_bfam_late (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (x : ℤ)
    (hx : x ∈ X.toLate (j.val : ℤ)) :
    X.bfam p K la e (j.val : ℤ) x = X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j) x := by
  obtain ⟨h1, h2, h3, -⟩ := sum_late_mem hx
  unfold Dat.bfam Dat.setTau
  rw [if_pos h1, if_neg h2, sum_eZ_val]
  by_cases h : X.F.fr (j.val : ℤ) 0 ≤ x
  · rw [if_pos h, if_pos ⟨h, h3⟩]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

theorem family_degrees_admissible (hr : 0 < r) (hp : 0 < p) (hLL : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j)
    (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j : ℤ) :
    X.AdmLL p K j (X.nz p K la j) := by
  classical
  intro x hx
  have hv : la (posOf n' x) ∈ X.laSet p K (posOf n' x) := (Fintype.mem_piFinset.mp hla) _
  obtain ⟨-, hle, hall⟩ := Finset.mem_filter.mp hv
  obtain ⟨hlt, hmod⟩ := hall j x (hLL j x hx) rfl
  set P := X.Pz p K j x with hPdef
  set n := X.a' p K (posOf n' x) with hn
  set s := ∑ c, la (posOf n' x) c with hs
  have hP : 0 < P := by rw [hPdef]; unfold Dat.Pz; exact pow_pos hp _
  have hdvd : P ∣ n - s := (Nat.modEq_iff_dvd' hle).mp hmod
  have hnz : X.nz p K la j x = (n - s) / P := rfl
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcast : ((X.nz p K la j x : ℕ) : ℝ) = ((n : ℝ) - s) / P := by
    rw [hnz, Nat.cast_div hdvd hPr.ne', Nat.cast_sub hle]
  have hslt : s < (r + K) * P := by
    calc s < ∑ _c : Fin (r + K), P := by
            rw [hs]
            exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ => hlt c
      _ = (r + K) * P := by simp
  have hslt' : (s : ℝ) < Dat.k (r := r) K * P := by
    unfold Dat.k
    exact_mod_cast hslt
  rw [hcast]
  constructor
  · rw [sub_div, sub_lt_sub_iff_left, div_lt_iff₀ hPr]
    exact hslt'
  · exact div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg _; linarith) hPr.le

theorem first_sum_factor_bounds (hY : 1 ≤ X.Y) (ha : 32 * X.Y ≤ X.a) (hNs : 1 ≤ X.Ns) :
    1 - 1 / (32 * X.Y) ≤ X.firstSumFactor ∧ 0 ≤ X.firstSumFactor := by
  have ha1 : 1 ≤ X.a := by linarith
  have h1 : X.a ≤ X.a ^ (X.Ns ^ 2) := by
    calc X.a = X.a ^ 1 := (pow_one _).symm
      _ ≤ X.a ^ (X.Ns ^ 2) := pow_le_pow_right₀ ha1 (Nat.one_le_pow _ _ hNs)
  have h2 : 1 / X.a ^ (X.Ns ^ 2) ≤ 1 / (32 * X.Y) :=
    one_div_le_one_div_of_le (by linarith) (ha.trans h1)
  have h3 : 1 / (32 * X.Y) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  unfold Dat.firstSumFactor
  constructor <;> linarith

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

theorem sum_one_le_hT (t : Fin n') (v : Fin (r + K) → ℕ) : 1 ≤ X.sumhT p K t v := by
  unfold Dat.sumhT
  refine sum_one_le_prod _ _ fun j _ => sum_one_le_prod _ _ fun x _ => ?_
  split_ifs
  · exact sum_one_le_bin _ _ _
  · exact le_rfl

theorem sum_mem_laSet (F : SumFacts X p K) {j0 x0 : ℤ} (hx0 : x0 ∈ X.toLate j0) (v : Fin (r + K) → ℕ)
    (h1 : ∀ c, v c < X.Pz p K j0 x0) (h2 : ∑ c, v c ≤ X.a' p K (posOf n' x0))
    (h3 : (∑ c, v c) % X.Pz p K j0 x0 = X.a' p K (posOf n' x0) % X.Pz p K j0 x0) :
    v ∈ X.laSet p K (posOf n' x0) := by
  classical
  unfold Dat.laSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun c => ?_, h2, fun j x hx hpos => ?_⟩
  · rw [Finset.mem_range]
    have : v c ≤ ∑ c, v c := Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · rw [F.uniqP j j0 x x0 hx hx0 hpos]
    exact ⟨h1, h3⟩

theorem sum_St_nontop (t : Fin n') (ht : t ∉ X.F.TT) : 1 ≤ X.sumSt p K t := by
  classical
  have h0 : (0 : Fin (r + K) → ℕ) ∈ X.laSet p K t := by
    unfold Dat.laSet
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun c => by simp, by simp, fun j x hx hpos => ?_⟩
    exact absurd (hpos ▸ (sum_late_mem hx).2.2.2) ht
  unfold Dat.sumSt
  exact (sum_one_le_hT t 0).trans
    (Finset.single_le_sum (f := fun v => X.sumhT p K t v) (fun v _ => zero_le_one.trans (sum_one_le_hT t v)) h0)

theorem sum_St_nonneg (t : Fin n') : 0 ≤ X.sumSt p K t :=
  Finset.sum_nonneg fun v _ => zero_le_one.trans (sum_one_le_hT t v)

theorem Pz_pos (hp : 0 < p) (j x : ℤ) : 0 < X.Pz p K j x := by unfold Dat.Pz; exact pow_pos hp _

theorem sum_St_LL (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : Fin X.F.J) {x0 : ℤ}
    (hx0 : x0 ∈ X.F.LLset (j0.val : ℤ)) :
    sumBin r K (X.a' p K (posOf n' x0)) ≤ X.sumSt p K (posOf n' x0) := by
  classical
  have hl := (F.LLsub _ _ hx0).1
  have hd := sum_digit_count (r + K) (X.a' p K (posOf n' x0)) (X.Pz p K (j0.val : ℤ) x0) (by omega) (Pz_pos hp _ _)
    (X.laSet p K (posOf n' x0)) (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : sumBin r K (X.a' p K (posOf n' x0)) ≤ ∑ v ∈ X.laSet p K (posOf n' x0),
      sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x0) := by
    unfold sumBin
    exact_mod_cast hd
  refine hd'.trans (Finset.sum_le_sum fun v _ => ?_)
  unfold Dat.sumhT
  have hin : ∀ j : Fin X.F.J, ∀ x ∈ X.F.LLset (j.val : ℤ), (1 : ℝ) ≤
      (if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1) := by
    intro j x _
    split_ifs
    · exact sum_one_le_bin _ _ _
    · exact le_rfl
  have s1 := sum_single_le_prod (X.F.LLset (j0.val : ℤ)) (fun x => if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x) else 1) (hin j0) hx0
  have s2 := sum_single_le_prod (Finset.univ : Finset (Fin X.F.J)) (fun j => ∏ x ∈ X.F.LLset (j.val : ℤ),
      if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1)
      (fun j _ => sum_one_le_prod _ _ (hin j)) (Finset.mem_univ j0)
  simp only [if_true] at s1
  exact s1.trans s2

theorem sum_St_fr (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : ℤ) (i : Fin r) :
    ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤ X.sumSt p K (posOf n' (X.F.fr j0 i.val)) := by
  classical
  have hl := F.frlate j0 i
  have hd := sum_label_count (r + K) (X.a' p K (posOf n' (X.F.fr j0 i.val))) (X.Pz p K j0 (X.F.fr j0 i.val)) (by omega)
    (Pz_pos hp _ _) (F.kP _ _ hl) (X.laSet p K (posOf n' (X.F.fr j0 i.val)))
    (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤
      ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ) := by exact_mod_cast hd
  refine hd'.trans ?_
  unfold Dat.sumSt
  calc ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ)
      = ∑ _v ∈ X.laSet p K (posOf n' (X.F.fr j0 i.val)), (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => sum_one_le_hT _ v

theorem sum_LA :
    ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ), sumBin r K (X.nz p K la (j.val : ℤ) x) =
      ∏ t : Fin n', X.sumSt p K t := by
  classical
  unfold Dat.sumSt
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun la _ => ?_
  unfold Dat.sumhT
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_ite_eq]
  simp [Dat.nz]

theorem sub_le_mul_one_sub_and_mem_unit_interval {P c s : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : s ≤ P) :
    s - c ≤ P * (1 - c) ∧ 0 ≤ P * (1 - c) ∧ P * (1 - c) ≤ 1 := by
  refine ⟨by nlinarith, mul_nonneg hP0 (by linarith), by nlinarith⟩

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumEta (r : ℕ) (Y : ℝ) : ℝ := (1 - 5 / Y) * (1 - 1 / Y) * (1 - (r : ℝ) / (2 * Y))

theorem sum_total_loss (r J N : ℕ) (k Y A : ℝ) (hr : 2 ≤ r) (hk : 5 ≤ k) (hY : 1 ≤ Y) (hJN : J ≤ N) (hN : 1 ≤ N)
    (hA : 1 - 1 / (32 * Y) ≤ A) (hA1 : A ≤ 1) (hlt : 0 < 1 - 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y) :
    0 ≤ 1 - 5 / Y ∧ 0 ≤ 1 - 1 / Y ∧ 0 ≤ 1 - (r : ℝ) / (2 * Y) ∧ 1 - 5 / Y ≤ 1 ∧ 1 - 1 / Y ≤ 1 ∧
      1 - (r : ℝ) / (2 * Y) ≤ 1 ∧
      1 - 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y ≤ A ^ J * sumEta r Y ^ N := by
  have hY0 : 0 < Y := by linarith
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u := 1 / Y with hu
  have hu0 : 0 < u := by positivity
  have e1 : 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y = N * ((r : ℝ) ^ 2 * k * u) := by rw [hu]; ring
  have e5 : 5 / Y = 5 * u := by rw [hu]; ring
  have er : (r : ℝ) / (2 * Y) = (r : ℝ) / 2 * u := by rw [hu]; field_simp
  have e32 : 1 / (32 * Y) = u / 32 := by rw [hu]; field_simp
  rw [e1] at hlt ⊢
  rw [e32] at hA
  unfold sumEta
  rw [e5, er]
  have hrk : 0 ≤ (r : ℝ) ^ 2 * k * u := by positivity
  have h1 : (r : ℝ) ^ 2 * k * u < 1 := by nlinarith
  have hr2k : 10 * (r : ℝ) ≤ (r : ℝ) ^ 2 * k := by nlinarith
  have h5 : 5 * u ≤ 1 := by nlinarith
  have h1u : u ≤ 1 := by nlinarith
  have hru : (r : ℝ) / 2 * u ≤ 1 := by nlinarith
  have hru0 : 0 ≤ (r : ℝ) / 2 * u := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  have hA0 : 0 ≤ A := by nlinarith
  obtain ⟨s1, p1, q1⟩ := sub_le_mul_one_sub_and_mem_unit_interval (P := 1 - 5 * u) (c := u) (s := 1 - 5 * u) (by linarith) (by linarith) hu0.le h1u le_rfl
  obtain ⟨s2, p2, q2⟩ := sub_le_mul_one_sub_and_mem_unit_interval (c := (r : ℝ) / 2 * u) p1 q1 hru0 hru s1
  set η := (1 - 5 * u) * (1 - u) * (1 - (r : ℝ) / 2 * u) with hη
  have hAη : 1 - (7 + (r : ℝ) / 2) * u ≤ A * η := by
    have : (1 - u / 32) * η ≤ A * η := mul_le_mul_of_nonneg_right hA p2
    nlinarith
  have hε : (7 + (r : ℝ) / 2) * u ≤ (r : ℝ) ^ 2 * k * u := by
    apply mul_le_mul_of_nonneg_right _ hu0.le
    nlinarith
  have hbase0 : 0 ≤ 1 - (7 + (r : ℝ) / 2) * u := by linarith
  have hpow : A ^ N ≤ A ^ J := pow_le_pow_of_le_one hA0 hA1 hJN
  have hηN : 0 ≤ η ^ N := pow_nonneg p2 N
  calc 1 - (N : ℝ) * ((r : ℝ) ^ 2 * k * u) ≤ 1 + (N : ℝ) * (-((7 + (r : ℝ) / 2) * u)) := by nlinarith
    _ ≤ (1 + -((7 + (r : ℝ) / 2) * u)) ^ N := one_add_mul_le_pow (by linarith) N
    _ ≤ (A * η) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    _ = A ^ N * η ^ N := mul_pow _ _ _
    _ ≤ A ^ J * η ^ N := mul_le_mul_of_nonneg_right hpow hηN

section Main

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

theorem sum_fac_LL (F : SumFacts X p K) (h5 : 0 ≤ 1 - 5 / X.Y) (h1 : 0 ≤ 1 - 1 / X.Y) (h1' : 1 - 1 / X.Y ≤ 1)
    (hr0 : 0 ≤ 1 - (r : ℝ) / (2 * X.Y)) (hr1 : 1 - (r : ℝ) / (2 * X.Y) ≤ 1) (t : Fin n') (ht : t ∈ X.F.TT) :
    sumEta r X.Y * sumBin r K (X.deg t) ≤ sumBin r K (X.a' p K t) := by
  refine le_trans ?_ (F.compA t ht)
  have hb : 0 ≤ sumBin r K (X.deg t) := zero_le_one.trans (sum_one_le_bin _ _ _)
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hb
  unfold sumEta
  have : (1 - 5 / X.Y) * (1 - 1 / X.Y) ≤ 1 - 5 / X.Y := by nlinarith
  nlinarith [mul_nonneg h5 h1]

theorem sum_fac_fr (F : SumFacts X p K) (hr : 0 < r) (h5 : 0 ≤ 1 - 5 / X.Y) (h1 : 0 ≤ 1 - 1 / X.Y)
    (hr0 : 0 ≤ 1 - (r : ℝ) / (2 * X.Y)) (j : ℤ) (i : Fin r) :
    sumEta r X.Y * sumBin r K (X.deg (posOf n' (X.F.fr j i.val))) ≤
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat) *
        (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) *
        ((X.Pz p K j (X.F.fr j i.val) : ℕ) : ℝ) ^ (r + K - 1) * ((X.Qc p K j : ℕ) : ℝ) ^ K := by
  have ht := (sum_late_mem (F.frlate j i)).2.2.2
  have hA := F.compA _ ht
  have hW := F.compW j i
  set t := posOf n' (X.F.fr j i.val)
  set B := sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  set Qr := ((X.Qc p K j : ℕ) : ℝ)
  set Pr := ((X.Pz p K j (X.F.fr j i.val) : ℕ) : ℝ)
  have hmax : max 0 (1 - (r : ℝ) / (2 * X.Y)) = 1 - (r : ℝ) / (2 * X.Y) := max_eq_right hr0
  have hexp : r + K - 1 = (r - 1) + K := by omega
  have e : B * (Qr ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) * Pr ^ (r + K - 1) * Qr ^ K =
      (1 - (r : ℝ) / (2 * X.Y)) * ((Pr * Qr) ^ (r + K - 1) * B) := by
    rw [hmax, mul_pow, hexp, pow_add Qr]
    ring
  rw [e]
  have hW' : sumBin r K (X.a' p K t) * (1 - 1 / X.Y) ≤ (Pr * Qr) ^ (r + K - 1) * B := by
    have : (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) = Pr * Qr := by push_cast; rfl
    rw [← this]; exact hW
  have h2 : sumBin r K (X.deg t) * (1 - 5 / X.Y) * (1 - 1 / X.Y) ≤ (Pr * Qr) ^ (r + K - 1) * B :=
    (mul_le_mul_of_nonneg_right hA h1).trans hW'
  have h3 := mul_le_mul_of_nonneg_left h2 hr0
  refine le_trans (le_of_eq ?_) h3
  unfold sumEta
  ring

theorem restSum_of (hF : ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → (1088 : ℝ) ≤ X.CLa → (1088 : ℝ) ≤ X.Ck → SumFacts X p K ∧ 1 ≤ X.Ns) : RestSum 1088 1 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk G hG0 hGdep hGsum
  obtain ⟨F, hNs⟩ := hF p n' r K X hX hLa hk
  have hp : 0 < p := hX.prime.pos
  have hr : 0 < r := by have := hX.r2; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hRHS0 : 0 ≤ ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J,
      G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) :=
    Finset.sum_nonneg fun la _ => Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun j _ => hG0 _ _
  have hq0 : (0 : ℝ) < ((p : ℝ) ^ n') ^ (r * K) := by positivity
  rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hq0]
  have hbd : X.bound K 1 = (1 - 1 * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * Dat.k (r := r) K / X.Y) *
      ∏ t ∈ X.F.TT, sumBin r K (X.deg t) := rfl
  have hprod0 : 0 ≤ ∏ t ∈ X.F.TT, sumBin r K (X.deg t) :=
    Finset.prod_nonneg fun t _ => zero_le_one.trans (sum_one_le_bin _ _ _)
  rcases le_or_gt (1 - 1 * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * Dat.k (r := r) K / X.Y) 0 with hb | hb
  · rw [hbd]
    have h1 := mul_nonneg (neg_nonneg.mpr hb) hprod0
    have h2 := mul_nonneg hq0.le hRHS0
    nlinarith

  obtain ⟨hA0l, hA00⟩ := first_sum_factor_bounds hX.Y1 F.a32 hNs
  have hA01 : X.firstSumFactor ≤ 1 := by
    unfold Dat.firstSumFactor
    have : 0 ≤ 1 / X.a ^ (X.Ns ^ 2) := by
      have : 0 ≤ X.a := by have := F.a32; have := hX.Y1; linarith
      positivity
    linarith
  have hJ1 : 1 ≤ X.F.J := hX.valid.1
  have hk5 : (5 : ℝ) ≤ Dat.k (r := r) K := by
    unfold Dat.k
    have := hX.NsK; have := hX.r2
    exact_mod_cast (by omega : 5 ≤ r + K)
  obtain ⟨h5, h1, hr0, -, h1', hr1, htot⟩ := sum_total_loss r X.F.J X.F.TT.card (Dat.k (r := r) K) X.Y X.firstSumFactor hX.r2 hk5 hX.Y1
    F.JN (hJ1.trans F.JN) hA0l hA01 hb

  have hTf0 : ∀ j, 0 ≤ X.sumTf p K j := fun j => by
    unfold Dat.sumTf
    exact pow_nonneg (mul_nonneg (by positivity) (le_max_left _ _)) _
  have hWf0 : ∀ j, 0 ≤ X.sumWf p K j := fun j =>
    Finset.prod_nonneg fun i _ => zero_le_one.trans (sum_one_le_bin _ _ _)
  have hseg0 : ∀ j b, 0 ≤ X.segBound p K j b := fun j b => by
    rw [Dat.sum_segBound_eq]
    exact mul_nonneg (mul_nonneg (mul_nonneg hA00 (hWf0 j)) (hTf0 j))
      (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
  have step1 : ∀ la ∈ X.LA p K, ∏ j : Fin X.F.J, X.segBound p K (j.val : ℤ) (X.nz p K la (j.val : ℤ)) ≤
      ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) := by
    intro la hla
    have e1 : ∀ e : Fin X.F.J → Fin r → ℕ, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) =
        ∏ j : Fin X.F.J, G (j.val : ℤ) (X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j)) :=
      fun e => Finset.prod_congr rfl fun j _ => hGdep _ _ _ (sum_bfam_late la e j)
    rw [Finset.sum_congr rfl fun e _ => e1 e]
    have e2 := Finset.prod_univ_sum (fun j : Fin X.F.J => X.sumTset p K la (j.val : ℤ))
      (fun j ej => G (j.val : ℤ) (X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) ej))
    have e3 : X.EE p K la = Fintype.piFinset (fun j : Fin X.F.J => X.sumTset p K la (j.val : ℤ)) := by
      unfold Dat.EE Dat.sumTset
      congr
    rw [e3, ← e2]
    refine Finset.prod_le_prod₀ (fun j _ => hseg0 _ _) fun j _ => ?_
    exact hGsum (j.val : ℤ) _ (family_degrees_admissible hr hp (fun j x hx => (F.LLsub j x hx).1) la hla _)
      (fun i => X.nz p K la (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum step1) hq0.le)

  have step2 : ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, X.segBound p K (j.val : ℤ) (X.nz p K la (j.val : ℤ)) =
      (∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ))) * ∏ t : Fin n', X.sumSt p K t := by
    rw [← sum_LA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ)),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => Dat.sum_segBound_eq X p K _ _
  rw [step2]

  have step3 : ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
      ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) ≤ ∏ t : Fin n', X.sumSt p K t := by
    have hs := Finset.prod_sdiff (f := fun t => X.sumSt p K t) (Finset.subset_univ X.F.TT)
    rw [← hs, F.tiling]
    have hc : (1 : ℝ) ≤ ∏ t ∈ Finset.univ \ X.F.TT, X.sumSt p K t :=
      sum_one_le_prod _ _ fun t ht => sum_St_nontop t (Finset.mem_sdiff.mp ht).2
    have hm : ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
        ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) ≤
        ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), X.sumSt p K (posOf n' x) := by
      refine Finset.prod_le_prod₀ (fun j _ => mul_nonneg
        (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
        (Finset.prod_nonneg fun i _ => by positivity)) fun j hj => ?_
      rw [F.split (j : ℤ) (fun x => X.sumSt p K (posOf n' x))]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => by positivity)
        (Finset.prod_nonneg fun x _ => sum_St_nonneg _)
      · exact Finset.prod_le_prod₀ (fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _)) fun x hx =>
          sum_St_LL F hr hp ⟨j, Finset.mem_range.mp hj⟩ hx
      · exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => sum_St_fr F hr hp (j : ℤ) i
    have hnn : 0 ≤ ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), X.sumSt p K (posOf n' x) :=
      Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun x _ => sum_St_nonneg _
    nlinarith
  have hC0 : 0 ≤ ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ)) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (mul_nonneg hA00 (hWf0 _)) (hTf0 _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step3 hC0) hq0.le)

  have hW : ∏ j ∈ Finset.range X.F.J, X.sumWf p K (j : ℤ) = ∏ j ∈ Finset.range X.F.J, X.sumWf p K ((j : ℤ) + 1) :=
    (prod_range_shift_of_periodic (fun j => X.sumWf p K j) X.F.J hJ1 (fun j => by
      unfold Dat.sumWf
      exact Finset.prod_congr rfl fun i _ => by rw [F.perW j i])).symm
  have hQ : ((p : ℝ) ^ n') ^ (r * K) = ∏ j ∈ Finset.range X.F.J, (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r := by
    have := F.prodQ
    have h' : (p : ℝ) ^ n' = ∏ j ∈ Finset.range X.F.J, ((X.Qc p K (j : ℤ) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← this]; push_cast; rfl
    rw [h', ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have regroup : ((p : ℝ) ^ n') ^ (r * K) * ((∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ))) *
      ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
      ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1))) =
      ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
        (X.sumWf p K ((j : ℤ) + 1) * X.sumTf p K (j : ℤ) *
          (∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) *
          (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r))) := by
    rw [hQ]
    simp only [Finset.prod_mul_distrib]
    rw [hW]
    ring
  rw [regroup, hbd]
  refine le_trans (mul_le_mul_of_nonneg_right htot hprod0) ?_
  have hfin : X.firstSumFactor ^ X.F.J * sumEta r X.Y ^ X.F.TT.card * ∏ t ∈ X.F.TT, sumBin r K (X.deg t) =
      ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * ∏ x ∈ X.toLate (j : ℤ), (sumEta r X.Y * sumBin r K (X.deg (posOf n' x)))) := by
    rw [Finset.prod_mul_distrib, ← F.tiling (fun t => sumEta r X.Y * sumBin r K (X.deg t)), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, Finset.card_range]
    ring
  rw [hfin]
  have heta0 : 0 ≤ sumEta r X.Y := mul_nonneg (mul_nonneg h5 h1) hr0
  refine Finset.prod_le_prod₀ (fun j _ => mul_nonneg hA00 (Finset.prod_nonneg fun x _ =>
    mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _)))) fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ hA00
  rw [F.split (j : ℤ) (fun x => sumEta r X.Y * sumBin r K (X.deg (posOf n' x)))]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _)))
    (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
  · exact Finset.prod_le_prod₀ (fun x _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _))) fun x hx =>
      sum_fac_LL F h5 h1 h1' hr0 hr1 _ (sum_late_mem (F.LLsub _ _ hx).1).2.2.2
  · have e : X.sumWf p K ((j : ℤ) + 1) * X.sumTf p K (j : ℤ) *
        (∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) *
        (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r =
        ∏ i : Fin r, (sumBin r K ((X.Bw p K ((j : ℤ) + 1) (X.F.fr (j : ℤ) i.val) - (X.m0 K : ℤ)).toNat) *
          (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) *
          ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1) * ((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      unfold Dat.sumWf Dat.sumTf
      simp only [add_sub_cancel_right, mul_pow]
    rw [e]
    exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _))) fun i _ =>
      sum_fac_fr F hr h5 h1 hr0 (j : ℤ) i

end Main

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem fr_add_mul_period (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    F.fr (j + m * F.J) i = F.fr j i + m * n' := by
  have hper := hV.2.1
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h1 := hper (j + k * F.J) i
    rw [show j + ((k : ℤ) + 1) * (F.J : ℤ) = j + k * F.J + F.J by ring, h1, ih]
    ring
  | pred k ih =>
    have h1 := hper (j + (-(k : ℤ) - 1) * F.J) i
    rw [show j + (-(k : ℤ) - 1) * (F.J : ℤ) + F.J = j + -(k : ℤ) * F.J by ring, ih] at h1
    linarith

theorem fr_lt_fr_of_lt_of_valid (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' := by
  intro i' hii' hi'r
  induction i' with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii' with h | h
    · exact lt_trans (ih h (by omega)) (hV.2.2.1 j k (by omega))
    · subst h
      exact hV.2.2.1 j i (by omega)

theorem sum_fr_le (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' := by
  rcases h.lt_or_eq with h | h
  · exact (fr_lt_fr_of_lt_of_valid hV j i i' h h').le
  · subst h
    exact le_rfl

theorem sum_posOf_per (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  unfold posOf
  congr 3
  simp

theorem dist_add_mul_period (hV : F.Valid L₁ N₁) (j x m : ℤ) : F.dist (j + m * F.J) (x + m * n') = F.dist j x := by
  unfold Frames.dist
  rw [fr_add_mul_period hV]
  congr 1
  ring

theorem sum_prod_Ioc (g : ℕ → ℤ) (hg : Monotone g) (P : ℤ → Prop) [DecidablePred P] (ψ : ℤ → ℝ) (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ x ∈ (Finset.Ioc (g j) (g (j + 1))).filter P, ψ x =
      ∏ x ∈ (Finset.Ioc (g 0) (g m)).filter P, ψ x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, ← Finset.prod_union
      (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)), ← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le m)) (hg (Nat.le_succ m))]

end Geo

section GeoX

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (p K : ℕ)

theorem mem_late_iff (hV : X.F.Valid L₁ N₁) (j x : ℤ) :
    x ∈ X.toLate j ↔ (eFr X.F (j - 1) < x ∧ x ≤ eFr X.F j) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have : X.toLate j = nonW X.F j := rfl
  rw [this, nonW_eq hV, Finset.mem_filter, Finset.mem_Ioc]

theorem exists_shift_of_posOf_eq_of_mem_late (hV : X.F.Valid L₁ N₁) {j j' x x' : ℤ} (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : ∃ m : ℤ, j' = j + m * X.F.J ∧ x' = x + m * n' := by
  have h1 : x % (n' : ℤ) = x' % (n' : ℤ) := by rw [← posOf_val, ← posOf_val, h]
  have h2 : (n' : ℤ) ∣ x' - x := Int.ModEq.dvd h1
  obtain ⟨m, hm⟩ := h2
  have hm' : x' = x + m * n' := by linarith [mul_comm (n' : ℤ) m]
  refine ⟨m, ?_, hm'⟩
  have a1 := (mem_late_iff X hV j x).mp hx
  have a2 := (mem_late_iff X hV j' x').mp hx'
  have p1 : eFr X.F (j + m * X.F.J) = eFr X.F j + m * n' := fr_add_mul_period hV j (r - 1) m
  have p0 : eFr X.F (j + m * X.F.J - 1) = eFr X.F (j - 1) + m * n' := by
    have := fr_add_mul_period hV (j - 1) (r - 1) m
    rw [show j + m * X.F.J - 1 = j - 1 + m * X.F.J by ring]
    exact this
  exact idx_unique (eFr_strictMono hV) (x := x') a2.1.1 a2.1.2 (by rw [p0]; linarith [a1.1.1])
    (by rw [p1]; linarith [a1.1.2])

theorem sum_Rj_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Rj p K (j + m * X.F.J) = X.Rj p K j := by
  unfold Dat.Rj
  have e : j + m * X.F.J - 1 = (j - 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j - 1) 0 m, dist_add_mul_period hV]

theorem sum_Pz_per (hV : X.F.Valid L₁ N₁) (j x m : ℤ) :
    X.Pz p K (j + m * X.F.J) (x + m * n') = X.Pz p K j x := by
  unfold Dat.Pz
  rw [dist_add_mul_period hV, sum_Rj_per X p K hV]

theorem sum_Qc_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Qc p K (j + m * X.F.J) = X.Qc p K j := by
  unfold Dat.Qc
  have e : j + m * X.F.J + 1 = (j + 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j + 1) (r - 1) m, fr_add_mul_period hV j (r - 1) m, sum_Rj_per X p K hV, sum_Rj_per X p K hV]
  congr 2
  ring

theorem sum_uniqP (hV : X.F.Valid L₁ N₁) (j j' x x' : ℤ) (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : X.Pz p K j x = X.Pz p K j' x' := by
  obtain ⟨m, rfl, rfl⟩ := exists_shift_of_posOf_eq_of_mem_late X hV hx hx' h
  exact (sum_Pz_per X p K hV j x m).symm

theorem sum_perW (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) :
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val) := by
  have e1 : X.F.fr (j + X.F.J - 1) i.val = X.F.fr (j - 1) i.val + 1 * n' := by
    have := fr_add_mul_period hV (j - 1) i.val 1
    rw [show j + (X.F.J : ℤ) - 1 = j - 1 + 1 * X.F.J by ring]
    exact this
  have e2 : j + (X.F.J : ℤ) = j + 1 * X.F.J := by ring
  unfold Dat.Bw
  rw [e1, e2, sum_posOf_per, dist_add_mul_period hV, sum_Rj_per X p K hV]

theorem prod_tiling (hV : X.F.Valid L₁ N₁) (φ : Fin n' → ℝ) :
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) := by
  classical
  have hm := eFr_strictMono hV
  have h1 : ∀ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) =
      ∏ x ∈ (Finset.Ioc ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) (j + 1))).filter
        (fun x => posOf n' x ∈ X.F.TT), φ (posOf n' x) := by
    intro j _
    have : X.toLate (j : ℤ) = nonW X.F j := rfl
    rw [this, nonW_eq hV]
    simp
  rw [Finset.prod_congr rfl h1, sum_prod_Ioc (fun i : ℕ => eFr X.F ((i : ℤ) - 1))
    (fun a b hab => hm.monotone (by omega)) (fun x => posOf n' x ∈ X.F.TT) (fun x => φ (posOf n' x)) X.F.J]
  have h2 : eFr X.F ((X.F.J : ℤ) - 1) = eFr X.F (((0 : ℕ) : ℤ) - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    simp only [eFr]
    have e1 : ((X.F.J : ℤ) - 1) = -1 + X.F.J := by ring
    have e2 : (((0 : ℕ) : ℤ) - 1) = -1 := by norm_num
    rw [e1, e2, this]
  simp only [h2]
  set a := eFr X.F (((0 : ℕ) : ℤ) - 1) with ha
  symm
  refine Finset.prod_bij (fun x _ => posOf n' x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact posOf_injOn a (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1) hxy
  · intro t ht
    have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have b0 := Int.emod_nonneg ((t.val : ℤ) - (a + 1)) hn.ne'
    have b1 := Int.emod_lt_of_pos ((t.val : ℤ) - (a + 1)) hn
    have hpos : posOf n' (a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ)) = t := by
      have e : a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ) =
          (t.val : ℤ) + (-(((t.val : ℤ) - (a + 1)) / (n' : ℤ))) * n' := by
        have := Int.emod_add_mul_ediv ((t.val : ℤ) - (a + 1)) (n' : ℤ)
        linarith
      rw [e, sum_posOf_per, posOf_natCast]
    refine ⟨a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ), ?_, hpos⟩
    rw [Finset.mem_filter, Finset.mem_Ioc, hpos]
    exact ⟨⟨by omega, by omega⟩, ht⟩
  · intro x _
    rfl

theorem sum_LLsub (hV : X.F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ X.F.LLset j) : x ∈ X.toLate j ∧ x < X.F.fr j 0 := by
  classical
  unfold Frames.LLset at hx
  rw [Finset.mem_filter, Finset.mem_Ioo] at hx
  refine ⟨(mem_late_iff X hV j x).mpr ⟨⟨hx.1.1, ?_⟩, hx.2⟩, hx.1.2⟩
  exact hx.1.2.le.trans (fr_zero_le_eFr hV j)

theorem sum_frlate (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) : X.F.fr j i.val ∈ X.toLate j := by
  refine (mem_late_iff X hV j _).mpr ⟨⟨?_, ?_⟩, (hV.2.2.2.2.1 j i.val i.isLt).1⟩
  · have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    exact lt_of_lt_of_le h1 (fr_zero_le hV j i.val i.isLt)
  · exact sum_fr_le hV j i.val (r - 1) (by have := i.isLt; omega) (Nat.sub_lt (NeZero.pos r) Nat.one_pos)

theorem sum_split (hV : X.F.Valid L₁ N₁) (j : ℤ) (ψ : ℤ → ℝ) :
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val) := by
  classical
  have hinj : Function.Injective (fun i : Fin r => X.F.fr j i.val) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact absurd hab (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j a.val b.val h b.isLt))
    · exact absurd hab.symm (ne_of_lt (fr_lt_fr_of_lt_of_valid hV j b.val a.val h a.isLt))
  have hU : X.toLate j = X.F.LLset j ∪ Finset.univ.image (fun i : Fin r => X.F.fr j i.val) := by
    ext x
    rw [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hx
      have a1 := (mem_late_iff X hV j x).mp hx
      by_cases h0 : x < X.F.fr j 0
      · left
        unfold Frames.LLset
        rw [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨a1.1.1, h0⟩, a1.2⟩
      · right
        obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV j x a1.2 (not_lt.mp h0) (r - 1)
          (Nat.sub_lt (NeZero.pos r) Nat.one_pos) a1.1.2
        exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · rintro (hx | ⟨i, -, rfl⟩)
      · exact (sum_LLsub X hV j x hx).1
      · exact sum_frlate X hV j i
  have hdisj : Disjoint (X.F.LLset j) (Finset.univ.image (fun i : Fin r => X.F.fr j i.val)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx'
    have := (sum_LLsub X hV j _ hx).2
    have := fr_zero_le hV j i.val i.isLt
    omega
  rw [hU, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => hinj h)]

theorem J_le_card_TT_of_valid (hV : X.F.Valid L₁ N₁) : X.F.J ≤ X.F.TT.card := by
  classical
  refine le_trans ?_ (sum_card_nonW hV)
  calc X.F.J = ∑ _j ∈ Finset.range X.F.J, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.card_pos.mpr
      ⟨X.F.fr (j : ℤ) (⟨0, NeZero.pos r⟩ : Fin r).val, sum_frlate X hV (j : ℤ) ⟨0, NeZero.pos r⟩⟩

end GeoX

end Formalism.MainNotions.SelectionLemmas.Pf
