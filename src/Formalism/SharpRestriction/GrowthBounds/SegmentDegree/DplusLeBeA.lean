module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WindowSmall
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem two_N_lt_K (H : HypT N n0 r K LL B od bb a La p) : 2 * N < K := by
  have h := H.H4
  have hr := H.r1
  have hk : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by omega
    exact_mod_cast this
  have : (2 * N : ℝ) < (K : ℝ) := by linarith
  exact_mod_cast this

theorem dplus_le_beA (_H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) (hs : s ≤ n0) : dplus LL dd s ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = true
  · rw [if_pos hl, if_pos (by omega), hdd l (by omega)]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem dminus_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) : dminus LL dd s ≤ beA n0 B := by
  unfold dminus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = false
  · have hln : l.val < n0 := by
      by_contra hcon
      have := H.vec_true_of_late l (by omega)
      rw [hl.2] at this
      exact absurd this (by simp)
    rw [if_pos hl, if_pos hln, hdd l hln]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem path_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin (r + K)), P.mu ⟨s, hs⟩ m ≤ (beA n0 B : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, P.zero]; simp
  | succ s ih =>
    intro hs m
    by_cases hsn : s + 1 ≤ n0
    · refine le_trans (mu_le_dplus P (s + 1) hs m) ?_
      exact_mod_cast dplus_le_beA H hP.degs (s + 1) hsn
    · have hsN : s < N := by omega
      have hv : LL.vec ⟨s, hsN⟩ = true := H.vec_true_of_late ⟨s, hsN⟩ (by simp only; omega)
      by_cases hm : m.val = 0
      · have := hP.head ⟨s, hsN⟩ m (by simp only; omega) (by omega)
        exact le_of_eq this
      · have h := step_vec P ⟨s, hsN⟩ hv
        have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := h.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) _)

theorem beA_le (H : HypT N n0 r K LL B od bb a La p) : (beA n0 B : ℝ) ≤ 2 * a * (N : ℝ) := by
  unfold beA
  push_cast
  have ha : (0 : ℝ) ≤ 2 * a := by have := H.a3; linarith
  calc ∑ i : Fin N, (if i.val < n0 then (B i : ℝ) else 0) ≤ ∑ _i : Fin N, 2 * a := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i.val < n0
        · rw [if_pos hi]; exact (H.H1 i hi).2
        · rw [if_neg hi]; exact ha
    _ = 2 * a * (N : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end

def code (N r K : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Fin N × Fin (2 * N) → ℕ := fun v =>
  if h : v.2.val < N ∧ v.2.val < r + K then (μ v.1.succ ⟨v.2.val, h.2⟩).toNat
  else if h' : r + K - 2 * N + v.2.val < r + K then (-μ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).toNat else 0

theorem path_count_finite : PathCountFinite := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hK := two_N_lt_K H
  set M := beA n0 B with hM
  let t : Finset (Fin N × Fin (2 * N) → ℕ) := Fintype.piFinset fun _ => Finset.range (M + 1)
  have hshape : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ∀ (s : Fin (N + 1)) (m : Fin (r + K)),
      (m.val + N < r + K → 0 ≤ μ s m) ∧ (N ≤ m.val → μ s m ≤ 0) ∧ μ s m ≤ (M : ℤ) ∧ -(M : ℤ) ≤ μ s m := by
    rintro μ ⟨dd, hP⟩ s m
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨fun h => mu_nonneg P s.val s.2 m (by have := s.2; omega),
      fun h => mu_nonpos P s.val s.2 m (by have := s.2; omega), path_le_beA H P hP s.val s.2 m, ?_⟩
    refine le_trans ?_ (neg_dminus_le_mu P s.val s.2 m)
    have := dminus_le_beA H hP.degs s.val
    have h' : (dminus LL dd s.val : ℤ) ≤ (M : ℤ) := by exact_mod_cast this
    linarith
  have hmaps : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, code N r K μ ∈ (t : Set (Fin N × Fin (2 * N) → ℕ)) := by
    intro μ hμ
    simp only [t, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro v
    unfold code
    split_ifs with h h'
    · have := (hshape μ hμ v.1.succ ⟨v.2.val, h.2⟩).2.2.1
      omega
    · have := (hshape μ hμ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).2.2.2
      omega
    · omega
  have hinj : Set.InjOn (code N r K) (SP (r := r) (K := K) LL n0 B) := by
    intro μ hμ μ' hμ' hc
    funext s m
    induction s using Fin.cases with
    | zero =>
      obtain ⟨dd, hP⟩ := hμ
      obtain ⟨dd', hP'⟩ := hμ'
      obtain ⟨P, rfl⟩ := hP.path
      obtain ⟨P', rfl⟩ := hP'.path
      rw [P.zero, P'.zero]
    | succ i =>
      have h1 := hshape μ hμ i.succ m
      have h2 := hshape μ' hμ' i.succ m
      by_cases hm : m.val < N
      · have hcv := congrFun hc (i, ⟨m.val, by omega⟩)
        unfold code at hcv
        rw [dite_eq_left ⟨hm, m.2⟩, dite_eq_left ⟨hm, m.2⟩] at hcv
        have e1 := h1.1 (by omega)
        have e2 := h2.1 (by omega)
        have hcv' : (μ i.succ m).toNat = (μ' i.succ m).toNat := hcv
        omega
      · by_cases hm2 : m.val + N < r + K
        · have e1 := h1.1 hm2
          have e2 := h2.1 hm2
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
        · have hidx : m.val - (r + K - 2 * N) < 2 * N := by have := m.2; omega
          have hcv := congrFun hc (i, ⟨m.val - (r + K - 2 * N), hidx⟩)
          unfold code at hcv
          have hn1 : ¬ ((m.val - (r + K - 2 * N)) < N ∧ (m.val - (r + K - 2 * N)) < r + K) := by omega
          have hn2 : r + K - 2 * N + (m.val - (r + K - 2 * N)) < r + K := by have := m.2; omega
          rw [dite_eq_right hn1, dite_eq_right hn1, dite_eq_left hn2, dite_eq_left hn2] at hcv
          have hme : (⟨r + K - 2 * N + (m.val - (r + K - 2 * N)), hn2⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only; omega)
          rw [hme] at hcv
          have hcv' : (-μ i.succ m).toNat = (-μ' i.succ m).toNat := hcv
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
  have hfin : (SP (r := r) (K := K) LL n0 B).Finite :=
    Set.Finite.of_injOn (fun μ hμ => hmaps μ hμ) hinj t.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn (code N r K) hmaps hinj t.finite_toSet
  rw [Set.ncard_coe_finset] at hle
  have hcard : t.card = (M + 1) ^ (N * (2 * N)) := by
    simp [t, Fintype.card_piFinset]
  rw [hcard] at hle
  have hA : (0 : ℝ) < 1 + 2 * a * (N : ℝ) := by
    have := H.a3
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 1 + 2 * a * (N : ℝ) := by
    have := beA_le H
    push_cast
    linarith
  calc ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ (((M + 1) ^ (N * (2 * N)) : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((M + 1 : ℕ) : ℝ) ^ (N * (2 * N)) := by push_cast; rfl
    _ ≤ (1 + 2 * a * (N : ℝ)) ^ (N * (2 * N)) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a) := by
        unfold ell0
        rw [← Real.exp_log hA, ← Real.exp_nat_mul, Real.log_exp]
        congr 1
        push_cast
        ring

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_St {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).Finite := by
  classical
  refine Set.Finite.of_injOn (f := fun I (c : colRange mu) => I c.1) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    Set.finite_univ
  intro I hI I' hI' h
  funext c
  by_cases hc : c ∈ colRange mu
  · exact congrFun h ⟨c, hc⟩
  · rw [hI.1 c hc, hI'.1 c hc]

theorem wt_eq (D : Formalism.BasicNotions.D7) (h3 : admB3 D) {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (hd : Dominant (pEnd mu)) :
    ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).ncard = stCount n (pEnd mu) := by
  have h1 := h3 n N mu hd
  have h2 := h3 n 0 (fun _ => pEnd mu) hd
  have h4 : ((Nat.card {I : ℤ → Finset (Fin n) // IsSt mu I} : ℕ) : ℚ) = ((stCount n (pEnd mu) : ℕ) : ℚ) := by
    rw [h1]; unfold stCount; rw [h2]; rfl
  rw [← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem stCount_zero (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (n : ℕ) : stCount n (0 : Fin n → ℤ) = 1 := by
  have h2 := h3 n 0 (fun _ => (0 : Fin n → ℤ)) (fun _ _ _ => le_rfl)
  have h4 : ((stCount n (0 : Fin n → ℤ) : ℕ) : ℚ) = 1 := by
    unfold stCount
    rw [h2]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    split_ifs with hij
    · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
        have h5 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
        linarith
      simp only [pEnd, Pi.zero_apply, Int.cast_zero, sub_zero, zero_add]
      exact div_self this
    · rfl
  exact_mod_cast h4

theorem stCount_cast {n n' : ℕ} (h : n = n') (la : Fin n' → ℤ) :
    stCount n (fun l => la (Fin.cast h l)) = stCount n' la := by
  subst h; rfl

open Classical in
theorem pieri_vec (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i) (ν i + b)).filter (fun μ => HStrip ν μ b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).1

open Classical in
theorem pieri_cov (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i - b) (ν i)).filter (fun μ => HStrip μ ν b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).2

variable {N r K : ℕ}

def StepOK (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (i : Fin N) (la la' : Fin (r + K) → ℤ) : Prop :=
  (i.val < n0 → if LL.vec i then HStrip la la' (B i) else HStrip la' la (B i)) ∧
  (n0 ≤ i.val → (∃ d : ℕ, HStrip la la' d) ∧ ∀ m : Fin (r + K), m.val ≤ i.val - n0 → la' m = (beA n0 B : ℤ))

def VP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  μ 0 = 0 ∧ (∀ t : Fin (N + 1), t.val ≤ s → Dominant (μ t)) ∧
    ∀ i : Fin N, i.val < s → StepOK LL n0 B i (μ i.castSucc) (μ i.succ)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem sp_iff (H : HypT N n0 r K LL B od bb a La p) (μ : Fin (N + 1) → Fin (r + K) → ℤ) :
    μ ∈ SP (r := r) (K := K) LL n0 B ↔ VP LL n0 B N μ := by
  classical
  constructor
  · rintro ⟨dd, hP⟩
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨P.zero, fun t _ => P.dom t, fun i _ => ⟨fun hi => ?_, fun hi => ⟨⟨dd i, ?_⟩, fun m hm => hP.head i m hi hm⟩⟩⟩
    · have := P.step i
      rwa [hP.degs i hi] at this
    · exact step_vec P i (H.vec_true_of_late i (by omega))
  · rintro ⟨h0, hd, hs⟩
    have hex : ∀ i : Fin N, ∃ d : ℕ, (i.val < n0 → d = B i) ∧
        if LL.vec i then HStrip (μ i.castSucc) (μ i.succ) d else HStrip (μ i.succ) (μ i.castSucc) d := by
      intro i
      by_cases hi : i.val < n0
      · exact ⟨B i, fun _ => rfl, (hs i i.2).1 hi⟩
      · obtain ⟨d, hd'⟩ := ((hs i i.2).2 (by omega)).1
        refine ⟨d, fun h => absurd h hi, ?_⟩
        rw [if_pos (H.vec_true_of_late i (by omega))]
        exact hd'
    choose dd hdd using hex
    exact ⟨dd, ⟨⟨μ, h0, fun t => hd t (by have := t.2; omega), fun i => (hdd i).2⟩, rfl⟩, fun i hi => (hdd i).1 hi,
      fun i m hi hm => ((hs i i.2).2 hi).2 m hm⟩

theorem vp_le_dplus {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → t ≤ n0 → ∀ m, μ ⟨t, ht⟩ m ≤ (dplus LL B t : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts htn m
    have htN : t < N := by omega
    have ih' := ih (by omega) (by omega) (by omega) m
    have hst := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).1 (by simp only; omega)
    have hd : dplus LL B (t + 1) = dplus LL B t + if LL.vec ⟨t, htN⟩ = true then B ⟨t, htN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B t htN
    rw [hd]
    cases hv : LL.vec ⟨t, htN⟩ with
    | true =>
      rw [if_pos hv] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m + (B ⟨t, htN⟩ : ℤ) := strip_le_add hst m
      simp only [if_true]
      push_cast
      linarith
    | false =>
      rw [if_neg (by simp [hv])] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m := hst.1 m
      simp
      linarith

theorem dplus_le_beA' (t : ℕ) (ht : t ≤ n0) : dplus LL B t ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < t ∧ LL.vec l = true
  · rw [if_pos hl, if_pos (by omega)]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem vp_le {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → ∀ m, μ ⟨t, ht⟩ m ≤ (beA n0 B : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts m
    by_cases htn : t + 1 ≤ n0
    · refine le_trans (vp_le_dplus h (t + 1) ht hts htn m) ?_
      exact_mod_cast dplus_le_beA' (t + 1) htn
    · have htN : t < N := by omega
      obtain ⟨⟨d, hst⟩, hhead⟩ := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).2 (by simp only; omega)
      by_cases hm : m.val = 0
      · exact le_of_eq (hhead m (by omega))
      · have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := hst.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) (by omega) _)


open Classical in
theorem vp_update {s : ℕ} (hs : s < N) {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ)
    (la' : Fin (r + K) → ℤ) (hd : Dominant la')
    (hst : StepOK LL n0 B ⟨s, hs⟩ (μ (⟨s, hs⟩ : Fin N).castSucc) la') :
    VP LL n0 B (s + 1) (Function.update μ (⟨s, hs⟩ : Fin N).succ la') := by
  have hne : ∀ t : Fin (N + 1), t.val ≤ s → t ≠ (⟨s, hs⟩ : Fin N).succ := by
    intro t ht he
    rw [he] at ht
    simp at ht
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (hne 0 (by simp))]; exact h.1
  · intro t ht
    by_cases he : t = (⟨s, hs⟩ : Fin N).succ
    · rw [he, Function.update_self]; exact hd
    · rw [Function.update_of_ne he]
      refine h.2.1 t ?_
      have : t.val ≠ s + 1 := fun hv => he (Fin.ext (by simpa using hv))
      omega
  · intro i hi
    by_cases he : i.val = s
    · have hi' : i = ⟨s, hs⟩ := Fin.ext he
      subst hi'
      rw [Function.update_self, Function.update_of_ne (hne _ (by simp))]
      exact hst
    · rw [Function.update_of_ne (hne _ (by simp; omega)), Function.update_of_ne (hne _ (by simp; omega))]
      exact h.2.2 i (by omega)

end

end Formalism.MainNotions.SelectionLemmas.Pf.T
