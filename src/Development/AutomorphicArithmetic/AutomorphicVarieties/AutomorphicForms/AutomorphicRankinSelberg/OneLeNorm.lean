module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.OneLeNorm
open Set

namespace UpperTheory.V.Af.Rs

private lemma one_le_norm {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ ‖x i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (norm_le_pi_norm x i)

private lemma ker_le (hB : KerBd) {s : ℝ} (hs : s ∈ Icc (1 : ℝ) 2) {z : UpperHalfPlane}
    (hz : z ∈ ModularGroup.fd) (x : Fin 2 → ℤ) :
    ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
  obtain ⟨-, -, h3, -, -, h6⟩ := hB s hs
  have him0 : 0 < z.im := z.im_pos
  have him : 1 / 2 < z.im := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    nlinarith
  by_cases hx : x = 0
  · subst hx
    rw [h3]
    simp
  · have hn := one_le_norm hx
    have hpos : 0 < ‖x‖ := by linarith
    have e1 : ‖x‖ ^ (-(2 * s)) ≤ ‖x‖ ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith [hs.1])
    have e2 : ‖x‖ * ‖x‖ ^ (-3 : ℝ) = ‖x‖ ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = 1 + (-3) by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have hp : 0 ≤ ‖x‖ ^ (-2 : ℝ) := Real.rpow_nonneg hpos.le _
    have hq : 4 * z.im ^ 2 ≤ 8 * z.im ^ 3 := by
      nlinarith [mul_pos (pow_pos him0 2) (by linarith : (0 : ℝ) < 2 * z.im - 1)]
    calc ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) := h6 x z hz
      _ ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-2 : ℝ) := by gcongr
      _ ≤ 8 * z.im ^ 3 * ‖x‖ ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right hq hp
      _ = 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by rw [← e2]; ring

private lemma diff_le (hB : KerBd) (hD : KerDiff) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (1 : ℝ) 2,
    ∀ x x' : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
    |ker s x z - ker s x' z| ≤ C * ‖x - x'‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := hD
  refine ⟨max C 8, hC0.trans (le_max_left _ _), ?_⟩
  intro s hs x x' z hz
  obtain ⟨-, h2, h3, -⟩ := hB s hs
  have h0 : ‖(0 : Fin 2 → ℤ)‖ ^ (-3 : ℝ) = 0 := by
    rw [norm_zero]
    exact Real.zero_rpow (by norm_num)
  by_cases hx : x = 0
  · by_cases hx' : x' = 0
    · subst hx hx'
      rw [h3, sub_self, abs_zero]
      positivity
    · subst hx
      rw [h3, zero_sub, abs_neg, abs_of_nonneg (h2 _ _), zero_sub, norm_neg, h0, zero_add]
      calc ker s x' z ≤ 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := ker_le hB hs hz x'
        _ ≤ max C 8 * ‖x'‖ * z.im ^ 3 * ‖x'‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
  · by_cases hx' : x' = 0
    · subst hx'
      rw [h3, sub_zero, abs_of_nonneg (h2 _ _), sub_zero, h0, add_zero]
      calc ker s x z ≤ 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := ker_le hB hs hz x
        _ ≤ max C 8 * ‖x‖ * z.im ^ 3 * ‖x‖ ^ (-3 : ℝ) := by
          gcongr
          exact le_max_right _ _
    · refine (hC s hs x x' hx hx' z hz).trans ?_
      gcongr
      exact le_max_left _ _

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.zDiff :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerDiff → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff := by
  intro hB hD hW L _
  obtain ⟨C, hC0, hC⟩ := diff_le hB hD
  have hS : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-3 : ℝ) := hW.1 3 (by norm_num)
  set S := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-3 : ℝ) with hSdef
  refine ⟨C * L * (2 * S), ?_⟩
  intro v v' s hs z hz
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h2, -, -, -, h6⟩ := hB s hs'
  have him : 0 < z.im := z.im_pos
  let a : Fin 2 → ℤ := fun i => ((v' i - v i : ZMod L).val : ℤ)
  have hcls : ∀ x, cls L (x + a) = v' ↔ cls L x = v := by
    intro x
    have e : cls L (x + a) = cls L x + (v' - v) := by
      funext i
      simp [cls, a, ZMod.natCast_zmod_val]
    rw [e]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  have ha : ‖a‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [a, Int.norm_eq_abs]
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    exact_mod_cast (ZMod.val_lt _).le
  have hker : Summable fun x : Fin 2 → ℤ => ker s x z := by
    refine Summable.of_nonneg_of_le (fun x => h2 x z) (fun x => h6 x z hz) ?_
    exact (hW.1 (2 * s) (by linarith [hs.1])).mul_left _
  have hker' : Summable fun x : Fin 2 → ℤ => ker s (x + a) z :=
    (Equiv.addRight a).summable_iff.mpr hker
  have hS' : Summable fun x : Fin 2 → ℤ => ‖x + a‖ ^ (-3 : ℝ) :=
    (Equiv.addRight a).summable_iff.mpr hS
  set g : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s x z else 0 with hg
  set g' : (Fin 2 → ℤ) → ℝ := fun x => if cls L x = v then ker s (x + a) z else 0 with hg'
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker
    · simp only [hg]
      split_ifs
      exacts [h2 x z, le_rfl]
    · simp only [hg]
      split_ifs
      exacts [le_rfl, h2 x z]
  have hgs' : Summable g' := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hker'
    · simp only [hg']
      split_ifs
      exacts [h2 _ z, le_rfl]
    · simp only [hg']
      split_ifs
      exacts [le_rfl, h2 _ z]
  have hZ : Zc L v s z = ∑' x, g x := rfl
  have hZ' : Zc L v' s z = ∑' x, g' x := by
    show (∑' x, if cls L x = v' then ker s x z else 0) = _
    rw [← (Equiv.addRight a).tsum_eq (fun x => if cls L x = v' then ker s x z else 0)]
    congr 1
    funext x
    change (if cls L (x + a) = v' then ker s (x + a) z else 0) = g' x
    simp only [hg', hcls]
  have hd : ∀ x, |g x - g' x| ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
    intro x
    have hnn : 0 ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by positivity
    simp only [hg, hg']
    split_ifs
    · have e : ‖x - (x + a)‖ = ‖a‖ := by simp
      calc |ker s x z - ker s (x + a) z|
          ≤ C * ‖x - (x + a)‖ * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
            hC s hs' x (x + a) z hz
        _ ≤ C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
            rw [e]
            gcongr
    · simpa using hnn
  have hh : Summable fun x : Fin 2 → ℤ =>
      C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) :=
    (hS.add hS').mul_left _
  have hshift : ∑' x : Fin 2 → ℤ, ‖x + a‖ ^ (-3 : ℝ) = S :=
    (Equiv.addRight a).tsum_eq (fun x => ‖x‖ ^ (-3 : ℝ))
  have hsum : ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ))
      = C * L * z.im ^ 3 * (2 * S) := by
    rw [tsum_mul_left, hS.tsum_add hS', hshift]
    ring
  rw [hZ, hZ', ← hgs.tsum_sub hgs']
  calc |∑' x, (g x - g' x)|
      ≤ ∑' x : Fin 2 → ℤ, C * L * z.im ^ 3 * (‖x‖ ^ (-3 : ℝ) + ‖x + a‖ ^ (-3 : ℝ)) := by
        rw [abs_le]
        constructor
        · rw [← tsum_neg]
          exact Summable.tsum_le_tsum (fun x => neg_le_of_abs_le (hd x)) hh.neg (hgs.sub hgs')
        · exact Summable.tsum_le_tsum (fun x => le_of_abs_le (hd x)) (hgs.sub hgs') hh
    _ = C * L * z.im ^ 3 * (2 * S) := hsum
    _ = C * L * (2 * S) * z.im ^ 3 := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ArSumTerm
open scoped ComplexConjugate

private lemma arSum_term (r : ℕ) (t : ℝ) (ht : (r : ℝ) + 1 ≤ t) (x y : ℝ) (n₁ m : ℕ) (hx : 0 ≤ x)
    (hn : 1 ≤ n₁ * m ^ 2) (h : x ≤ y * (m : ℝ) ^ r) :
    x ^ 2 / ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t ≤ y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hn1r : (1:ℝ) ≤ n₁ := by exact_mod_cast hn1
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx2 : x ^ 2 ≤ y ^ 2 * ((m:ℝ) ^ r) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx h 2
  have hM : (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 ≤ ((m:ℝ) ^ 2) ^ t := by
    have h1 : ((m:ℝ) ^ 2) ^ (r + 1) = (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 := by ring
    rw [← h1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by push_cast; linarith)
  have hcast : ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t = (n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)
  have hN : (0:ℝ) < (n₁ : ℝ) ^ t := Real.rpow_pos_of_pos (by linarith) t
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  rw [hcast]
  calc x ^ 2 / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t)
      ≤ (y ^ 2 * ((m:ℝ) ^ r) ^ 2) / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2)) :=
        div_le_div₀ (by positivity) hx2 (by positivity) (mul_le_mul_of_nonneg_left hM hN.le)
    _ = y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m:ℝ) ^ 2) := by
        field_simp

theorem UpperTheory.V.Af.Rs.arSum :
    UpperTheory.V.Af.Rs.ArSum := by
  intro r t a b P ht hP h3 hsu
  have ht0 : 0 < t := by have : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith
  set u : ℕ → ℝ := fun n => ‖a n‖ ^ 2 / (n:ℝ) ^ t with hu
  set w : ℕ → ℂ := fun n => starRingEnd ℂ (b n) * a n / (((n:ℝ) ^ t : ℝ) : ℂ) with hw
  have h3' : ∀ n : ℕ, ∃ q : ℕ × ℕ, 1 ≤ n → a n ≠ 0 →
      q.1 ∈ P ∧ n = q.1 * q.2 ^ 2 ∧ ‖a n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r ∧ ‖b n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r := by
    intro n
    by_cases hc : 1 ≤ n ∧ a n ≠ 0
    · obtain ⟨n₁, hn₁, m, h1, h2, h4⟩ := h3 n hc.1 hc.2
      exact ⟨(n₁, m), fun _ _ => ⟨hn₁, h1, h2, h4⟩⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose φ hφ using h3'
  set Q : Set ℕ := {n | n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0} with hQ
  set c : ℕ → ℝ := ({m | 2 ≤ m} : Set ℕ).indicator (fun m => 1 / (m:ℝ) ^ 2) with hc
  set g : ℕ × ℕ → ℝ := fun q => P.indicator u q.1 * c q.2 with hg
  set G : ℕ → ℝ := Q.indicator (fun n => g (φ n)) with hG
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hc0 : ∀ m, 0 ≤ c m := fun m => by
    simp only [hc]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hPu : Summable (P.indicator u) := hsu.indicator P
  have hzeta : Summable (fun m : ℕ => 1 / (m:ℝ) ^ 2) := hasSum_zeta_two.summable
  have hcs : Summable c := hzeta.indicator _
  have hgs : Summable g :=
    summable_mul_of_summable_norm (f := P.indicator u) (g := c)
      (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)
  have hg0 : ∀ q, 0 ≤ g q := fun q =>
    mul_nonneg (Set.indicator_nonneg (fun n _ => hu0 n) _) (hc0 _)
  have hinj : Function.Injective (fun x : Q => φ x.1) := by
    intro x y hxy
    have hxQ : x.1 ∉ P ∧ 1 ≤ x.1 ∧ a x.1 ≠ 0 := x.2
    have hyQ : y.1 ∉ P ∧ 1 ≤ y.1 ∧ a y.1 ≠ 0 := y.2
    have hx := hφ x.1 hxQ.2.1 hxQ.2.2
    have hy := hφ y.1 hyQ.2.1 hyQ.2.2
    apply Subtype.ext
    simp only at hxy
    rw [hx.2.1, hy.2.1, hxy]
  have hGs : Summable G := by
    rw [hG, ← summable_subtype_iff_indicator]
    exact hgs.comp_injective hinj
  have hc34 : ∑' m, c m ≤ 3 / 4 := by
    have e1 := hzeta.sum_add_tsum_nat_add 2
    have e2 := hcs.sum_add_tsum_nat_add 2
    have s2 : ∑ i ∈ Finset.range 2, c i = 0 := by simp [Finset.sum_range_succ, hc]
    have s1 : ∑ i ∈ Finset.range 2, (1 / ((i:ℕ):ℝ) ^ 2) = 1 := by simp [Finset.sum_range_succ]
    have e3 : (fun i => c (i + 2)) = (fun i => 1 / (((i + 2 : ℕ)) : ℝ) ^ 2) := by
      funext i
      simp only [hc]
      rw [Set.indicator_of_mem (show i + 2 ∈ {m : ℕ | 2 ≤ m} by simp)]
    rw [s2, zero_add, e3] at e2
    rw [s1, hasSum_zeta_two.tsum_eq] at e1
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hpi2 : Real.pi ^ 2 < 9.93 := by nlinarith
    rw [← e2]
    linarith
  have hGle : ∑' n, G n ≤ (∑' n, P.indicator u n) * (3 / 4) := by
    rw [hG, ← tsum_subtype]
    calc ∑' x : Q, g (φ x) ≤ ∑' q, g q := tsum_comp_le_tsum_of_inj hgs hg0 hinj
      _ = (∑' n, P.indicator u n) * ∑' m, c m := by
          exact (tsum_mul_tsum_of_summable_norm (f := P.indicator u) (g := c)
            (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hc34
          (tsum_nonneg (fun n => Set.indicator_nonneg (fun n _ => hu0 n) _))
  have hpt : ∀ n, ‖w n‖ ≤ P.indicator u n + G n ∧
      6 * P.indicator u n - 8 * G n ≤ 7 * (w n).re - u n := by
    intro n
    by_cases hn : n ∈ P
    · have hGn : G n = 0 := by
        simp only [hG]
        have hnQ : n ∉ Q := fun h => by
          have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
          exact h'.1 hn
        exact Set.indicator_of_notMem hnQ _
      have hPn : P.indicator u n = u n := Set.indicator_of_mem hn u
      have hwn : w n = ((u n : ℝ) : ℂ) := by
        simp only [hw, hu]
        rw [hP n hn, Complex.conj_mul']
        push_cast
        ring
      rw [hGn, hPn, hwn, Complex.norm_real, Real.norm_of_nonneg (hu0 n), Complex.ofReal_re]
      constructor <;> linarith [hu0 n]
    · have hPn : P.indicator u n = 0 := Set.indicator_of_notMem hn u
      by_cases hq : 1 ≤ n ∧ a n ≠ 0
      · have hφn := hφ n hq.1 hq.2
        have hGn : G n = P.indicator u (φ n).1 * c (φ n).2 := by
          simp only [hG, hg]
          exact Set.indicator_of_mem (show n ∈ Q from ⟨hn, hq.1, hq.2⟩) _
        rcases hφq : φ n with ⟨n₁, m⟩
        rw [hφq] at hφn hGn
        obtain ⟨hn₁P, hnm, hA, hB⟩ := hφn
        simp only at hn₁P hnm hA hB hGn
        rcases Nat.lt_or_ge m 2 with hlt | hm2
        · exfalso
          interval_cases m
          · simp at hnm
            omega
          · simp at hnm
            exact hn (hnm ▸ hn₁P)
        have hc2 : c m = 1 / (m:ℝ) ^ 2 := by
          simp only [hc]
          exact Set.indicator_of_mem (show m ∈ {m : ℕ | 2 ≤ m} from hm2) _
        have hPn1 : P.indicator u n₁ = u n₁ := Set.indicator_of_mem hn₁P u
        rw [hc2, hPn1] at hGn
        have h1n : 1 ≤ n₁ * m ^ 2 := hnm ▸ hq.1
        have k1 := arSum_term r t ht ‖a n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hA
        have k2 := arSum_term r t ht ‖b n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hB
        rw [← hnm] at k1 k2
        have hnt : 0 < (n:ℝ) ^ t := Real.rpow_pos_of_pos (by exact_mod_cast hq.1) t
        have hwn : ‖w n‖ = ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t := by
          simp only [hw]
          rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hnt.le]
        have hw2 : ‖w n‖ ≤ G n := by
          rw [hwn, hGn]
          have hab : ‖b n‖ * ‖a n‖ ≤ (‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
          calc ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t ≤ ((‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2) / (n:ℝ) ^ t := by gcongr
            _ = (‖a n‖ ^ 2 / (n:ℝ) ^ t + ‖b n‖ ^ 2 / (n:ℝ) ^ t) / 2 := by ring
            _ ≤ _ := by simp only [hu]; linarith
        have hun : u n ≤ G n := by
          rw [hGn]
          simp only [hu]
          exact k1
        have hre : -‖w n‖ ≤ (w n).re := by
          have := Complex.abs_re_le_norm (w n)
          linarith [neg_abs_le (w n).re]
        rw [hPn]
        constructor <;> linarith
      · have hGn : G n = 0 := by
          simp only [hG]
          have hnQ : n ∉ Q := fun h => by
            have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
            exact hq ⟨h'.2.1, h'.2.2⟩
          exact Set.indicator_of_notMem hnQ _
        have hz : w n = 0 ∧ u n = 0 := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            simp [hw, hu, Real.zero_rpow (ne_of_gt ht0)]
          · have han : a n = 0 := by
              by_contra h
              exact hq ⟨h0, h⟩
            simp [hw, hu, han]
        rw [hPn, hGn, hz.1, hz.2]
        simp
  have hws : Summable w := Summable.of_norm_bounded (hPu.add hGs) (fun n => (hpt n).1)
  have hres : Summable (fun n => (w n).re) :=
    Summable.of_norm_bounded (hPu.add hGs)
      (fun n => by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hpt n).1)
  rw [Complex.re_tsum hws]
  have hD := Summable.tsum_le_tsum (fun n => (hpt n).2)
    ((hPu.mul_left 6).sub (hGs.mul_left 8)) ((hres.mul_left 7).sub hsu)
  rw [Summable.tsum_sub (hPu.mul_left 6) (hGs.mul_left 8),
    Summable.tsum_sub (hres.mul_left 7) hsu, Summable.tsum_mul_left 6 hPu,
    Summable.tsum_mul_left 8 hGs, Summable.tsum_mul_left 7 hres] at hD
  linarith [hGle]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerDiff
open UpperHalfPlane Set

namespace UpperTheory.V.Af.Rs

private lemma kd_pow {a b t m : ℝ} (hm : 1 ≤ m) (hb : m / 2 ≤ b) (hab : b ≤ a) (ht : 2 ≤ t) (ht' : t ≤ 4) :
    |a ^ (-t) - b ^ (-t)| ≤ 128 * (a - b) * m ^ (-3 : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  set A := a ^ t with hA
  set B := b ^ t with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos ha0 t
  have hBpos : 0 < B := Real.rpow_pos_of_pos hb0 t
  have hneg_a : a ^ (-t) = A⁻¹ := Real.rpow_neg ha0.le t
  have hneg_b : b ^ (-t) = B⁻¹ := Real.rpow_neg hb0.le t
  have hBA : B ≤ A := Real.rpow_le_rpow hb0.le hab (by linarith)
  have hbern : 1 + t * (b / a - 1) ≤ B / A := by
    have h := one_add_mul_self_le_rpow_one_add (s := b / a - 1)
      (by have := div_nonneg hb0.le ha0.le; linarith) (p := t) (by linarith)
    rw [show 1 + (b / a - 1) = b / a by ring, Real.div_rpow hb0.le ha0.le] at h
    exact h
  have hsub : |a ^ (-t) - b ^ (-t)| = B⁻¹ - A⁻¹ := by
    rw [hneg_a, hneg_b, abs_sub_comm, abs_of_nonneg]
    rw [sub_nonneg]
    exact inv_anti₀ hBpos hBA
  have hkey : B⁻¹ - A⁻¹ ≤ t * (a - b) / b / B := by
    have h1 : B⁻¹ - A⁻¹ = (1 - B / A) / B := by field_simp
    have h2 : 1 - B / A ≤ t * (a - b) / b := by
      have h3 : t * (1 - b / a) ≤ t * (a - b) / b := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [one_sub_div ha0.ne']
        exact div_le_div_of_nonneg_left (by linarith) hb0 hab
      nlinarith
    rw [h1]
    exact div_le_div_of_nonneg_right h2 hBpos.le
  have hbB : m ^ 3 / 32 ≤ b * B := by
    have e1 : (m / 2) ^ (t + 1) ≤ b ^ (t + 1) := Real.rpow_le_rpow (by positivity) hb (by linarith)
    have e2 : b ^ (t + 1) = b * B := by rw [Real.rpow_add_one hb0.ne']; ring
    have e3 : (m / 2) ^ (t + 1) = m ^ (t + 1) / 2 ^ (t + 1) := Real.div_rpow hm0.le (by norm_num) _
    have e4 : m ^ (3 : ℝ) ≤ m ^ (t + 1) := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
    have e5 : (2 : ℝ) ^ (t + 1) ≤ 2 ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have e6 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have e7 : m ^ (3 : ℝ) = m ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h2pos : 0 < (2 : ℝ) ^ (t + 1) := by positivity
    have h8 : m ^ 3 / 32 ≤ m ^ (t + 1) / 2 ^ (t + 1) := by
      rw [div_le_div_iff₀ (by norm_num) h2pos]
      have hm3 : 0 ≤ m ^ 3 := by positivity
      rw [← e7] at hm3 ⊢
      rw [e6] at e5
      nlinarith
    linarith
  have hm3pos : 0 < m ^ 3 := by positivity
  have hmneg : m ^ (-3 : ℝ) = (m ^ 3)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hsub, hmneg]
  refine hkey.trans ?_
  rw [div_div]
  have hbBpos : 0 < b * B := by positivity
  rw [div_le_iff₀ hbBpos]
  have hab' : 0 ≤ a - b := by linarith
  have : t * (a - b) ≤ 4 * (a - b) := by nlinarith
  have h32 : 128 * (a - b) * (m ^ 3)⁻¹ * (m ^ 3 / 32) = 4 * (a - b) := by
    field_simp
    ring
  have hc : 0 ≤ 128 * (a - b) * (m ^ 3)⁻¹ := by positivity
  calc t * (a - b) ≤ 4 * (a - b) := this
    _ = 128 * (a - b) * (m ^ 3)⁻¹ * (m ^ 3 / 32) := h32.symm
    _ ≤ 128 * (a - b) * (m ^ 3)⁻¹ * (b * B) := mul_le_mul_of_nonneg_left hbB hc

private lemma kd_abs (x : Fin 2 → ℤ) (i : Fin 2) : |(x i : ℝ)| ≤ ‖x‖ := by
  have := norm_le_pi_norm x i
  rwa [Int.norm_eq_abs] at this

private lemma kd_one {x : Fin 2 → ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (kd_abs x i)

private lemma kd_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    1 ≤ z.re ^ 2 + z.im ^ 2 ∧ -(1 / 2) ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 1 / 2 ≤ z.im := by
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy := z.im_pos
  obtain ⟨h1, h2⟩ := hz
  rw [Complex.normSq_apply] at h1
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1 h2
  rw [abs_le] at h2
  refine ⟨by nlinarith, h2.1, h2.2, by nlinarith⟩

private lemma kd_low (x : Fin 2 → ℤ) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    ‖x‖ / 2 ≤ ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := kd_fd hz
  set c : ℝ := (x 0 : ℝ)
  set d : ℝ := (x 1 : ℝ)
  have hsq : ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ 2 = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [c, d]
    ring
  have hmax : ‖x‖ ≤ max |c| |d| := by
    rw [pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))]
    intro i
    rw [Int.norm_eq_abs]
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hN : ‖x‖ ^ 2 ≤ c ^ 2 + d ^ 2 := by
    have hN0 := norm_nonneg x
    rcases le_max_iff.mp hmax with h | h
    · have : ‖x‖ ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ hN0 h 2
      rw [sq_abs] at this
      nlinarith
    · have : ‖x‖ ^ 2 ≤ |d| ^ 2 := pow_le_pow_left₀ hN0 h 2
      rw [sq_abs] at this
      nlinarith
  have hcd : |2 * c * d * z.re| ≤ |c * d| := by
    rw [show 2 * c * d * z.re = (c * d) * (2 * z.re) by ring, abs_mul]
    have : |2 * z.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |c * d| * |2 * z.re| ≤ |c * d| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = |c * d| := mul_one _
  have hcd2 : 2 * |c * d| ≤ c ^ 2 + d ^ 2 := by
    rw [abs_mul]
    have := sq_nonneg (|c| - |d|)
    nlinarith [sq_abs c, sq_abs d]
  have hlow : (‖x‖ / 2) ^ 2 ≤ ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ 2 := by
    rw [hsq]
    have e : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 = c ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * c * d * z.re + d ^ 2 := by ring
    rw [e]
    have := neg_abs_le (2 * c * d * z.re)
    have hc2 : c ^ 2 ≤ c ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
      nlinarith [sq_nonneg c]
    nlinarith
  have hw0 := norm_nonneg ((x 0 : ℂ) * z + (x 1 : ℂ))
  nlinarith [norm_nonneg x]

private lemma kd_up (x : Fin 2 → ℤ) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ≤ 4 * ‖x‖ * z.im := by
  obtain ⟨h1, h2, h3, h4⟩ := kd_fd hz
  have hz' : ‖(z : ℂ)‖ ≤ 1 / 2 + z.im := by
    have := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    rw [abs_of_pos z.im_pos] at this
    have : |z.re| ≤ 1 / 2 := abs_le.mpr ⟨h2, h3⟩
    linarith
  have hN0 := norm_nonneg x
  calc ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ≤ ‖(x 0 : ℂ)‖ * ‖(z : ℂ)‖ + ‖(x 1 : ℂ)‖ :=
        (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ ‖x‖ * (1 / 2 + z.im) + ‖x‖ := by
        rw [Complex.norm_intCast, Complex.norm_intCast]
        have a0 := kd_abs x 0
        have a1 := kd_abs x 1
        have := norm_nonneg (z : ℂ)
        nlinarith [abs_nonneg ((x 0 : ℤ) : ℝ)]
    _ ≤ 4 * ‖x‖ * z.im := by nlinarith

private lemma kd_ker (s : ℝ) (x : Fin 2 → ℤ) (z : ℍ) :
    ker s x z = z.im ^ s * ‖(x 0 : ℂ) * z + (x 1 : ℂ)‖ ^ (-(2 * s)) := by
  unfold ker
  have hy := z.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hy.le (by positivity),
    Real.rpow_neg (norm_nonneg _), Real.rpow_mul (norm_nonneg _), div_eq_mul_inv]
  norm_num

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.kerDiff :
    UpperTheory.V.Af.Rs.KerDiff := by
  refine ⟨1024, by norm_num, ?_⟩
  intro s hs x x' hx hx' z hz
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨-, -, -, hy2⟩ := kd_fd hz
  have hy : 0 < z.im := z.im_pos
  rw [kd_ker, kd_ker]
  set w : ℂ := (x 0 : ℂ) * z + (x 1 : ℂ) with hw
  set w' : ℂ := (x' 0 : ℂ) * z + (x' 1 : ℂ) with hw'
  set S : ℝ := ‖x‖ ^ (-3 : ℝ) + ‖x'‖ ^ (-3 : ℝ) with hS
  have hS1 : 0 ≤ ‖x‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hS2 : 0 ≤ ‖x'‖ ^ (-3 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hS0 : 0 ≤ S := by positivity
  have hdiff : ‖w‖ - ‖w'‖ ≤ 4 * ‖x - x'‖ * z.im ∧ ‖w'‖ - ‖w‖ ≤ 4 * ‖x - x'‖ * z.im := by
    have e : w - w' = (((x - x') 0 : ℤ) : ℂ) * z + (((x - x') 1 : ℤ) : ℂ) := by
      simp only [hw, hw', Pi.sub_apply, Int.cast_sub]
      ring
    have hu := kd_up (x - x') hz
    rw [← e] at hu
    have h1 := abs_norm_sub_norm_le w w'
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hD : |‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s))| ≤ 128 * (4 * ‖x - x'‖ * z.im) * S := by
    rcases le_total ‖w'‖ ‖w‖ with h | h
    · have := kd_pow (kd_one hx') (kd_low x' hz) h (by linarith : (2 : ℝ) ≤ 2 * s) (by linarith)
      calc _ ≤ 128 * (‖w‖ - ‖w'‖) * ‖x'‖ ^ (-3 : ℝ) := this
        _ ≤ 128 * (4 * ‖x - x'‖ * z.im) * ‖x'‖ ^ (-3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hS2
            linarith [hdiff.1]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have := norm_nonneg (x - x')
            positivity
    · rw [abs_sub_comm]
      have := kd_pow (kd_one hx) (kd_low x hz) h (by linarith : (2 : ℝ) ≤ 2 * s) (by linarith)
      calc _ ≤ 128 * (‖w'‖ - ‖w‖) * ‖x‖ ^ (-3 : ℝ) := this
        _ ≤ 128 * (4 * ‖x - x'‖ * z.im) * ‖x‖ ^ (-3 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hS1
            linarith [hdiff.2]
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have := norm_nonneg (x - x')
            positivity
  have hys : z.im ^ s ≤ 2 * z.im ^ 2 := by
    rcases le_total z.im 1 with h | h
    · have h1 : z.im ^ s ≤ z.im ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hy h hs1
      rw [Real.rpow_one] at h1
      nlinarith
    · have h1 : z.im ^ s ≤ z.im ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs2
      rw [Real.rpow_two] at h1
      nlinarith
  have hyspos : 0 ≤ z.im ^ s := Real.rpow_nonneg hy.le _
  rw [← mul_sub, abs_mul, abs_of_nonneg hyspos]
  calc z.im ^ s * |‖w‖ ^ (-(2 * s)) - ‖w'‖ ^ (-(2 * s))|
      ≤ (2 * z.im ^ 2) * (128 * (4 * ‖x - x'‖ * z.im) * S) :=
        mul_le_mul hys hD (abs_nonneg _) (by positivity)
    _ = 1024 * ‖x - x'‖ * z.im ^ 3 * S := by ring
end
