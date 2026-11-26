module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLval
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Hurzero
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termdiff
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BTaylor2
open Finset UpperTheory.V.Bern

private lemma hd_cpow (c : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t := by
  have hmem : ((t : ℂ)) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 ht
  exact (Complex.hasStrictDerivAt_cpow_const (c := c) hmem).hasDerivAt.comp_ofReal

private lemma lip (s : ℂ) (a x y : ℝ) (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) (hs : -2 ≤ s.re) :
    ‖(y : ℂ) ^ (-s - 1) - (x : ℂ) ^ (-s - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) * ‖y - x‖ := by
  have hge : ∀ z ∈ Set.uIcc x y, a ≤ z := by
    intro z hz
    rcases Set.mem_uIcc.1 hz with h | h
    · exact le_trans hx h.1
    · exact le_trans hy h.1
  have hder : ∀ z ∈ Set.uIcc x y, HasDerivWithinAt (fun w : ℝ => (w : ℂ) ^ (-s - 1))
      ((-s - 1) * (z : ℂ) ^ (-s - 1 - 1)) (Set.uIcc x y) z := by
    intro z hz
    exact (hd_cpow (-s - 1) z (lt_of_lt_of_le ha (hge z hz))).hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc x y, ‖(-s - 1) * (z : ℂ) ^ (-s - 1 - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0]
    have h1 : ‖-s - 1‖ = ‖s + 1‖ := by
      rw [show -s - 1 = -(s + 1) by ring, norm_neg]
    have h2 : (-s - 1 - 1).re = -s.re - 2 := by
      simp; ring
    rw [h1, h2]
    have h3 : z ^ (-s.re - 2) ≤ a ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos ha (hge z hz) (show -s.re - 2 ≤ 0 by linarith)
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc x y)
    Set.left_mem_uIcc Set.right_mem_uIcc

theorem UpperTheory.V.Bern.b_taylor2 :
    ∀ (s : ℂ) (a u v : ℝ), 0 < a → a ≤ u → a ≤ v → -2 ≤ s.re → ‖(v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
  intro s a u v ha hu hv hs
  have hge : ∀ z ∈ Set.uIcc u v, a ≤ z := by
    intro z hz
    rcases Set.mem_uIcc.1 hz with h | h
    · exact le_trans hu h.1
    · exact le_trans hv h.1
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1) with hg
  have hder : ∀ z ∈ Set.uIcc u v, HasDerivWithinAt g
      (-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)) (Set.uIcc u v) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    have h1 := hd_cpow (-s) z hz0
    have h2 : HasDerivAt (fun x : ℝ => s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1))
        (s * 1 * (u : ℂ) ^ (-s - 1)) z :=
      (((hasDerivAt_id z).ofReal_comp.sub_const (u : ℂ)).const_mul s).mul_const _
    have h3 := (h1.sub_const ((u : ℂ) ^ (-s))).add h2
    simp only [mul_one] at h3
    exact h3.hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc u v, ‖-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)‖ ≤
      ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by
    intro z hz
    have he : -s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1) =
        s * ((u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)) := by ring
    rw [he, norm_mul]
    have hl := lip s a z u ha (hge z hz) hu hs
    have hd : ‖u - z‖ ≤ ‖v - u‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
      exact Set.abs_sub_left_of_mem_uIcc hz
    have hC : 0 ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by positivity
    calc ‖s‖ * ‖(u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖u - z‖) := by gcongr
      _ ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by ring
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc u v)
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hgu : g u = 0 := by simp [hg]
  have hgv : g v = (v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1) := rfl
  rw [hgu, sub_zero, hgv] at key
  calc _ ≤ _ := key
    _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
      rw [Real.norm_eq_abs, mul_assoc _ |v - u| |v - u|, ← sq, sq_abs]
end

open Finset UpperTheory.V.Bern

private theorem termdiff_rpow_le {a e : ℝ} (ha : 0 < a) (h1 : -5 ≤ e) (h2 : e ≤ -(3 / 2)) :
    a ^ e ≤ 1 / |a| ^ (3 / 2 : ℝ) + 1 / |a| ^ (5 : ℝ) := by
  rw [abs_of_pos ha]
  have p1 : 0 ≤ 1 / a ^ (3 / 2 : ℝ) := by positivity
  have p2 : 0 ≤ 1 / a ^ (5 : ℝ) := by positivity
  rcases le_or_gt 1 a with h | h
  · have h' : a ^ e ≤ a ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le h h2
    rw [Real.rpow_neg ha.le, ← one_div] at h'
    linarith
  · have h' : a ^ e ≤ a ^ (-5 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha h.le h1
    rw [Real.rpow_neg ha.le, ← one_div] at h'
    linarith

private theorem termdiff_cpow {a : ℝ} (ha : 0 < a) : Differentiable ℂ (fun s : ℂ => (a : ℂ) ^ (-s)) := by
  exact Differentiable.const_cpow differentiable_id.neg (Or.inl (by exact_mod_cast ha.ne'))

theorem UpperTheory.V.Bern.b_termdiff :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s)))) ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) := by
  intro x hx0 hx1
  have hU : IsOpen ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => 24 * (1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ)))
    ?_ ?_ hU ?_
  · exact (((Real.summable_one_div_nat_add_rpow x (3 / 2)).2 (by norm_num)).add
      ((Real.summable_one_div_nat_add_rpow x 5).2 (by norm_num))).mul_left 24
  · intro n
    have hb : ∀ b : ℝ, 0 < b → Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (-s)) :=
      fun b hb => termdiff_cpow hb
    have h1 : (0 : ℝ) < (n : ℝ) + x := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    exact (((hb _ h1).sub (hb _ h2)).sub
      ((differentiable_const _).mul ((hb _ h2).sub (hb _ h3)))).differentiableOn
  · intro n s hs
    obtain ⟨hre, hball⟩ := hs
    simp only [Set.mem_setOf_eq] at hre
    rw [mem_ball_zero_iff] at hball
    have ha : (0 : ℝ) < (n : ℝ) + x := by positivity
    have hre2 : -2 ≤ s.re := by linarith
    have hR1 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + x) ha (by linarith) le_rfl hre2
    have hR2 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + 2) ha (by linarith) (by linarith) hre2
    have hA := termdiff_rpow_le ha (e := -s.re - 2)
      (by linarith [Complex.re_le_norm s]) (by linarith)
    have hA0 : 0 ≤ ((n : ℝ) + x) ^ (-s.re - 2) := Real.rpow_nonneg ha.le _
    have hs1 : ‖s + 1‖ ≤ 4 := by
      have := norm_add_le s 1
      rw [norm_one] at this
      linarith
    have hP : ‖s‖ * ‖s + 1‖ ≤ 3 * 4 := mul_le_mul hball.le hs1 (norm_nonneg _) (by norm_num)
    set B := 1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ) with hB
    have hB0 : 0 ≤ B := hA0.trans hA
    have hsq1 : ((n : ℝ) + x - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hsq2 : ((n : ℝ) + 2 - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hR1' := hR1.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq1 (sq_nonneg _) (by positivity))
    have hR2' := hR2.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq2 (sq_nonneg _) (by positivity))
    have hnx : ‖(1 : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ = ‖((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + x : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))
            + (1 - (x : ℂ)) * ((((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + 2 : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))‖ := by
          congr 1
          push_cast
          ring
      _ ≤ 3 * 4 * B * 1 + 1 * (3 * 4 * B * 1) :=
          (norm_add_le _ _).trans (by
            rw [norm_mul]
            exact add_le_add hR1' (mul_le_mul hnx hR2' (norm_nonneg _) zero_le_one))
      _ = 24 * B := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termsum
open Finset UpperTheory.V.Bern

private theorem hasSum_hurwitzZeta (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (((n : ℝ) + x : ℝ) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s) := by
  convert HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨h0, h1⟩ hs using 1
  ext1 n
  rw [Complex.cpow_neg, one_div]
  push_cast
  rfl

theorem UpperTheory.V.Bern.b_termsum :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))) = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ)) := by
  intro x hx0 hx1 s hs
  have hA := hasSum_hurwitzZeta x hx0.le hx1 s hs
  have hB := hasSum_hurwitzZeta 1 zero_le_one le_rfl s hs
  have hC : HasSum (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    have e1 : (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) = fun n : ℕ => (((((n + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
      funext n
      congr 1
      push_cast
      ring
    have e2 : ∑ i ∈ range 1, (((((i : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = 1 := by
      simp
    rw [e1, ← e2]
    exact h
  have hT := (hA.sub hB).sub ((hB.sub hC).mul_left (1 - (x : ℂ)))
  rw [hT.tsum_eq]
  ring
end

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_hurzero :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  intro x hx0 hx1
  set U : Set ℂ := {s | -1 / 2 < s.re} ∩ Metric.ball 0 3 with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hG : DifferentiableOn ℂ (fun s => HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s
      - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ))) U := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.sub_const
    rcases eq_or_ne s 1 with rfl | hs
    · have := (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (x : UnitAddCircle)).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div ((1 : ℝ) : UnitAddCircle))
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp only [Pi.sub_apply]; ring)
    · exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta _ hs)
  have hev : ∀ᶠ s in nhds (2 : ℂ), 1 < s.re :=
    (Complex.continuous_re.tendsto 2).eventually (lt_mem_nhds (by norm_num))
  have h2 : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num⟩
  have heq := ((b_termdiff x hx0 hx1).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) hUc h2 (hev.mono fun s hs => b_termsum x hx0 hx1 s hs)
  have h0 := heq (show (0 : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩)
  have h1 : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, riemannZeta_zero]
  simp only [neg_zero, Complex.cpow_zero, sub_self, mul_zero, tsum_zero] at h0
  rw [h1] at h0
  linear_combination -h0
end

open Finset UpperTheory.V.Bern

private theorem hurwitzZeta_one_sub_eq_bernoulli (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (1 - k) =
      -1 / k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0 := by push_cast; ring
    rw [e, b_hurzero x h0 h1]
    simp [Polynomial.bernoulli_one]
  · have := HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩
    have e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [e, this]
    push_cast
    ring

theorem UpperTheory.V.Bern.b_lval :
    ∀ {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ), 1 ≤ k → ZMod.LFunction Φ (1 - k) = -genB k Φ / k := by
  intro N _ Φ k hk
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hpow : (N : ℂ) ^ (-(1 - (k:ℂ))) = (N:ℂ) ^ ((k:ℤ) - 1) := by
    rw [show -(1 - (k:ℂ)) = (((k:ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hx0 : (0:ℝ) < a / N := div_pos (by exact_mod_cast ha.1) hN
  have hx1 : (a:ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast ha.2)
  rw [ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀,
    map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hq : (algebraMap ℚ ℂ) ((a:ℚ) / N) = (((a:ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
  rw [hq]
  field_simp
end

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_lprim :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), 1 ≤ k → χ.LFunction (1 - k) = -genB k χ / k ∧ Lprim χ (1 - k) = -Bprim k χ / k := by
  intro N _ χ k hk
  refine ⟨UpperTheory.V.Bern.b_lval χ k hk, ?_⟩
  unfold UpperTheory.V.Bern.Lprim UpperTheory.V.Bern.Bprim
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  exact UpperTheory.V.Bern.b_lval _ k hk
