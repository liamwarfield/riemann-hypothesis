module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NotSummableTwo
open Filter Topology Set

private lemma not_summable_two : ¬ Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * (1 : ℝ))) := by
  intro hs
  set f : (Fin 2 → ℤ) → ℝ := fun x => ‖x‖ ^ (-(2 * (1 : ℝ))) with hf
  have hnn : ∀ x, 0 ≤ f x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  let g : ℕ × ℕ → (Fin 2 → ℤ) := fun p => ![(p.1 : ℤ) + 1, (p.2 : ℤ)]
  have hg : Function.Injective g := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [g] at h0 h1
    exact Prod.ext (by omega) (by omega)
  have hsg : Summable (f ∘ g) := hs.comp_injective hg
  have hprod : Summable fun a : ℕ => ∑' b : ℕ, (f ∘ g) (a, b) := hsg.prod
  have key : ∀ a : ℕ, (1 : ℝ) / ((a : ℝ) + 1) ≤ ∑' b : ℕ, (f ∘ g) (a, b) := by
    intro a
    have hrow : Summable fun b : ℕ => (f ∘ g) (a, b) := hsg.prod_factor a
    have hterm : ∀ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) = 1 / ((a : ℝ) + 1) ^ 2 := by
      intro b hb
      have hb' : b ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hn : ‖g (a, b)‖ = (a : ℝ) + 1 := by
        apply le_antisymm
        · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
          intro i
          fin_cases i
          · simp [g, Int.norm_eq_abs]
            rw [abs_of_nonneg (by positivity)]
          · simp [g, Int.norm_eq_abs]
            have : (b : ℝ) ≤ a := by exact_mod_cast hb'
            linarith
        · have h := norm_le_pi_norm (g (a, b)) 0
          have h2 : ‖g (a, b) 0‖ = (a : ℝ) + 1 := by
            simp [g, Int.norm_eq_abs]
            positivity
          linarith
      simp only [Function.comp, hf, hn]
      rw [show (-(2 * (1 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
        Real.rpow_natCast, one_div]
    calc (1 : ℝ) / ((a : ℝ) + 1)
        = ∑ b ∈ Finset.range (a + 1), 1 / ((a : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
      _ = ∑ b ∈ Finset.range (a + 1), (f ∘ g) (a, b) :=
          Finset.sum_congr rfl (fun b hb => (hterm b hb).symm)
      _ ≤ ∑' b, (f ∘ g) (a, b) := hrow.sum_le_tsum _ (fun b _ => hnn _)
  have hsum : Summable fun a : ℕ => (1 : ℝ) / ((a : ℝ) + 1) :=
    Summable.of_nonneg_of_le (fun a => by positivity) key hprod
  have hsum' : Summable fun a : ℕ => (1 : ℝ) / ((a + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hsum
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hsum')

theorem UpperTheory.V.Af.Rs.wTop :
    UpperTheory.V.Af.Rs.WTop := by
  unfold UpperTheory.V.Af.Rs.WTop
  refine ⟨fun t ht => EisensteinSeries.summable_one_div_norm_rpow ht, fun M => ?_⟩
  have hnn : ∀ (s : ℝ) (x : Fin 2 → ℤ), 0 ≤ ‖x‖ ^ (-(2 * s)) :=
    fun s x => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin 2 → ℤ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))) := by
    by_contra h
    push_neg at h
    exact not_summable_two (summable_of_sum_le (hnn 1) h)
  have ht : Tendsto (fun s : ℝ => ∑ x ∈ F, ‖x‖ ^ (-(2 * s))) (𝓝 1)
      (𝓝 (∑ x ∈ F, ‖x‖ ^ (-(2 * (1 : ℝ))))) := by
    apply tendsto_finsetSum
    intro x _
    have hc : ContinuousAt (fun s : ℝ => ‖x‖ ^ (-(2 * s))) 1 := by
      apply ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) (g := fun y : ℝ => ‖x‖ ^ y)
      · exact Real.continuousAt_const_rpow' (by norm_num)
      · fun_prop
    exact hc
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), M < ∑ x ∈ F, ‖x‖ ^ (-(2 * s)) ∧ s ∈ Ioc 1 2 := by
    refine ((ht.eventually (lt_mem_nhds hF)).filter_mono nhdsWithin_le_nhds).and ?_
    have hI : Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hI] with s hs using ⟨hs.1, hs.2.le⟩
  obtain ⟨s, hsM, hs⟩ := hev.exists
  refine ⟨s, hs, ?_⟩
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith [hs.1])
  exact hsM.le.trans (hsum.sum_le_tsum F (fun x _ => hnn s x))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ArFact
open UpperTheory.V.Af.Rs in
private theorem arFact_agree (e e' a b : ℕ → ℂ) (ha : Rec e a) (hb : Rec e' b)
    (hp : ∀ p : ℕ, p.Prime → b p = a p) :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → e p = e' p) → b n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hdiv
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [ha.1, hb.1]
  · obtain ⟨p, hpp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨n', rfl⟩ := hpn
    have hn' : 1 ≤ n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hlt : n' < p * n' := by have := hpp.two_le; nlinarith
    have hep : e p = e' p := hdiv p hpp (dvd_mul_right p n')
    have hsub : ∀ q : ℕ, q.Prime → q ∣ n' → e q = e' q :=
      fun q hq hqd => hdiv q hq (dvd_mul_of_dvd_right hqd p)
    have h1 := ha.2 p hpp n' hn'
    have h2 := hb.2 p hpp n' hn'
    have hb' := ih n' hlt hn' hsub
    by_cases hpd : p ∣ n'
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have hlt' : t < p * t := by have := hpp.two_le; nlinarith
      have hbt := ih t (by nlinarith) ht
        (fun q hq hqd => hsub q hq (dvd_mul_of_dvd_right hqd p))
      rw [if_pos (dvd_mul_right p t), hdt] at h1 h2
      rw [hbt, hb', hp p hpp, ← hep] at h2
      linear_combination h2 - h1
    · rw [if_neg hpd, mul_zero, add_zero] at h1 h2
      rw [hb', hp p hpp] at h2
      rw [h2, h1]

theorem UpperTheory.V.Af.Rs.arFact :
    UpperTheory.V.Af.Rs.ArFact := by
  intro r e e' a b ha hb hp hbad hbd
  refine ⟨{n | b n = a n}, fun n hn => hn, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn han
  by_cases hgood : ∀ p : ℕ, p.Prime → p ∣ n → e p = e' p
  · have hag := arFact_agree e e' a b ha hb hp n hn hgood
    exact ⟨n, hag, 1, by ring, by simp, by simp [hag]⟩
  · push_neg at hgood
    obtain ⟨p, hpp, hpn, hne⟩ := hgood
    have hap : a p = 0 := hbad p hpp hne
    have hbp : b p = 0 := by rw [hp p hpp, hap]
    obtain ⟨n'', rfl⟩ := hpn
    have hn'' : 1 ≤ n'' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have h1 := ha.2 p hpp n'' hn''
    by_cases hpd : p ∣ n''
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn'')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have h2 := hb.2 p hpp (p * t) hn''
      rw [if_pos (dvd_mul_right p t), hdt, hap, zero_mul] at h1
      rw [if_pos (dvd_mul_right p t), hdt, hbp, zero_mul] at h2
      have hA : a (p * (p * t)) = -(e p * a t) := by linear_combination h1
      have hB : b (p * (p * t)) = -(e' p * b t) := by linear_combination h2
      have hat : a t ≠ 0 := by
        intro h0
        apply han
        rw [hA, h0, mul_zero, neg_zero]
      have hlt : t < p * (p * t) := by have := hpp.two_le; nlinarith
      obtain ⟨n₁, hn₁, m, hnm, hA1, hB1⟩ := ih t hlt ht hat
      refine ⟨n₁, hn₁, p * m, by rw [hnm]; ring, ?_, ?_⟩
      · rw [hA, norm_neg, norm_mul]
        calc ‖e p‖ * ‖a t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).1 hA1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
      · rw [hB, norm_neg, norm_mul]
        calc ‖e' p‖ * ‖b t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).2 hB1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
    · exfalso
      apply han
      rw [if_neg hpd, mul_zero, add_zero, hap, zero_mul] at h1
      exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ClsProp
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private theorem cls_rep (hR : RowRep) (L : ℕ) [NeZero L] (v : Fin 2 → ZMod L) :
    ∃ (n : ℕ) (γ : SL(2, ℤ)), v = cls L ((n : ℤ) • row γ) := by
  obtain ⟨n, γ, h⟩ := hR (fun i => ((v i).val : ℤ))
  refine ⟨n, γ, ?_⟩
  rw [← h]
  funext i
  simp [cls]

private theorem cls_smul (L : ℕ) (m n : ℕ) (x : Fin 2 → ℤ) :
    (m : ZMod L) • cls L ((n : ℤ) • x) = cls L (((m * n : ℕ) : ℤ) • x) := by
  funext i
  simp only [cls, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem norm_char_le {L : ℕ} [NeZero L] (ψ : DirichletCharacter ℂ L) (a : ZMod L) : ‖ψ a‖ ≤ 1 :=
  ψ.norm_le_one a

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.clsProp :
    UpperTheory.V.Af.Rs.RowRep → UpperTheory.V.Af.Rs.ClsProp := by
  intro hR L _ ψ F G hG
  have hscale : ∀ (a : ZMod L) (v : Fin 2 → ZMod L) (z : ℍ), G (a • v) z = ψ a * G v z := by
    intro a v z
    obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
    rw [← ZMod.natCast_zmod_val a, cls_smul, hG, hG]
    push_cast
    rw [map_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hFc, C, hC⟩
    refine ⟨?_, C, ?_⟩
    · intro v
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      have hγ : Continuous (fun z : ℍ => γ • z) :=
        continuous_const_smul (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      have : (fun z => G (cls L ((n : ℤ) • row γ)) z) = fun z => ψ n * F (γ • z) := by
        funext z; exact hG n γ z
      change Continuous (fun z => G (cls L ((n : ℤ) • row γ)) z)
      rw [this]
      exact continuous_const.mul (hFc.comp hγ)
    · intro v z hz
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG, norm_mul, mul_assoc]
      have h1 := hC γ z hz
      have h0 : 0 ≤ ‖F (γ • z)‖ * z.im ^ 3 := by
        have : 0 < z.im := z.im_pos
        positivity
      exact (mul_le_of_le_one_left h0 (norm_char_le ψ _)).trans h1
  · intro hψ z
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hψ
    let e : (Fin 2 → ZMod L) ≃ (Fin 2 → ZMod L) :=
      { toFun := fun v => (u : ZMod L) • v
        invFun := fun v => ((u⁻¹ : (ZMod L)ˣ) : ZMod L) • v
        left_inv := fun v => by simp [smul_smul]
        right_inv := fun v => by simp [smul_smul] }
    have hs : ∑ v, G v z = ∑ v, G ((u : ZMod L) • v) z :=
      Fintype.sum_equiv e.symm _ _ (fun v => by simp [e, smul_smul])
    have hs2 : ∑ v, G v z = ψ u * ∑ v, G v z := by
      rw [Finset.mul_sum]
      conv_lhs => rw [hs]
      exact Finset.sum_congr rfl (fun v _ => hscale _ v z)
    have hne : (1 : ℂ) - ψ u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have : ((1 : ℂ) - ψ u) * ∑ v, G v z = 0 := by rw [sub_mul, one_mul, ← hs2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  · intro hψ hF0 hFpos
    have hval : ∀ n : ℕ, ψ n = 0 ∨ ψ n = 1 := by
      intro n
      subst hψ
      by_cases h : IsUnit (n : ZMod L)
      · exact Or.inr (MulChar.one_apply h)
      · exact Or.inl (MulChar.map_nonunit _ h)
    refine ⟨?_, ?_⟩
    · intro v z
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG]
      rcases hval n with h | h <;> simp [h, hF0]
    · obtain ⟨z0, hz0⟩ := hFpos
      obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z0
      refine ⟨cls L (((1 : ℕ) : ℤ) • row g⁻¹), g • z0, hg, ?_⟩
      rw [hG, inv_smul_smul]
      subst hψ
      simpa using hz0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.HalfLeIm
open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private theorem half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private theorem norm_G_cls_mul_ker_le_of_mem_fd {L : ℕ} (G : (Fin 2 → ZMod L) → ℍ → ℂ) (C s : ℝ)
    (hC : ∀ (v : Fin 2 → ZMod L) (z : ℍ), 1 / 2 ≤ z.im → ‖G v z‖ * z.im ^ 3 ≤ C)
    (hk : ∀ (x : Fin 2 → ℤ), ∀ z ∈ ModularGroup.fd, ker s x z ≤ 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)))
    (h0 : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ ker s x z) (x : Fin 2 → ℤ) (z : ℍ)
    (hz : z ∈ ModularGroup.fd) :
    ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) := by
  have him := half_le_im hz
  have hw : 0 ≤ ‖x‖ ^ (-(2 * s)) := Real.rpow_nonneg (norm_nonneg _) _
  have hG := hC (cls L x) z him
  have hn : 0 ≤ ‖G (cls L x) z‖ := norm_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 x z)]
  have h2 : ‖G (cls L x) z‖ * z.im ^ 2 ≤ 2 * C := by
    nlinarith [mul_nonneg (mul_nonneg hn (sq_nonneg z.im)) (sub_nonneg.2 him)]
  calc ‖G (cls L x) z‖ * ker s x z
      ≤ ‖G (cls L x) z‖ * (4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s))) :=
        mul_le_mul_of_nonneg_left (hk x z hz) hn
    _ = 4 * (‖G (cls L x) z‖ * z.im ^ 2) * ‖x‖ ^ (-(2 * s)) := by ring
    _ ≤ 4 * (2 * C) * ‖x‖ ^ (-(2 * s)) := by gcongr
    _ = 8 * C * ‖x‖ ^ (-(2 * s)) := by ring

private theorem sum_cls (L : ℕ) [NeZero L] (g : (Fin 2 → ZMod L) → ℂ) (s : ℝ) (z : ℍ)
    (hs : Summable fun x => ker s x z) :
    ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ) = ∑ v, g v * (Zc L v s z : ℂ) := by
  have hc : ∀ v, Summable fun x : Fin 2 → ℤ => if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
    intro v
    have := ((Complex.ofRealCLM.summable hs).mul_left (g v)).indicator {x | cls L x = v}
    refine this.congr (fun x => ?_)
    simp [Set.indicator_apply]
  calc ∑' x : Fin 2 → ℤ, g (cls L x) * (ker s x z : ℂ)
      = ∑' x : Fin 2 → ℤ, ∑ v, if cls L x = v then g v * (ker s x z : ℂ) else 0 := by
        refine tsum_congr (fun x => ?_)
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ v, ∑' x : Fin 2 → ℤ, if cls L x = v then g v * (ker s x z : ℂ) else 0 :=
        Summable.tsum_finsetSum (fun v _ => hc v)
    _ = ∑ v, g v * (Zc L v s z : ℂ) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Zc, Complex.ofReal_tsum, ← tsum_mul_left]
        refine tsum_congr (fun x => ?_)
        split_ifs <;> simp

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.swap :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.Swap := by
  intro hfd hkb hw L _ G hG s hs
  obtain ⟨hGc, C, hC⟩ := hG
  have hs' : s ∈ Icc (1:ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, -, -, -, hkb'⟩ := hkb s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hw.1 (2 * s) (by linarith [hs.1])
  have hbd : ∀ x : Fin 2 → ℤ, ∀ z ∈ ModularGroup.fd,
      ‖G (cls L x) z * (ker s x z : ℂ)‖ ≤ 8 * C * ‖x‖ ^ (-(2 * s)) :=
    fun x z hz => norm_G_cls_mul_ker_le_of_mem_fd G C s hC hkb' hk0 x z hz
  have hint : ∀ x : Fin 2 → ℤ,
      IntegrableOn (fun z => G (cls L x) z * (ker s x z : ℂ)) ModularGroup.fd volume := by
    intro x
    exact Measure.integrableOn_of_bounded hfd.2.ne
      ((hGc _).mul (Complex.continuous_ofReal.comp (hkc x))).aestronglyMeasurable
      ((ae_restrict_iff' hfd.1).2 (Filter.Eventually.of_forall (hbd x)))
  refine ⟨hint, ?_⟩
  have hnorm : Summable fun x : Fin 2 → ℤ =>
      ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun x => integral_nonneg (fun _ => norm_nonneg _))
      (fun x => ?_) ((hsum.mul_left (8 * C)).mul_right (volume.real ModularGroup.fd))
    calc ∫ z in ModularGroup.fd, ‖G (cls L x) z * (ker s x z : ℂ)‖
        ≤ ∫ z in ModularGroup.fd, 8 * C * ‖x‖ ^ (-(2 * s)) :=
          setIntegral_mono_on (hint x).norm (integrableOn_const hfd.2.ne) hfd.1 (hbd x)
      _ = 8 * C * ‖x‖ ^ (-(2 * s)) * volume.real ModularGroup.fd := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
  have h := hasSum_integral_of_summable_integral_norm hint hnorm
  have e : TT L G s = ∫ z in ModularGroup.fd, ∑' x : Fin 2 → ℤ, G (cls L x) z * (ker s x z : ℂ) := by
    unfold TT
    refine setIntegral_congr_fun hfd.1 (fun z hz => ?_)
    have hsz : Summable fun x : Fin 2 → ℤ => ker s x z :=
      Summable.of_nonneg_of_le (fun x => hk0 x z) (fun x => hkb' x z hz) (hsum.mul_left _)
    exact (sum_cls L (fun v => G v z) s z hsz).symm
  rw [e]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Unfold
open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

namespace UpperTheory.V.Af.Rs

private theorem unf_meas_strip : MeasurableSet strip := by
  unfold strip
  exact (measurableSet_le measurable_const UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_lt UpperHalfPlane.continuous_re.measurable measurable_const)

private theorem unf_meas_smul (γ : SL(2, ℤ)) : Measurable (fun z : ℍ => γ • z) := by
  refine Continuous.measurable ?_
  rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff]
  have h : (UpperHalfPlane.coe ∘ fun z : ℍ => γ • z) = fun z : ℍ =>
      (((algebraMap ℤ ℝ (γ 0 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 0 1) : ℂ)) /
      ((algebraMap ℤ ℝ (γ 1 0) : ℂ) * z + (algebraMap ℤ ℝ (γ 1 1) : ℂ))) :=
    funext fun z => UpperHalfPlane.coe_specialLinearGroup_apply γ z
  rw [h]
  refine Continuous.div₀ (by fun_prop) (by fun_prop) fun z => ?_
  have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  simpa [UpperHalfPlane.denom] using this

private theorem unf_countable : Countable SL(2, ℤ) := @Subtype.countable (Matrix (Fin 2) (Fin 2) ℤ) (show Countable (Fin 2 → Fin 2 → ℤ) from inferInstance) _

end UpperTheory.V.Af.Rs

private theorem hasSum_integral_fd_smul_eq_two_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hU : UpperTheory.V.Af.Rs.UnfM) (f : ℍ → E) (hfm : StronglyMeasurable f)
    (hfi : Integrable f volume) :
    HasSum (fun γ : SL(2, ℤ) => ∫ z in ModularGroup.fd, f (γ • z)) ((2 : ℝ) • ∫ z, f z) := by
  have hsum : Integrable f (Measure.sum fun γ : SL(2, ℤ) =>
      Measure.map (fun z => γ • z) (volume.restrict ModularGroup.fd)) := by
    rw [hU, two_smul]
    exact hfi.add_measure hfi
  have h1 := hasSum_integral_measure hsum
  rw [hU, two_smul, integral_add_measure hfi hfi, ← two_smul ℝ] at h1
  convert h1 using 1
  funext γ
  rw [integral_map (UpperTheory.V.Af.Rs.unf_meas_smul γ).aemeasurable hfm.aestronglyMeasurable]

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.unfold :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.UnfM → UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.Unfold := by
  classical
  intro _ hU hR H Φ hH hHi hHΦ hΦ
  haveI := unf_countable
  have hstrip := unf_meas_strip
  set f : ℍ → ℂ := strip.indicator H with hf
  have hfm : StronglyMeasurable f := hH.stronglyMeasurable.indicator hstrip
  have hfi : Integrable f volume := (integrable_indicator_iff hstrip).mpr hHi
  have hA := hasSum_integral_fd_smul_eq_two_integral hU f hfm hfi
  have hB := hasSum_integral_fd_smul_eq_two_integral hU (fun z => ‖f z‖) hfm.norm hfi.norm
  have hval : (2 : ℝ) • ∫ z, f z = 2 * ∫ z in strip, H z := by
    rw [hf, integral_indicator hstrip]
    norm_num
  rw [hval] at hA
  have hfγ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = if γ • z ∈ strip then Φ (row γ) z else 0 := by
    intro γ z
    rw [hf]
    split_ifs with h
    · rw [indicator_of_mem h, hHΦ]
    · rw [indicator_of_notMem h]
  let g : SL(2, ℤ) → Cop := fun γ => ⟨row γ, hR.1 γ⟩
  have hA' := (Equiv.sigmaFiberEquiv g).hasSum_iff.mpr hA
  refine HasSum.sigma hA' fun x => ?_
  have hint : ∀ c : {γ // g γ = x},
      Integrable (fun z => f (c.1 • z)) (volume.restrict ModularGroup.fd) := by
    intro c
    refine Integrable.mono (hΦ x)
      ((hfm.comp_measurable (unf_meas_smul c.1)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    have hrow : row c.1 = x := congrArg Subtype.val c.2
    rw [hfγ]
    split_ifs
    · rw [hrow]
    · simp
  have hsumm : Summable fun c : {γ // g γ = x} => ∫ z in ModularGroup.fd, ‖f (c.1 • z)‖ :=
    hB.summable.comp_injective Subtype.val_injective
  have h := hasSum_integral_of_summable_integral_norm hint hsumm
  have heq : ∀ z, ∑' c : {γ // g γ = x}, f (c.1 • z) = Φ x z := by
    intro z
    obtain ⟨γ0, ⟨h0row, h0s⟩, huniq⟩ := hR.2 z x
    have hg0 : g γ0 = x := Subtype.ext h0row
    rw [tsum_eq_single ⟨γ0, hg0⟩]
    · rw [hfγ, if_pos h0s, h0row]
    · intro c hc
      rw [hfγ, if_neg]
      intro hs
      apply hc
      exact Subtype.ext (huniq c.1 ⟨congrArg Subtype.val c.2, hs⟩)
  simp only [heq] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerLow
noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

theorem kerLow : KerLow := by
  intro s hs x z hz
  obtain ⟨hs1, hs2⟩ := hs
  unfold ker
  have hy : 0 < z.im := z.im_pos
  have hy2 : 3 ≤ 4 * z.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  set r : ℝ := ‖(z : ℂ)‖ with hr
  set n : ℝ := ‖x‖ with hn
  have hr0 : 0 ≤ r := norm_nonneg _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hyr : z.im ≤ r := by
    have := Complex.abs_im_le_norm (z : ℂ)
    simp only [UpperHalfPlane.coe_im] at this
    exact le_trans (le_abs_self _) this
  by_cases hx0 : x = 0
  · subst hx0
    have hn' : n = 0 := by simp [hn]
    have hs0 : -(2 * s) ≠ 0 := by linarith
    rw [hn', Real.zero_rpow hs0, mul_zero]
    exact Real.rpow_nonneg (div_nonneg hy.le (Complex.normSq_nonneg _)) _
  have hxi : ∀ i, |((x i : ℤ) : ℝ)| ≤ n := by
    intro i
    have := norm_le_pi_norm x i
    rwa [Int.norm_eq_abs] at this
  have hn1 : 1 ≤ n := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hi
    exact h1.trans (hxi i)
  set w : ℂ := (x 0 : ℂ) * (z : ℂ) + (x 1 : ℂ) with hw
  have hwle : ‖w‖ ≤ n * (r + 1) := by
    calc ‖w‖ ≤ ‖(x 0 : ℂ)‖ * r + ‖(x 1 : ℂ)‖ := by
          rw [hw]
          exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ n * r + n := by
          rw [Complex.norm_intCast, Complex.norm_intCast]
          have := hxi 0
          have := hxi 1
          nlinarith
      _ = n * (r + 1) := by ring
  have hwne : w ≠ 0 := by
    intro h0
    have him : (w).im = 0 := by rw [h0]; simp
    have hre : (w).re = 0 := by rw [h0]; simp
    simp [hw] at him hre
    rcases him with h | h
    · have h1 : x 1 = 0 := by simpa [h] using hre
      exact hx0 (by ext i; fin_cases i <;> simp [h, h1])
    · exact absurd h hy.ne'
  have hwpos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hwne
  have hnsq : Complex.normSq w ≤ n ^ 2 * (r + 1) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_nonneg w
    nlinarith
  set q : ℝ := z.im / (r + 1) ^ 2 with hq
  have hr1 : 0 < (r + 1) ^ 2 := by positivity
  have hq0 : 0 < q := div_pos hy hr1
  have hq1 : q ≤ 1 := by
    rw [div_le_one hr1]
    nlinarith
  have hbase : q / n ^ 2 ≤ z.im / Complex.normSq w := by
    rw [hq, div_div]
    apply div_le_div_of_nonneg_left hy.le hwpos
    nlinarith
  have hqn0 : 0 ≤ q / n ^ 2 := by positivity
  have hstep : (q / n ^ 2) ^ s ≤ (z.im / Complex.normSq w) ^ s :=
    Real.rpow_le_rpow hqn0 hbase (by linarith)
  have hsplit : (q / n ^ 2) ^ s = q ^ s * n ^ (-(2 * s)) := by
    rw [Real.div_rpow hq0.le (by positivity), div_eq_mul_inv, Real.rpow_neg hn0,
      Real.rpow_mul hn0]
    norm_num
  have hq2 : q ^ (2 : ℝ) ≤ q ^ s := Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hs2
  have hq2' : 1 / 2 / (r + 1) ^ 4 ≤ q ^ (2 : ℝ) := by
    rw [Real.rpow_two, hq, div_pow, ← pow_mul]
    norm_num
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hnpos : 0 ≤ n ^ (-(2 * s)) := Real.rpow_nonneg hn0 _
  calc 1 / 2 / (r + 1) ^ 4 * n ^ (-(2 * s)) ≤ q ^ s * n ^ (-(2 * s)) :=
        mul_le_mul_of_nonneg_right (hq2'.trans hq2) hnpos
    _ = (q / n ^ 2) ^ s := hsplit.symm
    _ ≤ _ := hstep

end UpperTheory.V.Af.Rs
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NsqPos
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private lemma nsq_eq (x : Fin 2 → ℤ) (z : ℍ) :
    Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) =
      ((x 0 : ℝ) * z.re + x 1) ^ 2 + ((x 0 : ℝ) * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

private lemma nsq_pos (x : Fin 2 → ℤ) (hx : x ≠ 0) (z : ℍ) :
    0 < Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have : (x 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    simp only [h0, Int.cast_zero, zero_mul, zero_add]
    positivity
  · have : (x 0 : ℝ) ≠ 0 := by exact_mod_cast h0
    have := z.im_pos.ne'
    positivity

private lemma nsq_low (x : Fin 2 → ℤ) (z : ℍ) (hz : z ∈ ModularGroup.fd) :
    ‖x‖ ^ 2 ≤ 2 * Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) := by
  rw [nsq_eq]
  obtain ⟨hz1, hzre⟩ := hz
  have hN : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have := hz1
    rw [Complex.normSq_apply] at this
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    nlinarith
  set a : ℝ := (x 0 : ℝ)
  set b : ℝ := (x 1 : ℝ)
  have hnorm : ‖x‖ ≤ max |a| |b| := by
    refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg a))).mpr fun i => ?_
    fin_cases i
    · simp [Int.norm_eq_abs, a]
    · simp [Int.norm_eq_abs, b]
  have hM : (max |a| |b|) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total |a| |b| with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_nonneg a]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_nonneg b]
  have hx2 : ‖x‖ ^ 2 ≤ (max |a| |b|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hab : -(|a| * |b|) ≤ 2 * a * b * z.re := by
    have h1 : |2 * a * b * z.re| ≤ |a| * |b| := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have := abs_nonneg a
      have := abs_nonneg b
      nlinarith [mul_nonneg (abs_nonneg a) (abs_nonneg b)]
    exact (abs_le.mp h1).1
  have hsq : a ^ 2 + b ^ 2 ≤ 2 * (a ^ 2 - |a| * |b| + b ^ 2) := by
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
  have hexp : (a * z.re + b) ^ 2 + (a * z.im) ^ 2
      = a ^ 2 * (z.re ^ 2 + z.im ^ 2) + 2 * a * b * z.re + b ^ 2 := by ring
  rw [hexp]
  have : a ^ 2 ≤ a ^ 2 * (z.re ^ 2 + z.im ^ 2) := by
    nlinarith [sq_nonneg a]
  linarith

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.kerBd :
    UpperTheory.V.Af.Rs.KerBd := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := by linarith
  have hzero : ∀ z, ker s 0 z = 0 := by
    intro z
    simp [ker, Real.zero_rpow hs0.ne']
  have hnn : ∀ (x : Fin 2 → ℤ) (z : ℍ), 0 ≤ z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) :=
    fun x z => div_nonneg z.im_pos.le (Complex.normSq_nonneg _)
  refine ⟨?_, ?_, hzero, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · subst hx
      have : ker s 0 = fun _ => 0 := funext hzero
      rw [this]; exact continuous_const
    · unfold ker
      refine Continuous.rpow_const ?_ (fun _ => Or.inr hs0.le)
      refine Continuous.div UpperHalfPlane.continuous_im ?_ (fun z => (nsq_pos x hx z).ne')
      exact Complex.continuous_normSq.comp
        ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const)
  · intro x z
    exact Real.rpow_nonneg (hnn x z) _
  · intro γ z
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
    rfl
  · intro n x z
    have h : Complex.normSq (((((n : ℤ) • x) 0 : ℤ) : ℂ) * z + ((((n : ℤ) • x) 1 : ℤ) : ℂ)) =
        Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) * (n : ℝ) ^ (2 : ℝ) := by
      rw [nsq_eq, nsq_eq]
      simp
      ring
    unfold ker
    rw [h, ← div_div, Real.div_rpow (hnn x z) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg n)]
  · intro x z hz
    by_cases hx : x = 0
    · subst hx
      rw [hzero]
      positivity
    · have hp := nsq_pos x hx z
      have hl := nsq_low x z hz
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy := z.im_pos
      have hy1 : 1 ≤ 2 * z.im := by
        have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
        nlinarith
      have h1 : z.im / Complex.normSq ((x 0 : ℂ) * z + (x 1 : ℂ)) ≤ 2 * z.im / ‖x‖ ^ (2 : ℝ) := by
        rw [Real.rpow_two, div_le_div_iff₀ hp (by positivity)]
        nlinarith
      calc ker s x z ≤ (2 * z.im / ‖x‖ ^ (2 : ℝ)) ^ s := Real.rpow_le_rpow (hnn x z) h1 hs0.le
        _ = (2 * z.im) ^ s * ‖x‖ ^ (-(2 * s)) := by
          rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hn.le,
            Real.rpow_neg hn.le, div_eq_mul_inv]
        _ ≤ (2 * z.im) ^ (2 : ℝ) * ‖x‖ ^ (-(2 * s)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hy1 hs2) (by positivity)
        _ = _ := by rw [Real.rpow_two]; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.IntOnOfBdd
open MeasureTheory Set UpperHalfPlane

private lemma half_le_im {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have := z.im_pos
  nlinarith

private lemma intOn_of_bdd (hF : UpperTheory.V.Af.Rs.FdFin) (φ : ℍ → ℝ) (hc : Continuous φ) (B : ℝ)
    (hB : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ B) : IntegrableOn φ ModularGroup.fd :=
  Measure.integrableOn_of_bounded hF.2.ne hc.aestronglyMeasurable
    ((ae_restrict_iff' hF.1).2 (Filter.Eventually.of_forall hB))

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.tTop :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdPos → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZLow → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TTop := by
  intro hfd hpos hw hzd hzl hzi L _ G hG hre hex M
  obtain ⟨hGc, C', hC'⟩ := hG
  obtain ⟨C, hC⟩ := hzd L
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (Fintype.card (Fin 2 → ZMod L) : ℝ) := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast Fintype.card_pos
  have hNpos : 0 < N := by linarith
  have hcard : ∀ x : ℝ, (Finset.univ : Finset (Fin 2 → ZMod L)).card • x = N * x := by
    intro x
    rw [Finset.card_univ, nsmul_eq_mul, hN]
  obtain ⟨φ, hφ⟩ : ∃ φ : ℍ → ℝ,
      φ = fun z => (∑ v, (G v z).re) / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℍ → ℝ, ψ = fun z => ∑ v, (G v z).re * z.im ^ 3 := ⟨_, rfl⟩
  have hreC : ∀ v, Continuous fun z => (G v z).re := fun v => Complex.continuous_re.comp (hGc v)
  have himC : Continuous fun z : ℍ => z.im := UpperHalfPlane.continuous_im
  have hnC : Continuous fun z : ℍ => ‖(z : ℂ)‖ := continuous_norm.comp UpperHalfPlane.continuous_coe
  have hden : ∀ z : ℍ, 0 < 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := fun z => by positivity
  have hφC : Continuous φ := by
    rw [hφ]
    exact (continuous_finsetSum _ (fun v _ => hreC v)).div
      (continuous_const.mul ((hnC.add continuous_const).pow 4)) (fun z => (hden z).ne')
  have hψC : Continuous ψ := by
    rw [hψ]
    exact continuous_finsetSum _ (fun v _ => (hreC v).mul (himC.pow 3))
  have hGb : ∀ v, ∀ z ∈ ModularGroup.fd,
      0 ≤ (G v z).re * z.im ^ 3 ∧ (G v z).re * z.im ^ 3 ≤ C' := by
    intro v z hz
    have hp : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    refine ⟨mul_nonneg (hre v z) hp, ?_⟩
    exact (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hp).trans (hC' v z (half_le_im hz))
  have hψb : ∀ z ∈ ModularGroup.fd, ‖ψ z‖ ≤ N * C' := by
    intro z hz
    rw [hψ, Real.norm_of_nonneg (Finset.sum_nonneg (fun v _ => (hGb v z hz).1))]
    exact (Finset.sum_le_card_nsmul _ _ _ (fun v _ => (hGb v z hz).2)).trans_eq (hcard _)
  have hφb : ∀ z ∈ ModularGroup.fd, ‖φ z‖ ≤ N * (8 * C') := by
    intro z hz
    have hs0 : 0 ≤ ∑ v, (G v z).re := Finset.sum_nonneg (fun v _ => hre v z)
    have h1 : 1 ≤ 2 * N * (‖(z : ℂ)‖ + 1) ^ 4 := by
      have : 1 ≤ (‖(z : ℂ)‖ + 1) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg (z : ℂ)])
      nlinarith
    rw [hφ, Real.norm_of_nonneg (div_nonneg hs0 (hden z).le)]
    refine (div_le_self hs0 h1).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ _ (fun v _ => ?_)).trans_eq (hcard _)
    have h8 := (hGb v z hz).2
    have h3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) (half_le_im hz) 3) (hre v z)
    norm_num at h3
    linarith
  have hφI := intOn_of_bdd hfd φ hφC _ hφb
  have hψI := intOn_of_bdd hfd ψ hψC _ hψb
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => by
    rw [hφ]
    exact div_nonneg (Finset.sum_nonneg (fun v _ => hre v z)) (hden z).le
  obtain ⟨v0, z0, hz0, hv0⟩ := hex
  have hc : 0 < ∫ z in ModularGroup.fd, φ z := by
    refine hpos φ hφC hφ0 hφI z0 hz0 ?_
    rw [hφ]
    refine div_pos ?_ (hden z0)
    exact lt_of_lt_of_le hv0
      (Finset.single_le_sum (f := fun v => (G v z0).re) (fun v _ => hre v z0) (Finset.mem_univ v0))
  obtain ⟨c, hcd⟩ : ∃ c, c = ∫ z in ModularGroup.fd, φ z := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hψint : ∫ z in ModularGroup.fd, ψ z ≤ N * C' * volume.real ModularGroup.fd :=
    (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hfd.2 hψb)
  obtain ⟨s, hs, hWs⟩ := hw.2 ((M + |C| * (N * C' * volume.real ModularGroup.fd)) / c)
  refine ⟨s, hs, ?_⟩
  have hpt : ∀ z ∈ ModularGroup.fd,
      Wsum s * φ z - |C| * ψ z ≤ (∑ v, G v z * (Zc L v s z : ℂ)).re := by
    intro z hz
    have hlow := hzl L s hs z hz
    have hp3 : 0 ≤ z.im ^ 3 := by
      have := z.im_pos
      positivity
    have hZ : ∀ v, Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3 ≤ Zc L v s z := by
      intro v
      have hsum : ∑ v', Zc L v' s z ≤ N * (Zc L v s z + |C| * z.im ^ 3) := by
        refine (Finset.sum_le_card_nsmul _ _ _ (fun v' _ => ?_)).trans_eq (hcard _)
        have h1 := hC v v' s hs z hz
        have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) hp3
        have h3 := neg_abs_le (Zc L v s z - Zc L v' s z)
        linarith
      have hq : 1 / 2 / (‖(z : ℂ)‖ + 1) ^ 4 * Wsum s =
          N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) := by
        have := hden z
        field_simp
      have h4 : N * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) ≤ N * (Zc L v s z + |C| * z.im ^ 3) :=
        hq ▸ hlow.trans hsum
      have h5 := le_of_mul_le_mul_left h4 hNpos
      linarith
    rw [Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hφ, hψ]
    simp only
    rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have h6 := mul_le_mul_of_nonneg_left (hZ v) (hre v z)
    calc Wsum s * ((G v z).re / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4)) - |C| * ((G v z).re * z.im ^ 3)
        = (G v z).re * (Wsum s / (2 * N * (‖(z : ℂ)‖ + 1) ^ 4) - |C| * z.im ^ 3) := by ring
      _ ≤ (G v z).re * Zc L v s z := h6
  have hfI : IntegrableOn (fun z => ∑ v, G v z * (Zc L v s z : ℂ)) ModularGroup.fd :=
    integrable_finsetSum _ (fun v _ => hzi L G ⟨hGc, C', hC'⟩ s hs v v)
  have hre_eq : (∫ z in ModularGroup.fd, ∑ v, G v z * (Zc L v s z : ℂ)).re =
      ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re := (integral_re hfI).symm
  unfold TT
  rw [hre_eq]
  calc M ≤ Wsum s * c - |C| * (N * C' * volume.real ModularGroup.fd) := by
        have := (div_le_iff₀ hc).1 hWs
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (Wsum s * φ z - |C| * ψ z) := by
        rw [integral_sub (hφI.const_mul _) (hψI.const_mul _), integral_const_mul,
          integral_const_mul, ← hcd]
        have := mul_le_mul_of_nonneg_left hψint (abs_nonneg C)
        linarith
    _ ≤ ∫ z in ModularGroup.fd, (∑ v, G v z * (Zc L v s z : ℂ)).re :=
        setIntegral_mono_on ((hφI.const_mul _).sub (hψI.const_mul _)) hfI.re hfd.1 hpt
end
