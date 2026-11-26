module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConductorAdicCompletion
namespace GlobalTheory.ConductorAdicCompletion

theorem eq_one_of_pow_near_one (z : ℂ) (h : ∀ k : ℕ, ‖z ^ k - 1‖ ≤ 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1

  have hre : ∀ k : ℕ, 1 / 2 ≤ (z ^ k).re := by
    intro k
    have h2 := (Complex.abs_re_le_norm (z ^ k - 1)).trans (h k)
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.mp h2).1
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hsum : ∑ k ∈ Finset.range N, z ^ k = (z ^ N - 1) / (z - 1) := geom_sum_eq hz N
  have hlow : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, z ^ k).re := by
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ k ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hre k
  have hup : (∑ k ∈ Finset.range N, z ^ k).re ≤ 1 / 2 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hsum, norm_div]
    exact div_le_div_of_nonneg_right (h N) (norm_nonneg _)
  have he : 1 / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) / 2 := by ring
  linarith

theorem exists_ball_trivial {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by
  have hmem : {x : K | ‖ψ x - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun x hx => ?_⟩
  have hlt : WithZero.exp (WithZero.log g - 1) < g :=
    (WithZero.lt_log_iff_exp_lt hg0).mp (by omega)
  apply eq_one_of_pow_near_one
  intro k
  rw [← AddChar.map_nsmul_eq_pow]
  have hk : Valued.v (k • x) ≤ WithZero.exp (WithZero.log g - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_le _ ih hx
  have : k • x ∈ {x : K | ‖ψ x - 1‖ < 1 / 2} := by
    apply hγ
    exact (Valuation.restrict_lt_iff_lt_embedding _).mpr (hk.trans_lt hlt)
  exact le_of_lt this

theorem exists_conductor {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    ⟨WithZero.log (Valued.v t₀ : WithZero (Multiplicative ℤ)), fun m hm => by
      have h1 : WithZero.exp m < Valued.v t₀ := lt_of_not_ge fun h => ht₀ (hm _ h)
      exact ((WithZero.lt_log_iff_exp_lt (ne_zero_of_lt h1)).mpr h1).le⟩
    (exists_ball_trivial ψ hc)
  refine ⟨n, fun t => ⟨fun h => ?_, fun h s hs => ?_⟩⟩
  · by_contra hlt
    have h1 : WithZero.exp n < Valued.v t := lt_of_not_ge hlt
    have hv0 : (Valued.v t : WithZero (Multiplicative ℤ)) ≠ 0 := ne_zero_of_lt h1
    have ht : t ≠ 0 := fun h0 => hv0 (by simp [h0])
    have h2 := (WithZero.lt_log_iff_exp_lt hv0).mpr h1
    have h3 := hmax (WithZero.log (Valued.v t : WithZero (Multiplicative ℤ))) (fun x hx => by
      rw [WithZero.exp_log hv0] at hx
      have h4 := h (x / t) (by
        rw [map_div₀]
        exact div_le_one_of_le₀ hx zero_le)
      rwa [mul_div_cancel₀ _ ht] at h4)
    omega
  · apply hn
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans h

theorem exists_conductor_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (ψ : AddChar (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ℂ),
      Continuous (⇑ψ : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → ℂ) →
      (∀ t, ‖ψ t‖ = (1 : ℝ)) → (∃ t, ψ t ≠ (1 : ℂ)) →
      ∃ n : ℤ, ∀ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v,
        (∀ s ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v,
          ψ (t * s) = (1 : ℂ)) ↔
        (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v →
          WithZero (Multiplicative ℤ)) t ≤ WithZero.exp n := by
  intro F _ _ v ψ hc _ hne
  exact exists_conductor ψ hc hne

end GlobalTheory.ConductorAdicCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsTer
namespace GlobalTheory.IterationConvergence

theorem step (w : ℂ) (h : ‖w - 1‖ < 1 / 2) : (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have e2 : w + 1 = 2 - (1 - w) := by ring
  have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
    have := norm_sub_norm_le (2 : ℂ) (1 - w)
    rw [← e2] at this
    have h1 : ‖(1 : ℂ) - w‖ = ‖w - 1‖ := norm_sub_rev _ _
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  rw [e, norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem iter {z : ℂ} (hz : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (z ^ (2 ^ k)) (hz _)
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
      _ ≤ _ := hs

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := iter hz k
  have h2 := hz (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterationConvergence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfNormSubOneLt
namespace GlobalTheory.CharacterConductorBall

private lemma norm_sub_one_le_norm_mul_self_sub_one (w : ℂ) (h : ‖w - 1‖ < 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w * w - 1‖ := by
  have h1 : w * w - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (2 : ℝ) ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have := norm_sub_le (w + 1) (w - 1)
    have e : (w + 1) - (w - 1) = (2 : ℂ) := by ring
    rw [e] at this
    simpa using this
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem eq_one_of_norm_sub_one_lt {A : Type} [AddMonoid A] (ψ : AddChar A ℂ) (B : Set A)
    (hB : ∀ x ∈ B, x + x ∈ B) (hψ : ∀ x ∈ B, ‖ψ x - 1‖ < 1 / 2) : ∀ x ∈ B, ψ x = 1 := by

  have key : ∀ k : ℕ, ∀ x ∈ B, (3 / 2 : ℝ) ^ k * ‖ψ x - 1‖ < 1 / 2 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hψ x hx
    | succ k ih =>
      intro x hx
      have h2 := ih (x + x) (hB x hx)
      have h3 := norm_sub_one_le_norm_mul_self_sub_one (ψ x) (hψ x hx)
      rw [AddChar.map_add_eq_mul] at h2
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖ψ x - 1‖ = (3 / 2) ^ k * (3 / 2 * ‖ψ x - 1‖) := by ring
        _ ≤ (3 / 2) ^ k * ‖ψ x * ψ x - 1‖ := by gcongr
        _ < 1 / 2 := h2
  intro x hx
  by_contra hne
  have hpos : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖ψ x - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have := key k x hx
  rw [div_lt_iff₀ hpos] at hk
  linarith

theorem exists_ball_trivial {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by

  have hnhds : (ψ : K → ℂ) ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hnhds
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc0 : c ≠ 0 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.2 γ.ne_zero)
    rw [map_zero] at this
    exact this.ne'

  have hlt : ∀ y ∈ {y : K | Valued.v y < c}, ψ y = 1 := by
    refine eq_one_of_norm_sub_one_lt ψ _ (fun y hy => ?_) (fun y hy => ?_)
    · exact lt_of_le_of_lt ((Valued.v.map_add y y).trans (max_self _).le) hy
    · apply hγ
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  refine ⟨WithZero.log c - 1, fun x hx => hlt x ?_⟩
  calc Valued.v x ≤ WithZero.exp (WithZero.log c - 1) := hx
    _ < WithZero.exp (WithZero.log c) := WithZero.exp_lt_exp.2 (by omega)
    _ = c := WithZero.exp_log hc0

private lemma addChar_trivial_mul_of_valuation_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) {t t' : K}
    (ht : ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1)
    (hle : Valued.v t' ≤ Valued.v t) :
    ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t' * s) = 1 := by
  intro s hs
  by_cases h0 : t = 0
  · subst h0
    have : t' = 0 := by simpa using hle
    simp [this, AddChar.map_zero_eq_one]
  · have hv : Valued.v t ≠ 0 := by simpa using h0
    have e : t' * s = t * (t' * t⁻¹ * s) := by field_simp
    rw [e]
    apply ht
    rw [map_mul, map_mul, map_inv₀]
    calc Valued.v t' * (Valued.v t)⁻¹ * Valued.v s ≤ Valued.v t * (Valued.v t)⁻¹ * 1 := by
          gcongr
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hv]

theorem exists_conductor {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) (hψ : ∃ t : K, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K,
      (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
        Valued.v t ≤ WithZero.exp n := by
  classical
  obtain ⟨m, hm⟩ := exists_ball_trivial ψ hc
  obtain ⟨t₀, ht₀⟩ := hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; simp [AddChar.map_zero_eq_one] at ht₀
  have hnot : ¬ ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t₀ * s) = 1 :=
    fun h => ht₀ (by simpa using h 1 (by simp))

  have hmem : ∀ t : K, Valued.v t ≤ WithZero.exp m →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1 := by
    intro t ht s hs
    apply hm
    rw [map_mul]
    calc Valued.v t * Valued.v s ≤ WithZero.exp m * 1 := by gcongr
      _ = WithZero.exp m := mul_one _
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (∀ t : K, Valued.v t ≤ WithZero.exp k →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) → k ≤ b := by
    refine ⟨WithZero.log (Valued.v t₀), fun k hk => ?_⟩
    by_contra hlt
    apply hnot
    apply hk
    have hv : Valued.v t₀ ≠ 0 := by simpa using ht₀0
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 (by omega)
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨m, hmem⟩
  refine ⟨n, fun t => ⟨fun hS => ?_, fun ht => hn t ht⟩⟩
  by_contra hgt
  rw [not_le] at hgt
  have hv : Valued.v t ≠ 0 := ne_of_gt (lt_trans WithZero.exp_pos hgt)
  have hj : WithZero.log (Valued.v t) ≤ n := by
    apply hmax
    intro t' ht'
    rw [WithZero.exp_log hv] at ht'
    exact addChar_trivial_mul_of_valuation_le ψ hS ht'
  have : Valued.v t ≤ WithZero.exp n := by
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 hj
  exact absurd hgt (not_lt.2 this)

end GlobalTheory.CharacterConductorBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CharConductor

theorem eq_one_of_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  apply _root_.GlobalTheory.IterationConvergence.main <;> assumption

theorem exists_exponent_of_valued {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption

theorem exists_conductor_exponent : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  exact @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion

end GlobalTheory.CharConductor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExistsStatement
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_char_conductor_exists : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first | exact @GlobalTheory.CharConductor.exists_conductor_exponent | exact GlobalTheory.CharConductor.exists_conductor_exponent | (intros; apply GlobalTheory.CharConductor.exists_conductor_exponent <;> assumption)
end
