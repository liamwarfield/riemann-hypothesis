module

public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem ind_unique :
    ∀ (N N' M : ℕ) [NeZero N] [NeZero N'] (ψ : DirichletCharacter ℂ N) (ψ' : DirichletCharacter ℂ N'), M ≠ 0 →
      ψ.IsPrimitive → ψ'.IsPrimitive → (∀ n : ℕ, n.Coprime M → ψ (n : ZMod N) = ψ' (n : ZMod N')) →
      (⟨N, ψ⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨N', ψ'⟩ := by
  intro N N' M _ _ ψ ψ' hM hψ hψ' h
  have hN : N ≠ 0 := NeZero.ne N
  have hN' : N' ≠ 0 := NeZero.ne N'
  haveI : NeZero (N * N' * M) := ⟨mul_ne_zero (mul_ne_zero hN hN') hM⟩
  haveI : NeZero (N * N') := ⟨mul_ne_zero hN hN'⟩
  haveI : NeZero (N' * N) := ⟨mul_ne_zero hN' hN⟩
  have hL1 : N ∣ N * N' * M := (Nat.dvd_mul_right N N').mul_right M
  have hL2 : N' ∣ N * N' * M := (Nat.dvd_mul_left N' N).mul_right M
  have hLM : M ∣ N * N' * M := Nat.dvd_mul_left M _
  have hA : N * N' ∣ N * N' * M := Nat.dvd_mul_right _ _
  have hB : N' * N ∣ N * N' * M := ⟨M, by ring⟩
  have key : ψ.changeLevel hL1 = ψ'.changeLevel hL2 := by
    ext a
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have hc : ((a : ZMod (N * N' * M)).val).Coprime (N * N' * M) := ZMod.val_coe_unit_coprime a
    rw [← ZMod.natCast_zmod_val (a : ZMod (N * N' * M)), ZMod.cast_natCast hL1,
      ZMod.cast_natCast hL2]
    exact h _ (Nat.Coprime.coprime_dvd_right hLM hc)
  have k1 : ψ.changeLevel (Nat.dvd_mul_right N N') = ψ'.changeLevel (Nat.dvd_mul_left N' N) := by
    apply DirichletCharacter.changeLevel_injective hA
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    exact key
  have k2 : ψ'.changeLevel (Nat.dvd_mul_right N' N) = ψ.changeLevel (Nat.dvd_mul_left N N') := by
    apply DirichletCharacter.changeLevel_injective hB
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    exact key.symm
  have f1 := DirichletCharacter.factorsThrough_gcd ψ ψ' k1
  have f2 := DirichletCharacter.factorsThrough_gcd ψ' ψ k2
  have e1 : ψ.conductor = N := hψ
  have e2 : ψ'.conductor = N' := hψ'
  have c1 : ψ.conductor ≤ N.gcd N' := Nat.sInf_le f1
  have c2 : ψ'.conductor ≤ N'.gcd N := Nat.sInf_le f2
  rw [e1] at c1
  rw [e2] at c2
  have g1 : N.gcd N' = N := le_antisymm (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hN)) c1
  have g2 : N'.gcd N = N' := le_antisymm (Nat.gcd_le_left _ (Nat.pos_of_ne_zero hN')) c2
  have hEq : N = N' := by rw [← g1, Nat.gcd_comm, g2]
  subst hEq
  have : ψ = ψ' := DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right N N) k1
  subst this
  rfl

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.TwistPrim
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem twist_prim :
    ∀ (f q : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f), ξ.IsPrimitive → q.Prime → q ≠ 2 → ¬ q ∣ f →
      ∃ ψ : DirichletCharacter ℂ (f * q), ψ.IsPrimitive ∧ ψ ≠ 1 ∧ ∀ n : ℕ, ψ (n : ZMod (f * q)) = ξ (n : ZMod f) * J q n := by
  intro f q _ ξ hξ hq hq2 hqf
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : q.Coprime f := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqf
  obtain ⟨hp, hne, -⟩ := Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character.2 f ξ q hξ hq2 hcop
  refine ⟨tw ξ q, hp, hne, fun n => ?_⟩
  rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.twist_evaluation_formula f ξ q n]
  rfl

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.realCond
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem conductor_le_of_quadratic_squares {N M : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) (hM : M ∣ N) (hM0 : M ≠ 0)
    (hsq : ∀ t : ℤ, ∃ v : ZMod N, v ^ 2 = 1 + (M : ZMod N) * (t : ZMod N)) : N ≤ M := by
  haveI : NeZero M := ⟨hM0⟩
  have hf : χ.FactorsThrough M := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hM]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod N)
    have h1 : ((a : ℤ) : ZMod M) = ((1 : ℤ) : ZMod M) := by
      have h := congrArg (fun x : (ZMod M)ˣ => (x : ZMod M)) hu
      simp only [ZMod.unitsMap_val, Units.val_one] at h
      rw [← ha, ZMod.cast_intCast hM] at h
      simpa using h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    obtain ⟨t, ht⟩ := h1
    obtain ⟨v, hv⟩ := hsq (-t)
    have ha' : a = 1 + (M : ℤ) * (-t) := by linarith
    have huv : (u : ZMod N) = v ^ 2 := by
      rw [hv, ← ha, ha']; push_cast; ring
    have hvu : IsUnit v := by
      have : IsUnit (v ^ 2) := huv ▸ u.isUnit
      exact (isUnit_pow_iff two_ne_zero).mp this
    ext
    rw [MulChar.coe_toUnitHom, huv, map_pow, ← MulChar.pow_apply' χ two_ne_zero, h2,
      MulChar.one_apply hvu, Units.val_one]
  have hle : χ.conductor ≤ M := Nat.sInf_le hf
  rw [DirichletCharacter.isPrimitive_def] at hp
  omega

private theorem real_cond_odd {N p : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) (hpp : p.Prime) (hodd : p ≠ 2) : ¬ p ^ 2 ∣ N := by
  rintro ⟨k, hk⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hN hk
  obtain ⟨r, hr⟩ := hpp.odd_of_ne_two hodd
  have hle : N ≤ p * k := by
    refine conductor_le_of_quadratic_squares χ hp h2 ⟨p, by rw [hk]; ring⟩ (mul_ne_zero hpp.ne_zero hk0) fun t => ?_
    refine ⟨1 + (p : ZMod N) * k * t * (r + 1), ?_⟩
    have h0 : (p : ZMod N) ^ 2 * k = 0 := by
      have h := congrArg (Nat.cast : ℕ → ZMod N) hk
      rw [ZMod.natCast_self] at h
      push_cast at h
      linear_combination -h
    have hr' : (p : ZMod N) = 2 * r + 1 := by rw [hr]; push_cast; ring
    push_cast
    linear_combination (t + k * t ^ 2 * (r + 1) ^ 2) * h0 - (p : ZMod N) * k * t * hr'
  have h1 := hpp.one_lt
  have : 0 < p * k := Nat.pos_of_ne_zero (mul_ne_zero hpp.ne_zero hk0)
  nlinarith

private theorem real_cond_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) : ¬ 2 ^ 4 ∣ N := by
  rintro ⟨k, hk⟩
  have hN : N ≠ 0 := NeZero.ne N
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hN hk
  have hle : N ≤ 8 * k := by
    refine conductor_le_of_quadratic_squares χ hp h2 ⟨2, by rw [hk]; ring⟩ (mul_ne_zero (by norm_num) hk0) fun t => ?_
    refine ⟨1 + 4 * (k : ZMod N) * t, ?_⟩
    have h0 : (16 : ZMod N) * k = 0 := by
      have h := congrArg (Nat.cast : ℕ → ZMod N) hk
      rw [ZMod.natCast_self] at h
      push_cast at h
      linear_combination -h
    push_cast
    linear_combination (k * t ^ 2) * h0
  omega

theorem real_cond :
    ∀ (N₀ q d : ℕ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ^ 2 = 1 → 8 ∣ N₀ → q.Prime → d.Prime →
      (∀ p : ℕ, p.Prime → p ∣ N → p ∣ N₀ ∨ p = q ∨ p = d) → N ∣ N₀ * q * d := by
  intro N₀ q d N _ χ hp h2 h8 hq hd hall
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hpp hk
  by_cases hp2 : p = 2
  · subst hp2
    have hk3 : k ≤ 3 := by
      by_contra hc
      exact real_cond_two χ hp h2 ((pow_dvd_pow 2 (by omega)).trans hk)
    have : 2 ^ k ∣ 8 := pow_dvd_pow 2 hk3
    exact ((this.trans h8).mul_right q).mul_right d
  · have hk1 : k ≤ 1 := by
      by_contra hc
      exact real_cond_odd χ hp h2 hpp hp2 ((pow_dvd_pow p (by omega)).trans hk)
    interval_cases k
    · simp
    · rw [pow_one] at hk ⊢
      rcases hall p hpp hk with h | rfl | rfl
      · exact (h.mul_right q).mul_right d
      · exact (Dvd.intro_left N₀ rfl).mul_right d
      · exact Dvd.intro_left _ rfl

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem noExc_mono {c c' : ℝ} (h : c' ≤ c) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hc : NoExc c χ) : NoExc c' χ :=
  fun β h1 h2 => hc β (by linarith) h2

private theorem noExc_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ c : ℝ, 0 < c ∧ (χ ≠ 1 → NoExc c χ) := by
  by_cases hχ : χ = 1
  · exact ⟨1, one_pos, fun h => absurd hχ h⟩
  have hcont : Continuous (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
  have h1 : (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hev := hcont.continuousAt.eventually_ne h1
  obtain ⟨c, hc, h⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨c, hc, fun _ β hb1 hb2 => h ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem noExc_level (N : ℕ) [NeZero N] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → NoExc c χ := by
  classical
  choose c hc h using fun χ : DirichletCharacter ℂ N => noExc_one χ
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_min c
  exact ⟨c χ₀, hc χ₀, fun χ hχ => noExc_mono (hχ₀ χ) (h χ hχ)⟩

theorem small_zeros :
    ∀ N₀ : ℕ, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N ≤ N₀ → χ ≠ 1 → NoExc c₀ χ := by
  intro N₀
  induction N₀ with
  | zero =>
    exact ⟨1, one_pos, fun N _ χ hN _ => absurd (Nat.le_zero.1 hN) (NeZero.ne N)⟩
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨c', hc', h'⟩ := noExc_level (n + 1)
    refine ⟨min c c', lt_min hc hc', fun N _ χ hN hχ => ?_⟩
    rcases Nat.lt_or_eq_of_le hN with hlt | heq
    · exact noExc_mono (min_le_left _ _) (h N χ (Nat.lt_succ_iff.1 hlt) hχ)
    · subst heq
      exact noExc_mono (min_le_right _ _) (h' χ hχ)

end QH
end
