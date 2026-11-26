module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AutomorphicArithmetic.CharacterBoxes.PairRows
public import Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
public import Development.AutomorphicArithmetic.MeanSquareBounds.Thin
public import Development.AutomorphicArithmetic.ThickFrames.topsBase
public import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large
public import Development.AutomorphicArithmetic.ShortNorms.MulLogLeRpowEventually
public import Development.AutomorphicArithmetic.ShortNorms.typePrimesN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThickFrames.topsChoiceH
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

private theorem lt_of_classC0' {R : Ranks} (H : Host R) {p : ℕ} {y : ℝ} (hp : p.Prime) (hc : H.cls p = PrimeClass.inertClass)
    (hs : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y → GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1) : y < p := by
  by_contra hle
  push_neg at hle
  have hk := hs p hp hle
  have hc' := hc
  simp only [Host.cls, primeClass] at hc'
  by_cases h2 : p = 2
  · subst h2
    have hmem : 2 ∈ H.toHostRaw.small := by
      rw [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
      refine ⟨Nat.prime_two, ?_, H.QS_pos.ne'⟩
      exact dvd_trans (dvd_pow_self 2 (by omega)) H.tower_dvd
    rw [if_pos hmem] at hc'
    exact absurd hc' (by decide)
  · have hodd : p.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm)
    simp only [GlobalTheoryTheory.kronSym, hodd, pow_zero, Nat.div_one, mul_one] at hk
    split_ifs at hc' <;> simp_all

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsChoiceH :
    ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x0 : ℝ, 0 < Cb ∧ ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x →
      RankVal s R → HostConst s C8 H → (∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H) →
      ∃ TT : Finset R.A, s.delta1 * R.n / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * R.n ∧
        BadOK s Cb { H with TT := TT } ∧ R.toFrame.Shares TT (s.x ^ (-1 + eps)) := by
  intro eps C8 heps heps52
  obtain ⟨Cb, x0, hCb, hT⟩ := topsBase eps (max C8 2) heps heps52
    (le_trans (by norm_num) (le_max_right _ _))
  refine ⟨Cb, x0, hCb, ?_⟩
  intro s R H hse hx hRV hHC hex
  obtain ⟨Y, hPW, hPR⟩ := hex
  obtain ⟨⟨hn1, hn2⟩, _, ⟨hk1, hk2⟩, _⟩ := hRV
  obtain ⟨hJ, ho, hQS⟩ := hHC
  rw [hse] at hn1 hn2 hk1 hk2 hPR
  have hCo1 : C8 ≤ max C8 2 := le_max_left _ _
  have hCo2 : (2 : ℝ) ≤ max C8 2 := le_max_right _ _
  have hx1 : 1 < s.x := s.one_lt_alt
  have hJ1 : 1 ≤ s.J := s.one_le_J
  have hkron := hPR.2.2.2.2.2.2.2.2.2.1
  have hsmall : s.x ^ (eps / (5 * max C8 2)) ≤ Y ^ (eps / 5) := by
    calc s.x ^ (eps / (5 * max C8 2)) = (s.x ^ (1 / max C8 2)) ^ (eps / 5) := by
          rw [← Real.rpow_mul (by linarith)]
          congr 1
          field_simp
      _ ≤ (s.x ^ (1 / s.J)) ^ (eps / 5) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
            (Real.rpow_le_rpow_of_exponent_le hx1.le
              (one_div_le_one_div_of_le (by linarith) (by linarith))) (by positivity)
      _ ≤ Y ^ (eps / 5) := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hPW.1 (by positivity)
  have hC0 : ∀ p : ℕ, p.Prime → (baseOf s 0 0 H).IsResidueClassZero p → s.x ^ (eps / (5 * max C8 2)) < p := by
    intro p hp hc
    exact lt_of_le_of_lt hsmall (lt_of_classC0' H hp hc hkron)
  have hxe : 0 ≤ s.x ^ (2 + 8 * eps) := Real.rpow_nonneg (by linarith) _
  obtain ⟨TT, h1, h2, h3, h4⟩ := hT (baseOf s 0 0 H) (hPH H) hse hx (by
      show s.x ^ (2 + 8 * eps) / 2 ≤ (R.n : ℝ)
      linarith)
    (le_trans hn2 (mul_le_mul_of_nonneg_right hCo2 hxe)) (le_trans ho hCo1) hk2 hC0
  exact ⟨TT, h1, h2, h4, h3⟩
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.GaussSumFunctionEq
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem gauss_sum_function_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    Formalism.HC.An.gChi χ y = G0 χ y := by
  have key : ∀ n ∈ Icc 1 ⌊y⌋₊, max (y / (n : ℝ) - 1) 0 = y / n - 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hy1 : 1 ≤ y := Nat.floor_pos.1 (by omega)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.2 hn.2).trans (Nat.floor_le (by linarith))
    have : 1 ≤ y / n := by rw [le_div_iff₀ (by linarith)]; linarith
    exact max_eq_left (by linarith)
  unfold Formalism.HC.An.gChi G0
  by_cases h : χ = 1
  · simp only [h, if_true]
    congr 1
    unfold Formalism.HC.An.G G1
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]
  · simp only [h, if_false]
    unfold Formalism.HC.An.sumLamChi Gchi
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [key n hn]

private theorem isReal_of_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h2 : χ ^ 2 = 1) (a : ZMod N) :
    (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h := congrArg (fun f : DirichletCharacter ℂ N => f a) h2
    simp only [pow_two, MulChar.one_apply ha] at h
    rw [MulChar.mul_apply] at h
    have hz : χ a = 1 ∨ χ a = -1 := by
      have : (χ a - 1) * (χ a + 1) = 0 := by ring_nf; rw [← pow_two] at h; rw [h]; ring
      rcases mul_eq_zero.1 this with h1 | h1
      · left; linear_combination h1
      · right; linear_combination h1
    rcases hz with hz | hz <;> simp [hz]
  · simp [MulChar.map_nonunit χ ha]

private theorem level_dvd {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : H.IsCharE χ) : N ∣ H.condN := by
  obtain ⟨θ, hθ⟩ := h
  have hp : (Formalism.HC.PChar.mk N χ hθ.1) = H.prim θ := (H.isPrimOf_iff θ (Formalism.HC.PChar.mk N χ hθ.1)).1 hθ
  have hN : N = (H.prim θ).N := congrArg Formalism.HC.PChar.N hp
  rw [hN]
  exact DirichletCharacter.conductor_dvd_level (H.dir θ)

theorem thinH :
    UpperTheory.Top.ThinH := by
  refine ⟨1, one_pos, fun B eps he he52 => ?_⟩
  obtain ⟨c₀s, hc₀s, hsmall⟩ := small_zeros (8 * ⌊B⌋₊)
  have hc₀ : 0 < min c₀s (1 / 400) := lt_min hc₀s (by norm_num)
  obtain ⟨x₀, hx₀⟩ := thin eps 2 1 (min c₀s (1 / 400)) he two_pos one_pos hc₀
  refine ⟨x₀, fun x hx φ H hB hlog hRB => ?_⟩
  intro N _ χ hχ y hy
  rw [gauss_sum_function_eq]
  have hprim : χ.IsPrimitive := by
    obtain ⟨θ, hθ⟩ := hχ
    exact hθ.1
  have hNd : N ∣ H.condN := level_dvd H χ hχ
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlogN : Real.log N ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 :=
    (Real.log_le_log (by exact_mod_cast hNpos)
      (by exact_mod_cast Nat.le_of_dvd H.condN_pos hNd)).trans hlog
  refine hx₀ x hx N χ hprim hlogN ?_ y hy
  intro h2 h1 β hβ hβ1
  have hq : H.q.Prime := H.hyp.1
  have hd : H.d.Prime := H.hyp.2.1
  by_cases hqd : H.q ∣ N ∨ H.d ∣ N
  · exact hRB (Formalism.HC.PChar.mk N χ hprim) hχ (isReal_of_sq χ h2) hqd β
      (by have := min_le_right c₀s (1 / 400); linarith)
  · push_neg at hqd
    have hQ0 : H.QS ≠ 0 := (H.QS_pos).ne'
    have hsplitQ := Nat.ordProj_mul_ordCompl_eq_self H.QS 2
    have hprimes : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) ∨ p = H.q ∨ p = H.d := by
      intro p hp hpN
      have hpc : p ∣ H.QS * H.q * H.d := hpN.trans hNd
      rcases (Nat.Prime.dvd_mul hp).1 hpc with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · left
          by_cases hp2 : p = 2
          · subst hp2
            exact Dvd.dvd.mul_right (by norm_num) _
          · apply Dvd.dvd.mul_left
            rw [← hsplitQ] at h'
            have hcop : Nat.Coprime p (2 ^ H.QS.factorization 2) :=
              Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
            exact hcop.dvd_of_dvd_mul_left h'
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hd).1 h))
    have hdiv := real_cond (8 * (H.QS / 2 ^ H.QS.factorization 2)) H.q H.d N χ hprim h2
      (dvd_mul_right 8 _) hq hd hprimes
    have hcq : Nat.Coprime N H.q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd.1).symm
    have hcd : Nat.Coprime N H.d := ((Nat.Prime.coprime_iff_not_dvd hd).2 hqd.2).symm
    have hN0 : N ∣ 8 * (H.QS / 2 ^ H.QS.factorization 2) :=
      hcq.dvd_of_dvd_mul_right (hcd.dvd_of_dvd_mul_right hdiv)
    have hopos : 0 < H.QS / 2 ^ H.QS.factorization 2 := Nat.ordCompl_pos 2 hQ0
    have hofl : H.QS / 2 ^ H.QS.factorization 2 ≤ ⌊B⌋₊ := Nat.le_floor hB
    have hNle : N ≤ 8 * ⌊B⌋₊ := (Nat.le_of_dvd (by omega) hN0).trans (by omega)
    exact hsmall N χ hNle h1 β (by have := min_le_left c₀s (1 / 400); linarith) hβ1

end QH
end

section -- merged from Development.AutomorphicArithmetic.CharacterBoxes.RealBox
open Formalism.HC UpperTheory.Top

private theorem UpperTheory.Top.realBox_level {φ : Frame} (H : HostRaw φ) (χ : PChar)
    (h : H.IsCharE χ.χ) : χ.N ∣ H.QS * H.q * H.d := by
  obtain ⟨θ, hθ⟩ := h
  rw [H.isPrimOf_iff] at hθ
  subst hθ
  exact DirichletCharacter.conductor_dvd_level _

private theorem UpperTheory.Top.realBox_main (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ)
    (hpr : ∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) (hM : ordCompl[2] H.QS ∣ M) (hg : PairGood M eps Y X H.q H.d)
    (χ : PChar) (hχ : H.IsCharE χ.χ) (hr : χ.IsReal) (hqd : H.q ∣ χ.N ∨ H.d ∣ χ.N) :
    ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
      (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0) := by
  have hP := hg.pair
  have hq := hP.q_prime
  have hd := hP.d_prime
  have hq8 := hP.q_mod
  have hd16 := hP.d_mod
  have hq2 : H.q ≠ 2 := by intro h; rw [h] at hq8; norm_num at hq8
  have hd2 : H.d ≠ 2 := by intro h; rw [h] at hd16; norm_num at hd16
  have hqd' : H.q ≠ H.d := by intro h; rw [h] at hq8; omega
  have hlev := UpperTheory.Top.realBox_level H χ hχ
  obtain ⟨ρ, i, j, hρr, hρN, hN, hval⟩ :=
    realSplit χ H.QS H.q H.d hr H.QS_pos hq hd hq2 hd2 hqd' H.QS_coprime hlev
  have hKdvd : ordCompl[2] H.QS ∣ H.QS := Nat.ordCompl_dvd _ _
  have hK0 : 0 < ordCompl[2] H.QS := Nat.ordCompl_pos 2 H.QS_pos.ne'
  have hnot : ∀ l, l.Prime → l ≠ 2 → l ∣ H.q * H.d → ¬ l ∣ ρ.N := by
    intro l hl hl2 hlqd hlρ
    have h8 := hlρ.trans hρN
    rcases (Nat.Prime.dvd_mul hl).1 h8 with h | h
    · have : l ∣ 2 := hl.dvd_of_dvd_pow (n := 3) (by norm_num; exact h)
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this)
    · have h1 := Nat.dvd_gcd (h.trans hKdvd) hlqd
      rw [H.QS_coprime.gcd_eq_one] at h1
      exact hl.not_dvd_one h1
  have hqρ := hnot _ hq hq2 (dvd_mul_right _ _)
  have hdρ := hnot _ hd hd2 (dvd_mul_left _ _)
  have hcopN : ∀ a : ℕ, a.Coprime (2 * M * H.q * H.d) → a.Coprime χ.N := by
    intro a ha
    refine Nat.coprime_of_dvd fun l hl hla hlN => ?_
    have hl' : l ∣ 2 * M * H.q * H.d := by
      rcases (Nat.Prime.dvd_mul hl).1 (hlN.trans hlev) with h | h
      · rcases (Nat.Prime.dvd_mul hl).1 h with h | h
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (hpr l hl h) _) _
        · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
      · exact Dvd.dvd.mul_left h _
    have h1 := Nat.dvd_gcd hla hl'
    rw [ha.gcd_eq_one] at h1
    exact hl.not_dvd_one h1
  have hind : An.Induces χ.χ (tw ρ.val H.q H.d i j) (2 * M * H.q * H.d) := by
    unfold An.Induces
    exact ⟨χ.prim, fun a ha => hval a (hcopN a ha)⟩
  have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj01 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [show H.q ^ ((0 : Fin 2) : ℕ) = 1 by simp, show H.d ^ ((0 : Fin 2) : ℕ) = 1 by simp,
      mul_one, mul_one] at hN
    rcases hqd with h | h <;> rw [hN] at h
    exacts [hqρ h, hdρ h]
  have hbox := hg.boxes ρ hρr (hρN.trans (mul_dvd_mul_left 8 hM)) i j hij χ.N χ.χ hind
  have hdq : ¬ H.d ∣ H.q := fun h => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).1 h).symm
  have hdqi : ∀ k : ℕ, ¬ H.d ∣ H.q ^ k := fun k h => hdq (hd.dvd_of_dvd_pow h)
  have hjd : (if H.d ∣ χ.N then (1 : Fin 2) else 0) = j := by
    rcases hj01 with rfl | rfl
    · rw [if_neg]
      rw [hN, show H.d ^ ((0 : Fin 2) : ℕ) = 1 by simp, mul_one]
      intro h
      rcases (Nat.Prime.dvd_mul hd).1 h with h | h
      exacts [hdρ h, hdqi _ h]
    · rw [if_pos]
      rw [hN]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by simp)) _
  have hqe : (H.q : ℝ) ≤ Real.exp (Y ^ (eps / 5)) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hq.pos)).1 hP.q_up
  have hde : (H.d : ℝ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hd.pos)).1 hP.d_up
  have hρle : (ρ.N : ℝ) ≤ 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (by norm_num) hK0) hρN
  have hbound : (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y j := by
    have hq1 : (1:ℝ) ≤ H.q := by exact_mod_cast hq.one_lt.le
    have hqi : (H.q:ℝ) ^ (i:ℕ) ≤ Real.exp (Y ^ (eps / 5)) :=
      (pow_le_pow_right₀ hq1 (Nat.lt_succ_iff.1 i.isLt)).trans (by rw [pow_one]; exact hqe)
    have hdj : (H.d:ℝ) ^ (j:ℕ) ≤ Real.exp (Y ^ (eps / 5) * Real.log Y ^ 2) ^ (j:ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hde _
    rw [hN, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
    unfold height
    exact mul_le_mul (mul_le_mul hρle hqi (by positivity) (by positivity)) hdj
      (by positivity) (by positivity)
  rw [hjd]
  exact ⟨hbox, hbound⟩

theorem UpperTheory.Top.realBox :
    ∀ (M : ℕ) (φ : Frame) (H : HostRaw φ) (eps Y X : ℝ), 0 < M → (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * M) → ordCompl[2] H.QS ∣ M →
      PairGood M eps Y X H.q H.d →
      (∀ χ : PChar, H.IsCharE χ.χ → χ.IsReal → (H.q ∣ χ.N ∨ H.d ∣ χ.N) →
        ZeroBox (height M eps Y (if H.d ∣ χ.N then 1 else 0)) χ.χ ∧
          (χ.N : ℝ) ≤ height (ordCompl[2] H.QS) eps Y (if H.d ∣ χ.N then 1 else 0)) ∧ RealBox H := by
  intro M φ H eps Y X _ hpr hM hg
  refine ⟨fun χ hχ hr hqd => UpperTheory.Top.realBox_main M φ H eps Y X hpr hM hg χ hχ hr hqd, ?_⟩
  intro ψ hψ hr hqd β hβ
  have h := (UpperTheory.Top.realBox_main M φ H eps Y X hpr hM hg ψ hψ hr hqd).1
  refine h (β : ℂ) (by simpa using hβ) ?_
  simp only [Complex.ofReal_im, abs_zero]
  unfold height
  positivity
end

section -- merged from Development.AutomorphicArithmetic.ShortNorms.levelData
section -- merged from Development.AutomorphicArithmetic.ShortNorms.ExistsThreePrimesOneModLeRpow
open GlobalTheory.Mem.An

namespace UpperTheory.T3

private theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

theorem exists_three_primes_one_mod_le_rpow :
    SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧
      p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  intro hS
  obtain ⟨A, hA1, hA⟩ := hS
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hAA : A ≤ A * A := by nlinarith
  have hAAA : 0 ≤ A * A * A := by positivity
  refine ⟨(1 + (2 * A + (2 * A + 2) * A)) * A, by nlinarith, ?_⟩
  intro N hN
  have hx : (30 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hx1 : (1 : ℝ) ≤ N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ q : ℕ, q.Prime ∧ q % M = 1 ∧ (q : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hle
    obtain ⟨q, hq, hqm, hqle⟩ := hA M hM
    refine ⟨q, hq, hqm, le_trans hqle ?_⟩
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith)
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 (by omega) (by
    push_cast
    rw [Real.rpow_two]
    nlinarith)
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨p', hp', hp'm, hp'le⟩ := key (p * (15 * N)) (2 * A + 2)
    (by
      have := Nat.mul_le_mul hp.two_le (show 1 ≤ 15 * N by omega)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_two]
      exact mul_le_mul hple (by nlinarith) (by positivity) (by positivity))
  obtain ⟨q0, hq0, hq0m, hq0le⟩ := key (N * (p * p')) (1 + (2 * A + (2 * A + 2) * A))
    (by
      have := Nat.mul_le_mul (show 2 ≤ N by omega) (Nat.mul_pos hp.pos hp'.pos)
      omega)
    (by
      push_cast
      rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hple hp'le (Nat.cast_nonneg _) (by positivity)) hx0.le)
  have hp'p : p' % p = 1 := mod_eq_one_of_mod_mul hp'm hp1
  have hp'15 : p' % (15 * N) = 1 :=
    mod_eq_one_of_mod_mul (K := p) (by rw [Nat.mul_comm]; exact hp'm) (by omega)
  have hq0N : q0 % N = 1 := mod_eq_one_of_mod_mul hq0m (by omega)
  have hq0p : q0 % p = 1 :=
    mod_eq_one_of_mod_mul (K := p' * N) (by rw [show p * (p' * N) = N * (p * p') by ring]; exact hq0m) hp1
  have hq0p' : q0 % p' = 1 :=
    mod_eq_one_of_mod_mul (K := p * N) (by rw [show p' * (p * N) = N * (p * p') by ring]; exact hq0m) hp'.one_lt
  refine ⟨p, p', q0, hp, hp', hq0, ?_, ?_, ?_, hpm, hp'15, hq0N, ?_, ?_, hq0le⟩
  · intro h
    rw [← h, Nat.mod_self] at hp'p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p
    omega
  · intro h
    rw [h, Nat.mod_self] at hq0p'
    omega
  · exact le_trans hple (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))
  · exact le_trans hp'le (Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith))

end UpperTheory.T3
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

private theorem mod_small (C eps : ℝ) (hC : 1 ≤ C) (he : 0 < eps) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, 3 * x ^ (eps / 5) * Real.log x ^ 2 * C < x ^ eps := by
  have hc : 0 < 1 / (4 * C) := by positivity
  have h1 := (isLittleO_log_rpow_atTop (show 0 < eps / 5 by positivity)).bound hc
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨ha, hb⟩ := hx x hxx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _), abs_of_nonneg hl0] at ha
  have hu : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hb (by positivity)
  have he5 : x ^ eps = (x ^ (eps / 5)) ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  rw [he5]
  generalize x ^ (eps / 5) = u at ha hu ⊢
  generalize Real.log x = l at ha hl0 ⊢
  have h2 : 4 * C * l ≤ u := by
    have := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4 * C by positivity)
    rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
  have h3 : l ≤ u := by nlinarith
  have h4 : 4 * C * l * l ≤ u * u := mul_le_mul h2 h3 hl0 (by linarith)
  have h5 : u ^ 3 ≤ u ^ 5 := pow_le_pow_right₀ hu (by norm_num)
  have h6 : 0 < u ^ 3 := by positivity
  have h7 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ u by linarith)
  nlinarith

theorem UpperTheory.T3.levelData :
    UpperTheory.T3.ShortNorm → UpperTheory.T3.SmallOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ,
      ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → UpperTheory.T3.ModAt s.x eps N d →
      ∃ (g : Fin 2 → ℕ) (p p' q0 : ℕ), (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧
          GlobalTheory.Mem.An.NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) ∧
        p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧
        (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 ∧ ∀ i, p ≠ g i ∧ p' ≠ g i := by
  intro hN hS
  obtain ⟨C8, hC, hA⟩ := UpperTheory.T3.exists_three_primes_one_mod_le_rpow hS
  refine ⟨C8, hC, fun eps he he' => ?_⟩
  obtain ⟨x1, h1⟩ := UpperTheory.T3.typePrimesN hN eps he
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := mod_small C8 eps hC he
  refine ⟨max x1 (max x2 x3), fun s R N d hs hx hR hM => ?_⟩
  obtain ⟨hx1, hx23⟩ := max_le_iff.1 hx
  obtain ⟨hx2, hx3⟩ := max_le_iff.1 hx23
  obtain ⟨-, -, hr5, hkr, -⟩ := h2 s R hs hx2 hR
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  obtain ⟨g, hg, hg01, hgd⟩ := h1 s.x hx1 N d R.k R.r hM hk (hk.trans hkr) hr5
  obtain ⟨-, -, hd, hN0, hdN, hlog⟩ := hM
  have hN30 : 30 ≤ N := le_trans (by omega) (Nat.le_of_dvd hN0 hdN)
  obtain ⟨p, p', q0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩ := hA N hN30
  have hb : s.b = Real.exp (s.x ^ eps) := by rw [← hs]; rfl
  rw [hb]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlt : (N : ℝ) ^ C8 < Real.exp (s.x ^ eps) := by
    rw [Real.rpow_def_of_pos hNpos]
    exact Real.exp_lt_exp.2 ((mul_le_mul_of_nonneg_right hlog (by linarith)).trans_lt (h3 s.x hx3))
  have hb1 : 1 ≤ Real.exp (s.x ^ eps) := Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast hk
  have hkb : Real.exp (s.x ^ eps) ≤ (R.k : ℝ) * Real.exp (s.x ^ eps) := le_mul_of_one_le_left (by linarith) hk1
  have hY : Real.exp (s.x ^ eps) ≤ ((R.k : ℝ) * Real.exp (s.x ^ eps)) ^ 8 :=
    hkb.trans (le_self_pow₀ (hb1.trans hkb) (by norm_num))
  refine ⟨g, p, p', q0, hg, hg01, hgd, a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3, fun i => ⟨?_, ?_⟩⟩
  · intro h
    have := (hg i).2.1
    rw [← h] at this
    linarith
  · intro h
    have := (hg i).2.1
    rw [← h] at this
    linarith
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

private theorem hof_quadraticChar_induces (d M : ℕ) [Fact d.Prime] (hd : d % 4 = 3) (hM : M ≠ 1) :
    GlobalTheoryTheory.Induces ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)
      (GlobalTheoryTheory.chDir d) M := by
  have hp : d.Prime := Fact.out
  haveI : NeZero d := ⟨hp.ne_zero⟩
  have hch : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  refine ⟨?_, fun a ha => ?_⟩
  · rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
        ((MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hch))
    · exact h
  · have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; exact absurd (Nat.coprime_zero_left M |>.1 ha) hM
      · exact h
    rw [GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 d a hd ha0,
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simp

private theorem hof_abs_dlogH_le {R : Ranks} (H : Host R) {x eps C : ℝ} (h : QDq x eps C H.q H.d) :
    |dlogH H| ≤ C * Real.log x := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  have hd : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h1 := (h.2.1 H.d _ (hof_quadraticChar_induces H.d (8 * H.q * H.d) (by omega) (by
    rw [mul_assoc]; omega))).2
  exact (Complex.abs_re_le_norm _).trans h1

private theorem hof_log_le_rpow (eps C : ℝ) (he : 0 < eps) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_atTop he).bound (inv_pos.2 hC)
  obtain ⟨x0, h0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max x0 1, fun x hx => ?_⟩
  have h1 := h0 x (le_of_max_le_left hx)
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (by positivity)] at h1
  calc C * Real.log x ≤ C * (C⁻¹ * x ^ eps) := by gcongr
    _ = x ^ eps := by field_simp

private theorem hof_Lwv_le (s : Scale) (hy : 1 ≤ Real.log s.x) :
    (Lwv s : ℝ) ≤ (4084 + 60 / s.eps) * Real.log s.x := by
  have he := s.eps_pos
  have h1 : (⌈(405 : ℝ) * Real.log s.x⌉₊ : ℝ) < 405 * Real.log s.x + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have h2 : (⌈30 / s.eps⌉₊ : ℝ) < 30 / s.eps + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : 60 / s.eps = 2 * (30 / s.eps) := by ring
  have h4 : 0 < 30 / s.eps := by positivity
  unfold Lwv
  push_cast
  rw [h3]
  nlinarith [mul_nonneg h4.le (sub_nonneg.mpr hy)]

private theorem hof_thick :
    ∃ CT2 : ℝ, ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x →
      RankVal s R → (R.o : ℝ) ≤ Co → ∃ T : Finset ℕ, (∀ a ∈ T, 4 * Lwv s * a < R.n0) ∧ Formalism.FrobeniusOrbits.NoRel T (Lwv s) ∧
        (R.n0 : ℝ) * Real.exp (-(CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log (Lwv s)))) / (Lwv s) ≤ T.card ∧
        s.x ^ (-s.eps) * R.n ≤ (T.card : ℝ) ∧ 4 * Lwv s * T.card ≤ R.n0 ∧ 2 ≤ Lwv s := by
  obtain ⟨C, -, hT⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2
  refine ⟨C, fun eps Co he he' => ?_⟩
  obtain ⟨x0, hT⟩ := hT eps (max Co 2) (4084 + 60 / eps) he he'
  refine ⟨max x0 (Real.exp 1), fun s R hs hx hR ho => ?_⟩
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hy1 : 1 ≤ Real.log s.x := (Real.le_log_iff_exp_le hx0).mpr ((le_max_right _ _).trans hx)
  have hL : 2 ≤ Lwv s := by unfold Lwv; omega
  have hLK := hof_Lwv_le s hy1
  have hn1 := hR.n_lo
  have hn2 := hR.n_up
  rw [hs] at hLK hn1 hn2
  have hp0 : 0 < s.x ^ (2 + 8 * eps) := Real.rpow_pos_of_pos hx0 _
  have hlo : s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps / 2 ≤ (R.n : ℝ) := by
    unfold UpperTheory.BernoulliSumsFrobeniusOrbits.hE
    linarith
  have hup : (R.n : ℝ) ≤ max Co 2 * s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps :=
    hn2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp0.le)
  obtain ⟨T, t1, t2, t3, t4, t5⟩ := hT s.x ((le_max_left _ _).trans hx) R.toFrame (Lwv s) hL hLK
    (ho.trans (le_max_left _ _)) hlo hup
  exact ⟨T, t1, t2, t3, hs ▸ t4, t5, hL⟩

private theorem hof_exists_host (R : Ranks) (H0 : HostAx R.toFrame) (hA : admitted R H0) (b : ℕ) (hF : FieldRows H0.toHostRaw b)
    (hbig : 4 * R.t * R.r + 1 < H0.q ∧ 4 * R.t * R.r + 1 < H0.d)
    (g : Fin 2 → ℕ) (p p' q0 : ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hp : p.Prime) (hp' : p'.Prime)
    (hpp : p ≠ p') (hm : p % 15 = 1 ∧ p' % 15 = 1) (hpg : ∀ i, p ≠ g i ∧ p' ≠ g i)
    (T : Finset ℕ) (Lw : ℕ) (hL : 2 ≤ Lw) (hT : ∀ a ∈ T, 4 * Lw * a < R.n0) (hT' : Formalism.FrobeniusOrbits.NoRel T Lw) (CT2 : ℝ)
    (hS : ∀ l ∈ ({g 0, g 1, p, p', q0} : Finset ℕ), Nat.Coprime l H0.QS) :
    ∃ H : Host R, H.toHostAx = H0 ∧ H.splitBound = b ∧ H.g = g ∧ H.pde = p ∧ H.pde' = p' ∧
      H.levelPrimes = {g 0, g 1, p, p', q0} ∧ H.ccK = ⊤ ∧ H.T2 = T ∧ H.Lw = Lw ∧ H.CT2 = CT2 := by
  obtain ⟨D, rfl, h2, h3⟩ := hA b
    { levelPrimes := {g 0, g 1, p, p', q0}, g := g, g_prime := hg, g_ne := hne
      g_level := by intro i; fin_cases i <;> simp
      pde := p, pde' := p', pde_prime := hp, pde'_prime := hp', pde_ne := hpp, pde_level := by simp
      pde_mod := hm, pde_ne_g := hpg, ccK := ⊤, ccK_ne_bot := top_ne_bot
      ccK_primitive := fun m hm h => by
        have h1 := congrArg Ideal.absNorm (top_le_iff.1 h)
        rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top, NumberField.RingOfIntegers.rank, H0.toHostRaw.finrank_K] at h1
        nlinarith
      ccK_split := fun P hP h => absurd (top_le_iff.1 h) hP.ne_top, ccK_coprime := by simp, ccK_coprimeS := by simp
      level_coprimeS := hS
      TT := ∅, T2 := T, u0 := 0, Lw := Lw, two_le_Lw := hL, second_set_range := hT, second_set_no_relation := hT', CT2 := CT2 } hF hbig
  have e := eq_of_heq h3
  exact ⟨D, rfl, h2, congrArg Choices.g e, congrArg Choices.pde e, congrArg Choices.pde' e, congrArg Choices.levelPrimes e,
    congrArg Choices.ccK e, congrArg Choices.T2 e, congrArg Choices.Lw e, congrArg Choices.CT2 e⟩

private theorem hof_coprime {l Q q d : ℕ} (h : l % (Q * q * d) = 1) : Nat.Coprime l Q := by
  have h1 : Nat.Coprime l (Q * q * d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact h1.coprime_mul_right_right.coprime_mul_right_right

private theorem hof_odd {Q k M : ℕ} (hQ : Q ≠ 0) (h : Q ∣ Nat.lcm (2 ^ k) M) :
    (∀ l : ℕ, l.Prime → l ∣ Q → l ∣ 2 * M) ∧ ordCompl[2] Q ∣ M := by
  have h' := h.trans (Nat.lcm_dvd_mul _ _)
  refine ⟨fun l hl hd => ?_, ?_⟩
  · rcases hl.dvd_mul.1 (hd.trans h') with h1 | h1
    · exact (hl.dvd_of_dvd_pow h1).mul_right _
    · exact h1.mul_left _
  · exact ((Nat.coprime_ordCompl Nat.prime_two hQ).symm.pow_right k).dvd_of_dvd_mul_left ((Nat.ordCompl_dvd _ _).trans h')

private theorem hof_box {R : Ranks} (H : Host R) {M : ℕ} {eps Y X : ℝ} (hM : 0 < M) (hQ : H.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M)
    (hG : PairGood M eps Y X H.q H.d) : BoxH H Y eps ∧ UpperTheory.Top.RealBox H.toHostRaw := by
  obtain ⟨h1, h2⟩ := hof_odd H.QS_pos.ne' hQ
  obtain ⟨a, b⟩ := UpperTheory.Top.realBox M R.toFrame H.toHostRaw eps Y X hM h1 h2 hG
  refine ⟨fun N _ χ hχ hr => ?_, b⟩
  have hle : ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM h2
  have hmono : ∀ j, height (ordCompl[2] H.QS) eps Y j ≤ height M eps Y j := fun j => by
    unfold height
    gcongr
  have key := a ⟨N, χ, hχ.1⟩ ((isCharH_iff H χ).1 hχ) hr
  refine ⟨fun hd => ?_, fun hq hd => ?_⟩
  · obtain ⟨k1, k2⟩ := key (Or.inr hd)
    rw [if_pos hd] at k1 k2
    have e : 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps = height (ordCompl[2] H.QS) eps Y 1 := by
      simp [height, GlobalTheoryTheory.X1, GlobalTheoryTheory.X2]
    rw [e]
    exact ⟨hχ.1, hr, k2, fun z z1 z2 => k1 z z1 (z2.trans (hmono _))⟩
  · obtain ⟨k1, k2⟩ := key (Or.inl hq)
    rw [if_neg hd] at k1 k2
    have e : 8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps = height (ordCompl[2] H.QS) eps Y 0 := by
      simp [height, GlobalTheoryTheory.X1]
    rw [e]
    exact ⟨hχ.1, hr, k2, fun z z1 z2 => k1 z z1 (z2.trans (hmono _))⟩

theorem UpperTheory.T3.hostOfFieldOf :
    UpperTheory.T3.ShortNorm → UpperTheory.T3.SmallOne → ∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
      ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
        s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
        PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
        ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
          R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps)) := by
  intro hSN hSO eps C0 he he' hC0
  obtain ⟨C1, hC1, hL⟩ := UpperTheory.T3.levelData hSN hSO
  obtain ⟨xa, hL⟩ := hL eps he he'
  obtain ⟨c6, hc6, hThin⟩ := QH.thinH
  obtain ⟨xb, hThin⟩ := hThin C0 eps he he'
  obtain ⟨Cb, xc, hCb, hTops⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.topsChoiceH eps C0 he he'
  obtain ⟨xd, hP⟩ := UpperTheory.Top.pairRows eps C0 he he'
  obtain ⟨CT2, hT⟩ := hof_thick
  obtain ⟨xe, hT⟩ := hT eps C0 he he'
  obtain ⟨xf, hlog⟩ := hof_log_le_rpow eps 4 he (by norm_num)
  obtain ⟨xg, hbig⟩ := UpperTheory.T3.qdBig eps C0 he he'
  refine ⟨CT2, max C0 C1, c6, Cb, max (max (max xa xb) (max xc xd)) (max (max xe xf) xg), le_max_left _ _, hc6, hCb,
    fun s R H0 M Y hs hx hR hJ ho hQS hM hMC hQ hW hG hF hA => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, ⟨hxe, hf⟩, hg⟩ := hx
  subst hs
  obtain ⟨hqd, h100⟩ := hbig s R Y H0.q H0.d rfl hg hR hJ hW hG.pair
  have hN : Real.log ((H0.QS : ℝ) * H0.q * H0.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    obtain ⟨c⟩ := nonempty_choices H0.toHostRaw
    obtain ⟨D0, h0, -⟩ := hA _ c hF hqd
    clear c
    subst h0
    have h1 := (hP s R D0 M Y rfl hd hR ⟨hJ, ho, hQS⟩ hM hW hG).1.2.2.2.2.2.2.2.2.2.2
    have h2 := hW.z_log_sq_le
    linarith
  have hN0 : 0 < H0.QS * H0.q * H0.d := Nat.mul_pos (Nat.mul_pos H0.QS_pos hG.pair.q_prime.pos) hG.pair.d_prime.pos
  have hN1 : 1 < H0.QS * H0.q * H0.d := lt_of_lt_of_le (by omega) (Nat.le_of_dvd hN0 (dvd_mul_left H0.d _))
  have hd4 : H0.d % 4 = 3 := by have := hG.pair.d_mod; omega
  obtain ⟨g, p, p', q0, hgi, hg01, hdisj, hp, hp', hq0, hpp, hq0p, hq0p', mp, mp', mq0, lp, lp', lq0, hpg⟩ :=
    hL s R (H0.QS * H0.q * H0.d) H0.d rfl ha hR ⟨hG.pair.d_prime, hd4, h100, hN0, dvd_mul_left _ _, by
      have h1 : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by have := s.one_lt_alt; positivity
      push_cast
      linarith⟩
  have hm : ((H0.QS * H0.q * H0.d : ℕ) : ℝ) ^ C1 ≤ ((H0.QS : ℝ) * H0.q * H0.d) ^ max C0 C1 := by
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN0) (le_max_right _ _)
  replace lp := lp.trans hm
  replace lp' := lp'.trans hm
  replace lq0 := lq0.trans hm
  replace mp := mod_lcm_of_mod_mul hN0 mp
  replace mp' := mod_lcm_of_mod_mul hN0 mp'
  obtain ⟨T, t1, t2, t3, t4, t5, t6⟩ := hT s R rfl hxe hR ho
  have hgm : ∀ i, g i % (H0.QS * H0.q * H0.d) = 1 := fun i =>
    Eq.trans (GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd _ _ _ hd4 (hgi i).2.2.2).1 (Nat.mod_eq_of_lt hN1)
  obtain ⟨D, e1, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hof_exists_host R H0 hA _ hF hqd g p p' q0 (fun i => (hgi i).1) hg01
    hp hp' hpp ⟨(mod_of_mod_lcm hN1 mp).1, (mod_of_mod_lcm hN1 mp').1⟩ hpg T (Lwv s) t6 t1 t2 CT2 (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl | rfl | rfl
      exacts [hof_coprime (hgm 0), hof_coprime (hgm 1), hof_coprime (mod_of_mod_lcm hN1 mp).2,
        hof_coprime (mod_of_mod_lcm hN1 mp').2, hof_coprime mq0])
  subst e1 e4 e5 e6 e9 e11
  obtain ⟨hrow, hq, hbox, -⟩ := hP s R D M Y rfl hd hR ⟨hJ, ho, hQS⟩ hM hW hG
  obtain ⟨TT, tt1, tt2, hbad, hsh⟩ := hTops s R D rfl hc hR ⟨hJ, ho, hQS⟩ ⟨Y, hW, hrow⟩
  have hnorm := fun i => (GlobalTheory.Mem.An.normOne_iff_host R D _ _).1 (hgi i).2.2.2
  have hsplit := GlobalTheory.HostSplit.split_of_one_mod R D
  obtain ⟨bH, bR⟩ := hof_box { D with TT := TT } hM hQ hG
  have hC : C0 ≤ max C0 C1 := le_max_left _ _
  refine ⟨{ D with TT := TT }, q0, rfl, rfl, ⟨
    ⟨⟨Y, hW, hrow⟩, ⟨tt1, tt2⟩, t4, ⟨lp, lp'⟩, fun i => ⟨(hgi i).2.1, (hgi i).2.2.1⟩, e10, e8, ?_,
      hJ.trans hC, ho.trans hC, hQS.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))⟩,
    ⟨fun i => ?_, hgm, ⟨?_, ?_⟩, fun l hl => ?_⟩, ?_, ?_, hq, ⟨Y, hW, hrow, hbox, bH⟩, ?_, ?_, hbad, hdisj,
    hnorm, ⟨mp, mp'⟩, ⟨hq0, mq0, lq0, hq0p, hq0p'⟩, e7⟩, hsh⟩
  · exact (Nat.floor_le_floor (hW.rpow_ez_le (by norm_num))).trans e3.ge
  · obtain ⟨π, h1, h2, -⟩ := hnorm i
    exact ⟨π, h1, h2⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver D.E hp).symm.trans (hsplit _ hp (mod_of_mod_lcm hN1 mp).2).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver D.E hp').symm.trans (hsplit _ hp' (mod_of_mod_lcm hN1 mp').2).1
  · have hl' : l ∈ D.levelPrimes := hl
    rw [e7] at hl'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl | rfl | rfl | rfl
    · exact (hsplit _ (hgi 0).1 (hgm 0)).2
    · exact (hsplit _ (hgi 1).1 (hgm 1)).2
    · exact (hsplit _ hp (mod_of_mod_lcm hN1 mp).2).2
    · exact (hsplit _ hp' (mod_of_mod_lcm hN1 mp').2).2
    · exact (hsplit _ hq0 mq0).2
  · rw [← e10] at t3
    exact t3
  · rw [← e10] at t5
    exact t5
  · exact (hof_abs_dlogH_le { D with TT := TT } hq).trans (hlog s.x hf)
  · refine (thinScales_iff_hostBound s c6 _).2 (hThin s.x hb R.toFrame D.toHostRaw ?_ ?_ bR)
    · have h1 : ((ordCompl[2] D.QS : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hM (hof_odd D.QS_pos.ne' hQ).2
      exact h1.trans hMC
    · have h1 : (D.condN : ℝ) = (D.QS : ℝ) * D.q * D.d := by
        rw [show D.condN = D.QS * D.q * D.d from rfl]
        push_cast
        rfl
      rw [h1]
      exact hN
