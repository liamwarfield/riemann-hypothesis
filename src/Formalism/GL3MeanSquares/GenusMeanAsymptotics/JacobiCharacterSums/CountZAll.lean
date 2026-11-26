module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll

@[expose] public section

section -- merged from Formalism.LFunctionBounds.LFunctionBoundsProofs.DivisorBound
namespace Formalism.FX

open Finset

theorem succ_le_max_mul_exp (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / a) * Real.exp (a * k) := by
  have hM1 : (1 : ℝ) ≤ max 1 (1 / a) := le_max_left _ _
  have hMa : 1 ≤ max 1 (1 / a) * a := by
    calc (1 : ℝ) = (1 / a) * a := by field_simp
      _ ≤ max 1 (1 / a) * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc ((k : ℝ) + 1) ≤ max 1 (1 / a) * (1 + a * k) := by nlinarith
    _ ≤ max 1 (1 / a) * Real.exp (a * k) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a * k)]) (by linarith)

theorem succ_le_max_mul_pow (e : ℝ) (he : 0 < e) (p k : ℕ) (hp : 2 ≤ p) :
    ((k : ℝ) + 1) ≤ max 1 (1 / (e * Real.log 2)) * ((p : ℝ) ^ e) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have ha : 0 < e * Real.log 2 := mul_pos he (Real.log_pos (by norm_num))
  refine (succ_le_max_mul_exp _ ha k).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (le_max_left _ _))
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc e * Real.log 2 * k ≤ e * Real.log p * k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog he.le) hk
    _ = k * (Real.log p * e) := by ring

theorem succ_le_pow_of_two_le (e : ℝ) (p k : ℕ) (hp : 2 ≤ (p : ℝ) ^ e) :
    ((k : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ k := by
  have hx : (0 : ℝ) ≤ (p : ℝ) ^ e := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : ((k : ℝ) + 1) * 2 ≤ ((p : ℝ) ^ e) ^ k * (p : ℝ) ^ e :=
      mul_le_mul ih hp (by norm_num) (by positivity)
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    push_cast
    linarith

theorem rpow_eq_prod_primeFactors (e : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (n : ℝ) ^ e = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hx : (0 : ℝ) ≤ p := p.cast_nonneg
  rw [← Real.rpow_natCast (p : ℝ) (n.factorization p), ← Real.rpow_mul hx,
    mul_comm ((n.factorization p : ℕ) : ℝ) e, Real.rpow_mul hx, Real.rpow_natCast]

theorem divisor_weight_bound : DivisorBound := by
  intro e he
  set M := max 1 (1 / (e * Real.log 2)) with hM
  set K := ⌈(2 : ℝ) ^ (1 / e)⌉₊ with hK
  refine ⟨M ^ K, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hcard : ((n.divisors.card : ℕ) : ℝ) =
      ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    norm_cast
  rw [hcard, rpow_eq_prod_primeFactors e hn0]
  have hfac : ∀ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) ≤
      (if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with hpK
    · exact succ_le_max_mul_pow e he p _ hp2
    · rw [one_mul]
      apply succ_le_pow_of_two_le
      have h1 : (2 : ℝ) ^ (1 / e) ≤ p :=
        (Nat.le_ceil _).trans (by exact_mod_cast (not_lt.mp hpK))
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / e)) ^ e := by
            rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ e := Real.rpow_le_rpow (by positivity) h1 he.le
  calc ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, ((if p < K then M else 1) * ((p : ℝ) ^ e) ^ (n.factorization p)) :=
        Finset.prod_le_prod₀ (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p < K then M else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ M ^ K * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        apply pow_le_pow_right₀ hM1
        calc (n.primeFactors.filter (fun p => p < K)).card ≤ (Finset.range K).card :=
              Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          _ = K := Finset.card_range K

end Formalism.FX
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZFinal
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem final_bound_of_assembly : FinalOf := by
  rintro ⟨C, hC0, hC⟩ hDet hBC hNum
  obtain ⟨Q₀, C', hQ₀, hN⟩ := hNum C hC0
  classical

  let F : Finset PC := (range ⌈Q₀⌉₊).sigma (fun N => @Finset.univ (DirichletCharacter ℂ (N + 1)) (Fintype.ofFinite _))
  refine ⟨max C' ((F.card : ℝ) + 1), fun Q S hQ hS => ?_⟩
  have hQ14 : (1 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hQ14' : (0 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by linarith
  rcases lt_or_ge Q Q₀ with hQQ | hQQ
  ·
    have hsub : S ⊆ F := by
      intro p hp
      obtain ⟨-, hpQ, -⟩ := hS p hp
      simp only [F, mem_sigma, mem_range, mem_univ, and_true]
      have h1 : ((p.1 : ℕ) : ℝ) < Q₀ := by push_cast at hpQ; linarith
      have h2 : (Q₀ : ℝ) ≤ (⌈Q₀⌉₊ : ℝ) := Nat.le_ceil Q₀
      exact_mod_cast h1.trans_le h2
    have hc : (S.card : ℝ) ≤ F.card := by exact_mod_cast card_le_card hsub
    calc (S.card : ℝ) ≤ (F.card : ℝ) + 1 := by linarith
      _ ≤ max C' ((F.card : ℝ) + 1) := le_max_right _ _
      _ = max C' ((F.card : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hQ14 (le_trans (by positivity) (le_max_right _ _))
  ·
    obtain ⟨hsm, hfin⟩ := hN Q hQQ
    have hQ20 : (20 : ℝ) ≤ Q := le_trans hQ₀ hQQ
    set J := pJ Q with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; unfold pJ; omega
    have hY1 : 1 ≤ pY Q := by
      unfold pY
      have : 1 ≤ q0 Q := by unfold q0; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      exact Nat.one_le_pow _ _ (by omega)

    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun p : PC => p.1 = 0)
    set S' := S.filter (fun p : PC => ¬ p.1 = 0) with hS'
    have h0 : (S.filter (fun p : PC => p.1 = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      obtain ⟨Na, χa⟩ := a
      obtain ⟨Nb, χb⟩ := b
      simp only [mem_filter] at ha hb
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨-, rfl⟩ := hb
      have e1 : χa = 1 := DirichletCharacter.level_one' _ rfl
      have e2 : χb = 1 := DirichletCharacter.level_one' _ rfl
      rw [e1, e2]

    let ρ : PC → ℂ := fun p => if h : (∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧
        DirichletCharacter.LFunction p.2 s = 0) then h.choose else 0
    have hρ : ∀ p ∈ S, 1 - 1 / 400 < (ρ p).re ∧ |(ρ p).im| ≤ Q ∧ DirichletCharacter.LFunction p.2 (ρ p) = 0 := by
      intro p hp
      have h := (hS p hp).2.2
      simp only [ρ, dif_pos h]
      exact h.choose_spec
    let jf : PC → ℕ := fun p => if h : (∃ j ∈ range J, 1 / (2 * (J : ℝ)) ≤
        ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p (ρ p)‖) then h.choose else 0
    have hne1 : ∀ p ∈ S', p.2 ≠ 1 := by
      intro p hp h
      simp only [hS', mem_filter] at hp
      have hc : p.2.conductor = p.1 + 1 := (hS p hp.1).1
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    have hjf : ∀ p ∈ S', jf p ∈ range J ∧
        1 / (2 * (J : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ (jf p)) p (ρ p)‖ := by
      intro p hp
      have hpS : p ∈ S := (mem_filter.1 hp).1
      have hp0 : p.1 ≠ 0 := (mem_filter.1 hp).2
      obtain ⟨hprim, hlev, -⟩ := hS p hpS
      obtain ⟨h1, h2, h3⟩ := hρ p hpS
      have h := hDet Q hQ20 p hprim hp0 hlev (ρ p) (by unfold s0; exact h1) h2 h3
      rw [← hJdef] at h
      simp only [jf, dif_pos h]
      exact h.choose_spec
    have hre1 : ∀ p ∈ S', (ρ p).re < 1 := by
      intro p hp
      by_contra hc
      push Not at hc
      have hpS : p ∈ S := (mem_filter.1 hp).1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 (Or.inl (hne1 p hp)) hc (hρ p hpS).2.2

    have hfib := Finset.card_eq_sum_card_fiberwise (f := jf) (s := S') (t := range J) (fun p hp => (hjf p hp).1)
    set K : ℕ := pY Q * 2 ^ J with hK
    have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hblock : ∀ j ∈ range J, ((S'.filter (fun p => jf p = j)).card : ℝ) ≤
        8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ) := by
      intro j hj
      have hU : 1 ≤ pY Q * 2 ^ j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
      have h := hBC C hC0 hC Q (by linarith) (pY Q) (pN Q) (pY Q * 2 ^ j) J hU hJ1 (hsm j hj)
        (S'.filter (fun p => jf p = j)) ρ (by
          intro p hp
          obtain ⟨hpS', hpj⟩ := mem_filter.1 hp
          have hpS : p ∈ S := (mem_filter.1 hpS').1
          obtain ⟨hprim, hlev, -⟩ := hS p hpS
          obtain ⟨h1, h2, -⟩ := hρ p hpS
          refine ⟨hprim, hlev, by unfold s0; exact h1, hre1 p hpS', h2, ?_⟩
          have := (hjf p hpS').2
          rw [hpj] at this
          exact this)
      refine h.trans ?_
      have hUK : ((pY Q * 2 ^ j : ℕ) : ℝ) ≤ K := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hj).le
        exact_mod_cast Nat.mul_le_mul_left _ this
      have hrp : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (K : ℝ) ^ (3 / 200 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hUK (by norm_num)
      have : (0 : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C := by positivity
      exact mul_le_mul_of_nonneg_left hrp this
    have hS'card : (S'.card : ℝ) ≤ (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      rw [hfib]; push_cast
      refine (sum_le_sum hblock).trans ?_
      rw [sum_const, card_range, nsmul_eq_mul]
    have htot : (S.card : ℝ) ≤ 1 + (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      have : (S.card : ℝ) = (S.filter (fun p : PC => p.1 = 0)).card + S'.card := by
        rw [← hcard]; push_cast; ring
      rw [this]
      have : ((S.filter (fun p : PC => p.1 = 0)).card : ℝ) ≤ 1 := by exact_mod_cast h0
      linarith
    calc (S.card : ℝ) ≤ C' * Q ^ (1 / 4 : ℝ) := htot.trans hfin
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hQ14'

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZBlock
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma norm_cpow_neg_le_one' {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
  simp only [Complex.neg_re]
  linarith

lemma conj_natCast_cpow_neg (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [show -(starRingEnd ℂ) z = (starRingEnd ℂ) (-z) from (map_neg _ _).symm,
    Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem blockCountOf_statement : BlockCountOf := by
  intro hDual hPair C hC hL Q hQ Y N U J hU hJ hsmall T ρ hT
  have hU0 : (0 : ℝ) < U := Nat.cast_pos.mpr (by omega)
  have hJ0 : (0 : ℝ) < J := Nat.cast_pos.mpr (by omega)
  have hs0 : s0 = 1 - 1 / 400 := rfl
  have hQ0 : (0 : ℝ) < Q := by linarith
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(s0 : ℂ)) with hb
  set v : PC → ℕ → ℂ := fun p n => cv p n * (n : ℂ) ^ (-(ρ p - (s0 : ℂ))) with hv
  set Δ : ℝ := (U : ℝ) + T.card * (8 * Q ^ 3) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have hcv : ∀ p n, ‖cv p n‖ ≤ 1 := fun p n => DirichletCharacter.norm_le_one _ _
  have hmemn : ∀ n ∈ Ioc U (2 * U), 0 < n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hrow : ∀ i ∈ T, ∑ j ∈ T, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ := by
    intro i hi
    rw [← Finset.add_sum_erase T _ hi]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have hone : ∀ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ 1 := by
        intro n hn
        rw [norm_mul, RCLike.norm_conj]
        have h1 : ‖v i n‖ ≤ 1 := by
          simp only [hv]
          rw [norm_mul]
          have h2 : ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 := by
            refine norm_cpow_neg_le_one' (hmemn n hn) ?_
            simp only [Complex.sub_re, Complex.ofReal_re]
            linarith [(hT i hi).2.2.1]
          calc ‖cv i n‖ * ‖(n : ℂ) ^ (-(ρ i - (s0 : ℂ)))‖ ≤ 1 * 1 :=
                mul_le_mul (hcv i n) h2 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        calc ‖v i n‖ * ‖v i n‖ ≤ 1 * 1 := mul_le_mul h1 h1 (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc ∑ n ∈ Ioc U (2 * U), ‖v i n * (starRingEnd ℂ) (v i n)‖ ≤ ∑ n ∈ Ioc U (2 * U), (1 : ℝ) :=
            Finset.sum_le_sum hone
        _ = U := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, show 2 * U - U = U by omega]
    have hoff : ∀ j ∈ T.erase i,
        ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖ ≤ 8 * Q ^ 3 := by
      intro j hj
      obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
      obtain ⟨hpi, hqi, hri1, hri2, himi, -⟩ := hT i hi
      obtain ⟨hpj, hqj, hrj1, hrj2, himj, -⟩ := hT j hjT
      set w : ℂ := (ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ)) with hw
      have hsum : ∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n) =
          ∑ n ∈ Ioc U (2 * U), cv i n * (starRingEnd ℂ) (cv j n) * (n : ℂ) ^ (-w) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
        simp only [hv, map_mul, conj_natCast_cpow_neg]
        rw [hw, show -((ρ i - (s0 : ℂ)) + (starRingEnd ℂ) (ρ j - (s0 : ℂ))) =
            -(ρ i - (s0 : ℂ)) + -(starRingEnd ℂ) (ρ j - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
        ring
      have hwre : w.re = (ρ i).re - s0 + ((ρ j).re - s0) := by
        simp [hw, Complex.conj_re]
      have hwim : w.im = (ρ i).im - (ρ j).im := by
        simp [hw, Complex.conj_im]
        ring
      have hwpos : 0 < w.re := by rw [hwre]; linarith
      have hne : i ≠ j := fun h => hji h.symm
      rw [hsum]
      refine (hPair i j hpi hpj hne w hwpos U hU).trans ?_
      have hwn : ‖w‖ ≤ 1 + 2 * Q := by
        refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
        have hre : |w.re| ≤ 1 := by
          rw [abs_le, hwre]
          constructor <;> linarith
        have him : |w.im| ≤ 2 * Q := by
          rw [hwim]
          calc |(ρ i).im - (ρ j).im| ≤ |(ρ i).im| + |(ρ j).im| := abs_sub _ _
            _ ≤ 2 * Q := by linarith
        linarith
      have hqq : (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) ≤ Q ^ 2 := by
        push_cast at hqi hqj ⊢
        rw [sq]
        exact mul_le_mul hqi hqj (by positivity) hQ0.le
      calc 2 * (((i.1 + 1) * (j.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖) ≤ 2 * Q ^ 2 * (2 + 2 * Q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqq (by norm_num)) (by linarith)
              (by positivity) (by positivity)
        _ ≤ 8 * Q ^ 3 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Q by linarith) (sq_nonneg Q)]
    calc ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v i n)‖ +
          ∑ j ∈ T.erase i, ‖∑ n ∈ Ioc U (2 * U), v i n * (starRingEnd ℂ) (v j n)‖
        ≤ U + (T.erase i).card * (8 * Q ^ 3) := by
          refine add_le_add hdiag ?_
          have := Finset.sum_le_card_nsmul _ _ _ hoff
          rwa [nsmul_eq_mul] at this
      _ ≤ Δ := by
          rw [hΔ]
          have hc : ((T.erase i).card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_erase_le
          nlinarith [pow_pos hQ0 3]
  have hD := hDual PC ℕ T (Ioc U (2 * U)) b v Δ hΔ0 hrow
  have hblk : ∀ i ∈ T, ∑ n ∈ Ioc U (2 * U), b n * v i n = blk Y N U i (ρ i) := by
    intro i hi
    unfold blk
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hmemn n hn).ne'
    simp only [hb, hv]
    rw [show -ρ i = -(s0 : ℂ) + -(ρ i - (s0 : ℂ)) by ring, Complex.cpow_add _ _ hn0]
    ring
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
    refine le_trans (le_of_eq ?_) (hL Y N U hU)
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hb]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hmemn n hn)]
    simp only [Complex.neg_re, Complex.ofReal_re]
  have hlow : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      ∑ i ∈ T, ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2 := by
    have := Finset.card_nsmul_le_sum T (fun i => ‖∑ n ∈ Ioc U (2 * U), b n * v i n‖ ^ 2)
      ((1 / (2 * (J : ℝ))) ^ 2) (fun i hi => by
        rw [hblk i hi]
        exact pow_le_pow_left₀ (by positivity) (hT i hi).2.2.2.2.2 2)
    rwa [nsmul_eq_mul] at this
  have hup := hD.trans (mul_le_mul_of_nonneg_right hbn hΔ0)
  have hUU : (U : ℝ) ^ (-(197 / 200 : ℝ)) * U = (U : ℝ) ^ (3 / 200 : ℝ) := by
    rw [← Real.rpow_add_one hU0.ne']
    norm_num
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hsm : (T.card : ℝ) * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) ≤
      T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc 8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ))) = 8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) := by
          ring
      _ ≤ _ := hsmall
  have key : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 ≤
      C * (U : ℝ) ^ (3 / 200 : ℝ) + T.card * (1 / (8 * (J : ℝ) ^ 2)) := by
    calc _ ≤ _ := hlow.trans hup
      _ = C * ((U : ℝ) ^ (-(197 / 200 : ℝ)) * U) +
            T.card * (8 * Q ^ 3 * (C * (U : ℝ) ^ (-(197 / 200 : ℝ)))) := by
          rw [hΔ]
          ring
      _ ≤ _ := by
          rw [hUU]
          linarith [hsm]
  have e1 : (T.card : ℝ) * (1 / (2 * (J : ℝ))) ^ 2 = 2 * ((T.card : ℝ) / (8 * (J : ℝ) ^ 2)) := by
    field_simp
    ring
  have e2 : (T.card : ℝ) * (1 / (8 * (J : ℝ) ^ 2)) = (T.card : ℝ) / (8 * (J : ℝ) ^ 2) := by
    rw [mul_one_div]
  rw [e1, e2] at key
  have h3 : (T.card : ℝ) / (8 * (J : ℝ) ^ 2) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  calc (T.card : ℝ) ≤ C * (U : ℝ) ^ (3 / 200 : ℝ) * (8 * (J : ℝ) ^ 2) := h3
    _ = 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZPair
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

scoped instance (p p' : PC) : NeZero ((p.1 + 1) * (p'.1 + 1)) := ⟨by positivity⟩

def mulLevel (p p' : PC) : DirichletCharacter ℂ ((p.1 + 1) * (p'.1 + 1)) :=
  DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2 *
    (DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2)⁻¹

theorem mulLevel_ne_one (p p' : PC) (hp : p.2.IsPrimitive) (hp' : p'.2.IsPrimitive) (hne : p ≠ p') :
    mulLevel p p' ≠ 1 := by
  intro h
  have h1 := mul_inv_eq_one.mp h
  have hc := congrArg DirichletCharacter.conductor h1
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    hp, hp'] at hc
  obtain ⟨N, χ⟩ := p
  obtain ⟨N', χ'⟩ := p'
  simp only [add_left_inj] at hc
  subst hc
  apply hne
  have := DirichletCharacter.changeLevel_injective (dvd_mul_right (N + 1) (N + 1)) h1
  exact congrArg (Sigma.mk N) this

theorem mulLevel_apply (p p' : PC) (n : ℕ) :
    mulLevel p p' (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n * (starRingEnd ℂ) (cv p' n) := by
  by_cases hu : IsUnit (n : ZMod ((p.1 + 1) * (p'.1 + 1)))
  · obtain ⟨u, hu⟩ := hu
    have e1 : DirichletCharacter.changeLevel (dvd_mul_right (p.1 + 1) (p'.1 + 1)) p.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_right _ _)]
      rfl
    have e2 : DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1))) = cv p' n := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
        ZMod.cast_natCast (dvd_mul_left _ _)]
      rfl
    have hn : ‖DirichletCharacter.changeLevel (dvd_mul_left (p'.1 + 1) (p.1 + 1)) p'.2
        (n : ZMod ((p.1 + 1) * (p'.1 + 1)))‖ = 1 := by
      rw [← hu]
      exact DirichletCharacter.unit_norm_eq_one _ u
    unfold mulLevel
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', e1, Complex.inv_eq_conj hn, e2]
  · rw [MulChar.map_nonunit _ hu]
    rw [ZMod.isUnit_iff_coprime] at hu
    by_cases h1 : n.Coprime (p.1 + 1)
    · have h2 : ¬ n.Coprime (p'.1 + 1) := fun h2 => hu (Nat.Coprime.mul_right h1 h2)
      have h3 : cv p' n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, map_zero, mul_zero]
    · have h3 : cv p n = 0 := MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h3, zero_mul]

private lemma sum_range_natCast_zmod_eq_sum_univ {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) :
    ∑ n ∈ Finset.range Q, f (n : ZMod Q) = ∑ x : ZMod Q, f x := by
  refine Finset.sum_nbij (fun n : ℕ => (n : ZMod Q)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb hab
    have ha' : a < Q := Finset.mem_range.mp ha
    have hb' : b < Q := Finset.mem_range.mp hb
    have h := congrArg ZMod.val hab
    simp only at h
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at h
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

private lemma sum_range_modulus_shift_eq_zero_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q) = 0 := by
  calc ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q)
        = ∑ n ∈ Finset.range Q, (fun x => ψ ((M : ZMod Q) + x)) (n : ZMod Q) := by
          simp [Nat.cast_add]
    _ = ∑ x : ZMod Q, ψ ((M : ZMod Q) + x) := sum_range_natCast_zmod_eq_sum_univ (fun x => ψ ((M : ZMod Q) + x))
    _ = ∑ x : ZMod Q, ψ x := Equiv.sum_comp (Equiv.addLeft (M : ZMod Q)) ψ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hψ

private lemma norm_charSum_range_le_modulus_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖ ≤ (Q : ℝ) := by
  have hQ : 0 < Q := NeZero.pos Q
  refine Nat.strong_induction_on M ?_
  intro M ih
  by_cases hM : M < Q
  · calc ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖
          ≤ ∑ n ∈ Finset.range M, ‖ψ (n : ZMod Q)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one ψ _
      _ = M := by simp
      _ ≤ Q := by exact_mod_cast hM.le
  · obtain ⟨K, hK⟩ : ∃ K, M = K + Q := ⟨M - Q, by omega⟩
    subst hK
    rw [Finset.sum_range_add, sum_range_modulus_shift_eq_zero_of_ne_one ψ hψ K, add_zero]
    exact ih K (by omega)

theorem pair_sum_bound : PairSum := by
  intro p p' hp hp' hne M
  have h := norm_charSum_range_le_modulus_of_ne_one (mulLevel p p') (mulLevel_ne_one p p' hp hp' hne) M
  simpa only [mulLevel_apply] using h

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZTwist
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma norm_cpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma norm_cpow_step_le {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 < w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have h := Formalism.FX.LFunctionPartialSum.norm_cpow_sub_le' hi0 hw
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e1, e2, norm_sub_rev] at h
  refine h.trans ?_
  have hUi : (U : ℝ) ≤ i := by exact_mod_cast hi
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have h1 : (i : ℝ) ^ (-w.re - 1) ≤ (i : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ i)) (by linarith)
  have h2 : (i : ℝ) ^ (-1 : ℝ) ≤ 1 / U := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ hU0 hUi
  calc ‖w‖ * (i : ℝ) ^ (-w.re - 1) ≤ ‖w‖ * (1 / U) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
    _ = ‖w‖ / U := by ring

theorem pair_twist_bound : PairTwistOf := by
  intro hPS p p' hp hp' hne w hw U hU
  set m : ℝ := (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) with hm
  set g : ℕ → ℂ := fun n => cv p n * (starRingEnd ℂ) (cv p' n) with hg
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-w) with hf
  have hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m := fun k => hPS p p' hp hp' hne k
  have hm0 : 0 ≤ m := by positivity
  have hrw : ∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), f n • g n := by
    refine sum_congr rfl (fun n _ => ?_); simp only [hf, hg, smul_eq_mul]; ring
  rw [hrw, Finset.sum_Ioc_by_parts f g (by omega : U < 2 * U)]
  have hb1 : ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (2 * U)‖ * ‖∑ i ∈ range (2 * U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb2 : ‖f (U + 1) • ∑ i ∈ range (U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (U + 1)‖ * ‖∑ i ∈ range (U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb3 : ‖∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ m * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ioc U (2 * U - 1),
        ‖(f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ ‖w‖ / U * m := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have hi' : U ≤ i := by have := (mem_Ioc.1 hi).1; omega
      exact mul_le_mul (norm_cpow_step_le hU hi' hw) (hGs _) (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hcnt : ((2 * U - 1 - U : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : 2 * U - 1 - U ≤ U)
    calc ((2 * U - 1 - U : ℕ) : ℝ) * (‖w‖ / U * m) ≤ U * (‖w‖ / U * m) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = m * ‖w‖ := by field_simp
  calc ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i - f (U + 1) • ∑ i ∈ range (U + 1), g i -
        ∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖
      ≤ m + m + m * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ ≤ 2 * m * (1 + ‖w‖) := by nlinarith [norm_nonneg w]

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZNum
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem numeric_constants : Num := by
  intro C hC
  have h3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 7 / 100)).bound
    (by norm_num : (0 : ℝ) < 1 / 32768)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 47 / 50)).bound
    (by positivity : (0 : ℝ) < 1 / (65536 * (C + 1)))
  obtain ⟨Q1, hQ1⟩ := Filter.eventually_atTop.1 (h3.and h2)
  refine ⟨max 20 Q1, 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ), le_max_left _ _, fun Q hQ => ?_⟩
  have hQ20 : 20 ≤ Q := (le_max_left _ _).trans hQ
  obtain ⟨hl3, hl2⟩ := hQ1 Q ((le_max_right _ _).trans hQ)
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 ≤ Real.log Q := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    abs_of_nonneg (Real.rpow_nonneg hQ0.le _)] at hl3 hl2
  have hl3' : Real.log Q ^ 3 ≤ 1 / 32768 * Q ^ (7 / 100 : ℝ) := by
    have e : Real.log Q ^ (3 : ℝ) = Real.log Q ^ 3 := by simpa using Real.rpow_natCast (Real.log Q) 3
    rw [← e]
    exact hl3
  have hl2' : Real.log Q ^ 2 ≤ 1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ) := by
    have e : Real.log Q ^ (2 : ℝ) = Real.log Q ^ 2 := by simpa using Real.rpow_natCast (Real.log Q) 2
    rw [← e]
    exact hl2
  have hq1 : Q ≤ (q0 Q : ℝ) := by rw [q0]; exact Nat.le_ceil Q
  have hq2 : (q0 Q : ℝ) ≤ 2 * Q := by
    rw [q0]
    have := Nat.ceil_lt_add_one hQ0.le
    linarith
  have hqpos : 0 < q0 Q := by exact_mod_cast lt_of_lt_of_le hQ0 hq1
  have hL2 : 2 ^ Nat.log 2 (q0 Q) ≤ q0 Q := Nat.pow_log_le_self 2 hqpos.ne'
  have hJdef : pJ Q = 8 * (Nat.log 2 (q0 Q) + 1) := by rw [pJ]
  have hYdef : pY Q = q0 Q ^ 4 := by rw [pY]
  have hLr : (Nat.log 2 (q0 Q) : ℝ) * Real.log 2 ≤ Real.log Q + Real.log 2 := by
    have h1 : ((2 ^ Nat.log 2 (q0 Q) : ℕ) : ℝ) ≤ q0 Q := by exact_mod_cast hL2
    push_cast at h1
    have h4 : Real.log ((2 : ℝ) ^ Nat.log 2 (q0 Q)) ≤ Real.log (2 * Q) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow, Real.log_mul (by norm_num) hQ0.ne'] at h4
    linarith
  have hlt2 := Real.log_two_gt_d9
  have hlt2' := Real.log_two_lt_d9
  have hL' : (Nat.log 2 (q0 Q) : ℝ) ≤ 3 * Real.log Q := by
    by_contra hc
    push_neg at hc
    nlinarith [(Nat.cast_nonneg (Nat.log 2 (q0 Q)) : (0 : ℝ) ≤ _)]
  have hJ : (pJ Q : ℝ) ≤ 32 * Real.log Q := by
    rw [hJdef]
    push_cast
    linarith
  have hJpos : (0 : ℝ) < pJ Q := by rw [hJdef]; positivity
  constructor
  · intro j _
    have hY : Q ^ 4 ≤ ((pY Q * 2 ^ j : ℕ) : ℝ) := by
      rw [hYdef]
      push_cast
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      calc Q ^ 4 ≤ (q0 Q : ℝ) ^ 4 := by gcongr
        _ ≤ (q0 Q : ℝ) ^ 4 * 2 ^ j := le_mul_of_one_le_right (by positivity) h1
    have hpow : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ Q ^ (-(197 / 50 : ℝ)) := by
      calc ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ (Q ^ 4) ^ (-(197 / 200 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hY (by norm_num)
        _ = Q ^ (-(197 / 50 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
            norm_num
    have hQ3 : Q ^ 3 * Q ^ (-(197 / 50 : ℝ)) = Q ^ (-(47 / 50 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hQ0]
      norm_num
    have hQ47 : Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hQ0]
      norm_num
    have hkey : 64 * C * (pJ Q : ℝ) ^ 2 ≤ Q ^ (47 / 50 : ℝ) := by
      have hJ2 : (pJ Q : ℝ) ^ 2 ≤ 1024 * Real.log Q ^ 2 := by nlinarith
      have hC1 : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc 64 * C * (pJ Q : ℝ) ^ 2 ≤ 64 * C * (1024 * Real.log Q ^ 2) := by gcongr
        _ ≤ 64 * C * (1024 * (1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ))) := by gcongr
        _ = C / (C + 1) * Q ^ (47 / 50 : ℝ) := by field_simp; ring
        _ ≤ 1 * Q ^ (47 / 50 : ℝ) := by gcongr
        _ = Q ^ (47 / 50 : ℝ) := one_mul _
    rw [le_div_iff₀ (by positivity)]
    calc 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2)
        ≤ 8 * Q ^ 3 * C * Q ^ (-(197 / 50 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2) := by gcongr
      _ = (64 * C * (pJ Q : ℝ) ^ 2) * (Q ^ 3 * Q ^ (-(197 / 50 : ℝ))) := by ring
      _ ≤ Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) := by rw [hQ3]; gcongr
      _ = 1 := hQ47
  · have hJ2 : (2 : ℕ) ^ pJ Q ≤ 256 * q0 Q ^ 8 := by
      rw [hJdef, pow_mul', pow_succ]
      calc (2 ^ Nat.log 2 (q0 Q) * 2) ^ 8 = 256 * (2 ^ Nat.log 2 (q0 Q)) ^ 8 := by ring
        _ ≤ 256 * q0 Q ^ 8 := by gcongr
    have hYJ : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ 1048576 * Q ^ 12 := by
      have h1 : pY Q * 2 ^ pJ Q ≤ q0 Q ^ 4 * (256 * q0 Q ^ 8) := by
        rw [hYdef]
        exact Nat.mul_le_mul_left _ hJ2
      have h4 : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := by
        exact_mod_cast h1
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := h4
        _ ≤ (2 * Q) ^ 4 * (256 * (2 * Q) ^ 8) := by gcongr
        _ = 1048576 * Q ^ 12 := by ring
    have hpow : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤
        (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (1048576 * Q ^ 12) ^ (3 / 200 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hYJ (by norm_num)
        _ = (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast Q 12,
              ← Real.rpow_mul hQ0.le]
            norm_num
    have hJ3 : (pJ Q : ℝ) ^ 3 ≤ Q ^ (7 / 100 : ℝ) := by
      calc (pJ Q : ℝ) ^ 3 ≤ (32 * Real.log Q) ^ 3 := by gcongr
        _ = 32768 * Real.log Q ^ 3 := by ring
        _ ≤ 32768 * (1 / 32768 * Q ^ (7 / 100 : ℝ)) := by gcongr
        _ = Q ^ (7 / 100 : ℝ) := by ring
    have hQ14 : 1 ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hsplit : Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ) = Q ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hQ0]
      norm_num
    calc 1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ))
        = 1 + 8 * C * ((pJ Q : ℝ) ^ 3 * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) := by ring
      _ ≤ 1 + 8 * C * (Q ^ (7 / 100 : ℝ) * ((1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ))) := by
          gcongr
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * (Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ)) := by ring
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by rw [hsplit]
      _ ≤ Q ^ (1 / 4 : ℝ) + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by gcongr
      _ = (1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ)) * Q ^ (1 / 4 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem zero_density_box : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox :=
  final_bound_of_assembly (coefficient_square_bound Formalism.FX.divisor_weight_bound) (zero_detection mollifier_identity)
    (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
