module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

def qPoch (t : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - t ^ (i + 1))

def qPochInf (t : ℂ) : ℂ := ∏' i : ℕ, (1 - t ^ (i + 1))

def qBinom (t : ℂ) (m k : ℕ) : ℂ := qPoch t m / (qPoch t k * qPoch t (m - k))

def finCoeff (t : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  if j.natAbs ≤ n then qBinom t (2 * n) ((n : ℤ) + j).toNat else 0

theorem qPoch_tendsto (t : ℂ) (ht : ‖t‖ < 1) :
    Filter.Tendsto (qPoch t) Filter.atTop (nhds (qPochInf t)) ∧ qPochInf t ≠ 0 ∧
      ∀ m, qPoch t m ≠ 0 := by
  have hg : Summable (fun i : ℕ => ‖t‖ * ‖t‖ ^ i) :=
    (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left ‖t‖
  have hsum : Summable (fun i : ℕ => ‖-(t ^ (i + 1))‖) :=
    hg.congr (fun i => by rw [norm_neg, norm_pow, pow_succ, mul_comm])
  have hne : ∀ i : ℕ, 1 + -(t ^ (i + 1)) ≠ 0 := by
    intro i h
    have h1 : t ^ (i + 1) = 1 := by linear_combination -h
    have h2 : ‖t‖ ^ (i + 1) < 1 := pow_lt_one₀ (norm_nonneg t) ht (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hm := multipliable_one_add_of_summable hsum
  have h0 := tprod_one_add_ne_zero_of_summable hne hsum
  simp only [← sub_eq_add_neg] at hm h0 hne
  refine ⟨hm.hasProd.tendsto_prod_nat, h0, fun m => Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)⟩

theorem tpFactor_eq (τ : ℍ) (z : ℂ) (k : ℕ) :
    GlobalTheory.ThetaWeberRoad.tpFactor τ z k = (1 - (cexp (π * I * (τ : ℂ)) ^ 2) ^ (k + 1)) *
      ((1 + cexp (2 * π * I * z) * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1)) *
        (1 + (cexp (2 * π * I * z))⁻¹ * cexp (π * I * (τ : ℂ)) ^ (2 * k + 1))) := by
  unfold GlobalTheory.ThetaWeberRoad.tpFactor
  rw [← pow_mul, ← exp_nat_mul, ← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]
  rw [mul_assoc]
  congr 3 <;> push_cast <;> ring_nf

theorem jacobiTheta₂_term_eq_zpow (τ z : ℂ) (j : ℤ) :
    jacobiTheta₂_term j z τ = cexp (2 * π * I * z) ^ j * cexp (π * I * τ) ^ (j ^ 2) := by
  unfold jacobiTheta₂_term
  rw [← exp_int_mul, ← exp_int_mul, ← exp_add]
  congr 1
  push_cast
  ring

theorem norm_exp_pi_I_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖cexp (π * I * τ)‖ < 1 := by
  rw [norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have : (π * I * τ).re = -(π * τ.im) := by simp
  rw [this]
  have := Real.pi_pos
  nlinarith

theorem multipliable_tpFactor (τ : ℍ) (z : ℂ) :
    Multipliable (GlobalTheory.ThetaWeberRoad.tpFactor τ z) := by
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) τ.2
  have g : Summable (fun k : ℕ => (‖s‖ ^ 2) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg s])
  have h1 : Multipliable (fun k : ℕ => 1 + -((s ^ 2) ^ (k + 1))) :=
    multipliable_one_add_of_summable ((g.mul_left (‖s‖ ^ 2)).congr (fun k => by
      rw [norm_neg, norm_pow, norm_pow, pow_succ]; ring))
  have h2 : Multipliable (fun k : ℕ => 1 + x * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  have h3 : Multipliable (fun k : ℕ => 1 + x⁻¹ * s ^ (2 * k + 1)) :=
    multipliable_one_add_of_summable ((g.mul_left (‖x⁻¹‖ * ‖s‖)).congr (fun k => by
      rw [norm_mul, norm_pow]; ring))
  convert h1.mul (h2.mul h3) using 1
  funext k
  rw [tpFactor_eq]
  ring

end GlobalTheory.JacobiTriple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteCoeffTendstoAndBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteCoeffTendstoAndBounded
open Complex
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem finCoeff_tendsto_and_bounded :
    ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j)
      Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧
      ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  intro t ht
  obtain ⟨hlim, hP0, hne⟩ := qPoch_tendsto t ht
  refine ⟨fun j => ?_, ?_⟩
  · have ha : Filter.Tendsto (fun n : ℕ => ((n : ℤ) + j).toNat) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_
      exact Filter.tendsto_sub_atTop_nat _
    have hb : Filter.Tendsto (fun n : ℕ => 2 * n - ((n : ℤ) + j).toNat) Filter.atTop
        Filter.atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n - j.natAbs) (fun n => by omega) ?_
      exact Filter.tendsto_sub_atTop_nat _
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) Filter.tendsto_id
    have hmain : Filter.Tendsto (fun n : ℕ => qPoch t (2 * n) /
        (qPoch t ((n : ℤ) + j).toNat * qPoch t (2 * n - ((n : ℤ) + j).toNat))) Filter.atTop
        (nhds (qPochInf t / (qPochInf t * qPochInf t))) :=
      (hlim.comp h2).div ((hlim.comp ha).mul (hlim.comp hb)) (mul_ne_zero hP0 hP0)
    have hval : qPochInf t / (qPochInf t * qPochInf t) = (qPochInf t)⁻¹ := by
      field_simp
    rw [hval] at hmain
    refine hmain.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop j.natAbs] with n hn
    simp [finCoeff, qBinom, hn]
  · obtain ⟨B1, hB1⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hlim)
    obtain ⟨B2, hB2⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hlim.inv₀ hP0))
    set B := max B1 B2
    have b1 : ∀ m, ‖qPoch t m‖ ≤ B := fun m => (hB1 _ ⟨m, rfl⟩).trans (le_max_left _ _)
    have b2 : ∀ m, ‖(qPoch t m)⁻¹‖ ≤ B := fun m => (hB2 _ ⟨m, rfl⟩).trans (le_max_right _ _)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (b1 0)
    refine ⟨max (B ^ 3) 0, fun n j => ?_⟩
    unfold finCoeff
    split_ifs
    · unfold qBinom
      rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
      refine le_max_of_le_left ?_
      calc ‖qPoch t (2 * n)‖ * (‖(qPoch t ((n : ℤ) + j).toNat)⁻¹‖ *
            ‖(qPoch t (2 * n - ((n : ℤ) + j).toNat))⁻¹‖) ≤ B * (B * B) := by
            gcongr
            · exact b1 _
            · exact b2 _
            · exact b2 _
        _ = B ^ 3 := by ring
    · simp

end GlobalTheory.JacobiTriple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteCoeffTendstoAndBoundedStatement
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded : ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j) Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧ ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  first | exact @GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | exact GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | (intros; apply GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimit
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

theorem tendsto_finCoeff_sum_jacobiTheta₂ : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im →
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
      GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ)
      Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  intro τ z hτ
  set t := cexp (π * I * τ) ^ 2 with ht
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_exp_pi_I_lt_one τ hτ
  have ht1 : ‖t‖ < 1 := by
    rw [ht, norm_pow]
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  obtain ⟨hlim, C, hC⟩ := GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded t ht1
  have hsum : Summable (fun j : ℤ => C * ‖jacobiTheta₂_term j z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).2 hτ).norm.mul_left C
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (n : ℕ) (j : ℤ) => finCoeff t n j * jacobiTheta₂_term j z τ)
    (g := fun j => jacobiTheta₂_term j z τ * (qPochInf t)⁻¹) hsum
    (fun j => by
      have := (hlim j).mul_const (jacobiTheta₂_term j z τ)
      simpa [mul_comm] using this)
    (Filter.Eventually.of_forall fun n j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n j) (norm_nonneg _))
  rw [tsum_mul_right] at hT
  refine hT.congr (fun n => ?_)
  apply tsum_eq_sum
  intro j hj
  have : ¬ j.natAbs ≤ n := by
    intro h
    apply hj
    rw [Finset.mem_Icc]
    omega
  simp [finCoeff, this]

end GlobalTheory.JacobiTriple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimitStatement
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_triple_product_limit : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im → Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ) Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  first | exact @GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ | exact GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ | (intros; apply GlobalTheory.JacobiTriple.tendsto_finCoeff_sum_jacobiTheta₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFinite
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple.QBinomial

open GlobalTheory.JacobiTriple

theorem qPoch_succ (t : ℂ) (n : ℕ) : qPoch t (n + 1) = qPoch t n * (1 - t ^ (n + 1)) := by
  unfold qPoch; rw [Finset.prod_range_succ]

theorem qBinom_zero_right (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m 0 = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; rw [show qPoch t 0 = 1 by simp [qPoch], Nat.sub_zero]; field_simp

theorem qBinom_self (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m m = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; simp [Nat.sub_self]; rw [show qPoch t 0 = 1 by simp [qPoch]]; field_simp

theorem qBinom_pascal (t : ℂ) (ht : ‖t‖ < 1) (m k : ℕ) (hk : k < m) :
    qBinom t (m + 1) (k + 1) = qBinom t m (k + 1) + t ^ (m - k) * qBinom t m k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  have hne := (qPoch_tendsto t ht).2.2
  have e1 : k + 1 + j + 1 - (k + 1) = j + 1 := by omega
  have e2 : k + 1 + j - (k + 1) = j := by omega
  have e3 : k + 1 + j - k = j + 1 := by omega
  unfold qBinom
  rw [e1, e2, e3, qPoch_succ t (k + 1 + j), qPoch_succ t k, qPoch_succ t j]
  have hk1 : (1 - t ^ (k + 1)) ≠ 0 := by
    have := hne (k + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hj1 : (1 - t ^ (j + 1)) ≠ 0 := by
    have := hne (j + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hk0 := hne k
  have hj0 := hne j
  field_simp
  ring

theorem exp_eq (m k : ℕ) (hk : k < m) : k * (k - 1) + 2 * m = (k + 1) * k + 2 * (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  rw [show k + 1 + j - k = j + 1 by omega]
  rcases k with _ | k
  · ring
  · simp only [Nat.add_sub_cancel]; ring

theorem qBinomial_finite : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  intro s X hs m
  have ht : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  induction m with
  | zero => simp [qBinom_zero_right _ ht]
  | succ m ih =>
    set f : ℕ → ℕ → ℂ := fun m k => qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k with hf
    change ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), f m k at ih
    change _ = ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k
    rw [Finset.prod_range_succ, ih, mul_add, mul_one]
    have A : ∑ k ∈ Finset.range (m + 1), f m k = f m 0 + ∑ k ∈ Finset.range m, f m (k + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have B : (∑ k ∈ Finset.range (m + 1), f m k) * (X * s ^ (2 * m)) =
        ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) + f m m * (X * s ^ (2 * m)) := by
      rw [Finset.sum_mul, Finset.sum_range_succ]
    have C : ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k =
        f (m + 1) 0 + ∑ k ∈ Finset.range m, f (m + 1) (k + 1) + f (m + 1) (m + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ', add_comm (f (m + 1) 0)]
    have hsum : ∑ k ∈ Finset.range m, f (m + 1) (k + 1)
        = ∑ k ∈ Finset.range m, f m (k + 1) + ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_range.mp hk
      simp only [hf]
      rw [qBinom_pascal _ ht m k hk']
      have : s ^ (k * (k - 1)) * s ^ (2 * m) = s ^ ((k + 1) * k) * (s ^ 2) ^ (m - k) := by
        rw [← pow_add, ← pow_mul, ← pow_add, exp_eq m k hk']
      simp only [Nat.add_sub_cancel]
      linear_combination (-(qBinom (s ^ 2) m k * X ^ (k + 1))) * this
    have hlast : s ^ ((m + 1) * (m + 1 - 1)) = s ^ (m * (m - 1)) * s ^ (2 * m) := by
      rw [← pow_add]; congr 1; rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    have e0 : f (m + 1) 0 = f m 0 := by
      simp only [hf, qBinom_zero_right _ ht]
    have em : f (m + 1) (m + 1) = f m m * (X * s ^ (2 * m)) := by
      simp only [hf, qBinom_self _ ht, hlast]; ring
    rw [B, A, C, hsum, e0, em]
    ring

end GlobalTheory.JacobiTriple.QBinomial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFiniteStatement
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  first | exact @GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | exact GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | (intros; apply GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProduct
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

theorem finTriple_sum_odd (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem finTriple_term (s x : ℂ) (hs : s ≠ 0) (hx : x ≠ 0) (n k : ℕ) (hk : k ≤ 2 * n) :
    (x⁻¹ ^ n * s ^ (n ^ 2)) *
        (qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * (x * s ^ ((1 : ℤ) - 2 * n)) ^ k) =
      finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
  have hc : finCoeff (s ^ 2) n ((k : ℤ) - n) = qBinom (s ^ 2) (2 * n) k := by
    unfold finCoeff
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [hc]
  have hkk : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases k with _ | k
    · simp
    · push_cast [Nat.add_sub_cancel]; ring
  have he : ((k : ℤ) - n) ^ 2 = ((n ^ 2 + k * (k - 1) : ℕ) : ℤ) + (1 - 2 * n) * k := by
    rw [Nat.cast_add, hkk]; push_cast; ring
  have hxz : x ^ ((k : ℤ) - n) = x ^ k * x⁻¹ ^ n := by
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow]
  rw [hxz, he, zpow_add₀ hs, zpow_natCast, zpow_mul, zpow_natCast, pow_add, mul_pow]
  ring

theorem finTriple (s x : ℂ) (hs : s ≠ 0) (hs1 : ‖s‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  set X := x * s ^ ((1 : ℤ) - 2 * n) with hX
  have ha : ∀ k ∈ Finset.range n, 1 + x * s ^ (2 * k + 1) = 1 + X * s ^ (2 * (n + k)) := by
    intro k _
    rw [hX, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs]
    congr 3
    push_cast; ring
  have hb : ∀ k ∈ Finset.range n, 1 + x⁻¹ * s ^ (2 * k + 1) =
      (x⁻¹ * s ^ (2 * k + 1)) * (1 + X * s ^ (2 * (n - 1 - k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e : ((2 * k + 1 : ℕ) : ℤ) + (1 - 2 * n) + ((2 * (n - 1 - k) : ℕ) : ℤ) = 0 := by omega
    have hab : x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k))) = 1 := by
      calc x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k)))
          = (x⁻¹ * x) * (s ^ ((2 * k + 1 : ℕ) : ℤ) * s ^ ((1 : ℤ) - 2 * n) *
              s ^ ((2 * (n - 1 - k) : ℕ) : ℤ)) := by
            rw [hX, zpow_natCast, zpow_natCast]; ring
        _ = 1 := by
            rw [inv_mul_cancel₀ hx, ← zpow_add₀ hs, ← zpow_add₀ hs, e, zpow_zero, one_mul]
    linear_combination -hab
  have hr : ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n - 1 - k))) =
      ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k)) :=
    Finset.prod_range_reflect (fun k => 1 + X * s ^ (2 * k)) n
  have hC : ∏ k ∈ Finset.range n, (x⁻¹ * s ^ (2 * k + 1)) = x⁻¹ ^ n * s ^ (n ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, finTriple_sum_odd]
  have hsplit : ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) =
      (∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))) *
        ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n + k))) := by
    rw [two_mul, Finset.prod_range_add]
  rw [Finset.prod_mul_distrib, Finset.prod_congr rfl ha, Finset.prod_congr rfl hb,
    Finset.prod_mul_distrib, hr, hC]
  calc _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) := by
        rw [hsplit]; ring
    _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∑ k ∈ Finset.range (2 * n + 1),
          qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * X ^ k := by
        rw [GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom s X hs1 (2 * n)]
    _ = ∑ k ∈ Finset.range (2 * n + 1),
          finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        exact finTriple_term s x hs hx n k (by omega)
    _ = _ := by
        refine Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - n) (fun j : ℤ => (j + n).toNat)
          ?_ ?_ ?_ ?_ ?_
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_range] at ha
          simp only [Finset.mem_coe, Finset.mem_Icc]; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          simp only [Finset.mem_coe, Finset.mem_range]; omega
        · intro a _; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          omega
        · intro a _; rfl

end GlobalTheory.JacobiTriple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProductStatement
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiTriple_finite_product : ∀ (s x : ℂ), s ≠ 0 → ‖s‖ < 1 → x ≠ 0 → ∀ n : ℕ, ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  first | exact @GlobalTheory.JacobiTriple.finTriple | exact GlobalTheory.JacobiTriple.finTriple | (intros; apply GlobalTheory.JacobiTriple.finTriple <;> assumption)
end
end

open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.JacobiTriple

theorem tripleProduct : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this

end GlobalTheory.JacobiTriple
