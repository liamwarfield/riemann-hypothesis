module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicProperties
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNHS

theorem hs_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (C C' : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), C ≤ C' → HS ε C φ h → HS ε C' φ h) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ + ψ) (h + h') ∧ HS ε C (φ - ψ) (h - h')) ∧ (∀ (C : ℝ) (r : ℚ) (c : Ω), HS ε C (fun z => ε c * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (HahnSeries.single r c)) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h : HahnSeries ℚ Ω), (∀ z : ℂ, C < z.im → φ z = ψ z) → HS ε C φ h → HS ε C ψ h) := by
  intro Ω _ ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C C' φ h hC hs z hz
    exact hs z (lt_of_le_of_lt hC hz)
  · intro C φ ψ h h' hφ hψ
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have := (hφ z hz).add (hψ z hz)
      simpa [HahnSeries.coeff_add, map_add (f := _), add_mul] using this
    · have := (hφ z hz).sub (hψ z hz)
      simpa [HahnSeries.coeff_sub, map_sub, sub_mul] using this
  · intro C r c z _
    have := hasSum_single (f := fun s : ℚ => ε ((HahnSeries.single r c).coeff s) *
        Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * z)) r (by
      intro b hb
      simp [HahnSeries.coeff_single_of_ne hb])
    simpa [HahnSeries.coeff_single_same] using this
  · intro C φ ψ h hφψ hs z hz
    rw [← hφψ z hz]
    exact hs z hz

end GlobalTheory.FNHS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicPropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionSumAbove_basic_properties : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (C C' : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), C ≤ C' → HS ε C φ h → HS ε C' φ h) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ + ψ) (h + h') ∧ HS ε C (φ - ψ) (h - h')) ∧ (∀ (C : ℝ) (r : ℚ) (c : Ω), HS ε C (fun z => ε c * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (HahnSeries.single r c)) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h : HahnSeries ℚ Ω), (∀ z : ℂ, C < z.im → φ z = ψ z) → HS ε C φ h → HS ε C ψ h) := by
  first | exact @GlobalTheory.FNHS.hs_props | exact GlobalTheory.FNHS.hs_props | (intros; apply GlobalTheory.FNHS.hs_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergent
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergent
namespace GlobalTheory

namespace PowerSeriesInv

theorem coeff_inv_norm_le (a : ℕ → ℂ) (M R : ℝ) (hR : 0 < R) (ha0 : a 0 ≠ 0)
    (hM : ∀ n, ‖a n‖ ≤ M * R ^ n) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ ≤ ‖a 0‖⁻¹ * (R * (1 + M / ‖a 0‖)) ^ n := by
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) = a 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  set A := ‖a 0‖ with hA
  have hA0 : 0 < A := norm_pos_iff.mpr ha0
  have hMA : A ≤ M := by simpa using hM 0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 hMA
  set m := M / A with hm
  have hm0 : 0 < m := div_pos hM0 hA0
  set K := R * (1 + m) with hK
  set q := (1 + m)⁻¹ with hq
  have hK0 : 0 < K := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hRK : R = K * q := by
    rw [hK, hq, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have hqA : q / (1 - q) = A / M := by
    have hqpos : 0 < q := by positivity
    have h1q : 1 - q = m * q := by
      have : (1 + m) * q = 1 := mul_inv_cancel₀ (by positivity)
      linarith
    rw [h1q, hm]
    field_simp
  have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0) ≤ A / M := by
    intro n
    rw [Finset.sum_range_succ']
    simp only [show ∀ k : ℕ, 1 ≤ k + 1 from fun k => by omega, if_true,
      show ¬ (1 ≤ 0) from by omega, if_false, add_zero]
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    calc (∑ i ∈ Finset.range n, q ^ i) * q ≤ 1 / (1 - q) * q := by gcongr
      _ = q / (1 - q) := by ring
      _ = A / M := hqA
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · subst hn
    simp [hc0, hA]
  · have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ‖(if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ ≤
          M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      split_ifs with h1 h2 h2
      · rw [norm_mul, PowerSeries.coeff_mk]
        calc ‖a p.1‖ * ‖PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹‖
            ≤ (M * R ^ p.1) * (A⁻¹ * K ^ p.2) :=
              mul_le_mul (hM _) (ih _ h1) (norm_nonneg _) (by positivity)
          _ = M * A⁻¹ * K ^ n * q ^ p.1 := by
              rw [hRK, ← hp, mul_pow, pow_add]; ring
      · omega
      · simp only [norm_zero]; positivity
      · simp
    calc ‖-(PowerSeries.constantCoeff (PowerSeries.mk a))⁻¹ *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖
        = A⁻¹ * ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then
            PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ := by
          rw [norm_mul, norm_neg, norm_inv, hc0]
      _ ≤ A⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
            (by positivity)
      _ = A⁻¹ * (M * A⁻¹ * K ^ n *
            ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0)) := by
          rw [← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      _ ≤ A⁻¹ * (M * A⁻¹ * K ^ n * (A / M)) := by
          gcongr
          exact hgeom n
      _ = A⁻¹ * K ^ n := by
          field_simp

theorem hasSum_inv :
    ∀ (a : ℕ → ℂ) (ρ : ℝ), 0 < ρ → a 0 ≠ 0 → (∀ x : ℂ, ‖x‖ < ρ → Summable fun n => a n * x ^ n) →
      ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ x : ℂ, ‖x‖ < ρ' → (∑' n, a n * x ^ n) ≠ 0 ∧
        HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n)
          (∑' n, a n * x ^ n)⁻¹ := by
  intro a ρ hρ ha0 hs
  set x0 : ℂ := ((ρ / 2 : ℝ) : ℂ) with hx0def
  have hx0 : ‖x0‖ = ρ / 2 := by
    rw [hx0def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum := hs x0 (by rw [hx0]; linarith)
  have htend := hsum.tendsto_atTop_zero.norm
  obtain ⟨M, hM⟩ := htend.bddAbove_range
  set R : ℝ := 2 / ρ with hRdef
  have hR : 0 < R := by positivity
  have hMa : ∀ n, ‖a n‖ ≤ M * R ^ n := by
    intro n
    have h1 : ‖a n * x0 ^ n‖ ≤ M := hM ⟨n, rfl⟩
    rw [norm_mul, norm_pow, hx0] at h1
    have h2 : (ρ / 2) ^ n * R ^ n = 1 := by
      rw [← mul_pow, hRdef, div_mul_div_comm, mul_comm ρ 2, div_self (by positivity), one_pow]
    calc ‖a n‖ = ‖a n‖ * (ρ / 2) ^ n * R ^ n := by rw [mul_assoc, h2, mul_one]
      _ ≤ M * R ^ n := by gcongr
  have hA0 : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 (by simpa using hMa 0)
  set K := R * (1 + M / ‖a 0‖) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨min (ρ / 2) K⁻¹, by positivity, ?_⟩
  intro x hx
  have hx1 : ‖x‖ < ρ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ < K⁻¹ := lt_of_lt_of_le hx (min_le_right _ _)
  have hRx : R * ‖x‖ < 1 := by
    rw [hRdef, div_mul_eq_mul_div, div_lt_one hρ]; linarith
  have hKx : K * ‖x‖ < 1 := by
    have := mul_lt_mul_of_pos_left hx2 hK
    rwa [mul_inv_cancel₀ hK.ne'] at this
  have hsa : Summable fun n => ‖a n * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hRx).mul_left M)
    rw [norm_mul, norm_pow]
    calc ‖a n‖ * ‖x‖ ^ n ≤ M * R ^ n * ‖x‖ ^ n := by gcongr; exact hMa n
      _ = M * (R * ‖x‖) ^ n := by ring
  have hsb : Summable fun n => ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hKx).mul_left ‖a 0‖⁻¹)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ * ‖x‖ ^ n
        ≤ ‖a 0‖⁻¹ * K ^ n * ‖x‖ ^ n := by
          gcongr; exact coeff_inv_norm_le a M R hR ha0 hMa n
      _ = ‖a 0‖⁻¹ * (K * ‖x‖) ^ n := by ring_nf
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; exact ha0
  have hc : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2) =
        (if n = 0 then 1 else 0) := by
    intro n
    have h := congrArg (PowerSeries.coeff n) (PowerSeries.mul_inv_cancel (PowerSeries.mk a) hc0)
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    calc ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2)
        = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 (PowerSeries.mk a) *
            PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹) * x ^ n := by
          refine Finset.sum_congr rfl (fun kl hkl => ?_)
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
          rw [← hkl, pow_add, PowerSeries.coeff_mk]; ring
      _ = (if n = 0 then 1 else 0) := by
          rw [← Finset.sum_mul, h]; split_ifs with hn <;> simp [hn]
  have key : (∑' n, a n * x ^ n) * (∑' n, PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) = 1 := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb, tsum_congr hc]
    exact tsum_ite_eq 0 1
  refine ⟨left_ne_zero_of_mul_eq_one key, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right key]
  exact (Summable.of_norm hsb).hasSum

end PowerSeriesInv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergentStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_powerSeries_inv_of_convergent : ∀ (a : ℕ → ℂ) (ρ : ℝ), 0 < ρ → a 0 ≠ 0 → (∀ x : ℂ, ‖x‖ < ρ → Summable fun n => a n * x ^ n) → ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ x : ℂ, ‖x‖ < ρ' → (∑' n, a n * x ^ n) ≠ 0 ∧ HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) (∑' n, a n * x ^ n)⁻¹ := by
  first | exact @GlobalTheory.PowerSeriesInv.hasSum_inv | exact GlobalTheory.PowerSeriesInv.hasSum_inv | (intros; apply GlobalTheory.PowerSeriesInv.hasSum_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSer
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fnShape : ∀ (Ω : Type) [Field Ω] (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → ∃ (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω), 0 < N ∧ a 0 ≠ 0 ∧ (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0 := by
  intro Ω _ h hD h0
  obtain ⟨N, hN, hd⟩ := hD
  have hc : h.coeff h.order ≠ 0 := fun e => h0 (HahnSeries.coeff_order_eq_zero.mp e)
  obtain ⟨n₀, hn₀⟩ := hd _ hc
  refine ⟨N, n₀, fun k => h.coeff (((n₀ + k : ℤ) : ℚ) / N), hN, ?_, fun k => rfl, ?_⟩
  · simpa [← hn₀] using hc
  · intro r hr
    by_contra hne
    obtain ⟨n, rfl⟩ := hd r hne
    have hle : h.order ≤ (n : ℚ) / N := HahnSeries.order_le_of_coeff_ne_zero hne
    rw [hn₀] at hle
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have : (n₀ : ℚ) ≤ n := by
      have := (div_le_div_iff_of_pos_right hNq).mp hle
      exact this
    have hnn : n₀ ≤ n := by exact_mod_cast this
    apply hr (n - n₀).toNat
    congr 2
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSerStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries : ∀ (Ω : Type) [Field Ω] (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → ∃ (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω), 0 < N ∧ a 0 ≠ 0 ∧ (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0 := by
  first | exact @GlobalTheory.fnShape | exact GlobalTheory.fnShape | (intros; apply GlobalTheory.fnShape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperations
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperations
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem den_scale_left {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((N * M : ℕ) : ℚ) := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * M, ?_⟩
  have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  rw [mul_div_mul_right _ _ this]

theorem den_scale_right {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((M * N : ℕ) : ℚ) := by
  rw [Nat.mul_comm]; exact den_scale_left hM h

theorem den_union {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h')
    (x : HahnSeries ℚ Ω) (hx : x.support ⊆ h.support ∪ h'.support) : Den x := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  rcases hx hr with h1 | h1
  · have := den_scale_left (M := N') hN' (H r h1)
    simpa using this
  · have := den_scale_right (M := N) hN (H' r h1)
    simpa using this

theorem den_mul {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h') :
    Den (h * h') := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  have hs := HahnSeries.support_mul_subset (x := h) (y := h') hr
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
  obtain ⟨n, rfl⟩ := H a ha
  obtain ⟨m, rfl⟩ := H' b hb
  refine ⟨n * N' + m * N, ?_⟩
  have h1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (N' : ℚ) ≠ 0 := by exact_mod_cast hN'.ne'
  push_cast
  field_simp

theorem den_single {Ω : Type} [Field Ω] (r : ℚ) (c : Ω) : Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  refine ⟨r.den, r.den_pos, fun s hs => ⟨r.num, ?_⟩⟩
  rw [HahnSeries.coeff_single] at hs
  split_ifs at hs with hsr
  · rw [hsr]; exact (Rat.num_div_den r).symm
  · exact (hs rfl).elim

theorem den_ring : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  intro Ω _
  refine ⟨fun h h' hh hh' => ⟨den_union hh hh' _ (HahnSeries.support_add_subset h h'),
    den_union hh hh' _ (HahnSeries.support_sub_subset h h'), den_mul hh hh'⟩, fun r c => den_single r c⟩

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperationsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCommonExponentDenominator_ring_operations : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  first | exact @GlobalTheory.FN.den_ring | exact GlobalTheory.FN.den_ring | (intros; apply GlobalTheory.FN.den_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZero
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hsne_re (N : ℕ) (z : ℂ) :
    (2 * Real.pi * Complex.I * z / N).re = -(2 * Real.pi * z.im / N) := by
  have : (2 * Real.pi * Complex.I * z / N) = ((2 * Real.pi / N : ℝ) : ℂ) * (Complex.I * z) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  simp [Complex.mul_re]
  ring

theorem fn_hsne_pre (N : ℕ) (hN : 0 < N) (C : ℝ) (x : ℂ) (hx : x ≠ 0)
    (hxr : ‖x‖ < Real.exp (-(2 * Real.pi * C / N))) :
    ∃ z : ℂ, C < z.im ∧ Complex.exp (2 * Real.pi * Complex.I * z / N) = x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi), ?_, ?_⟩
  · have hlog : Real.log ‖x‖ < -(2 * Real.pi * C / N) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx)]; exact hxr
    have him : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)).im
        = -(N * Real.log ‖x‖) / (2 * Real.pi) := by
      have : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi))
          = ((-(N : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * Complex.log x) := by
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]
      simp [Complex.mul_im, Complex.log_re]
      ring
    rw [him]
    rw [lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hlog hNr
    have e : (N : ℝ) * -(2 * Real.pi * C / N) = -(C * (2 * Real.pi)) := by
      field_simp
    nlinarith [this, e]
  · have : 2 * Real.pi * Complex.I * (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)) / N
        = Complex.log x := by
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      field_simp
      ring_nf
      rw [Complex.I_sq]; ring
    rw [this, Complex.exp_log hx]

end GlobalTheory

namespace GlobalTheory

theorem fn_hasSum_ne_zero : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω),
    Den h → h ≠ 0 → HS ε C φ h → ∃ C' : ℝ, ∀ z : ℂ, C' < z.im → φ z ≠ 0 := by
  intro Ω _ ε C φ h hD h0 hS
  obtain ⟨N, n₀, a, hN, ha0, ha, hz⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  set b : ℕ → ℂ := fun k => ε (a k) with hb
  have hb0 : b 0 ≠ 0 := by
    simp only [hb]; exact (map_ne_zero ε).mpr ha0

  have key : ∀ z : ℂ, C < z.im →
      HasSum (fun k : ℕ => b k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k)
        (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := fun z hzC =>
    (fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN ha hz).mp (hS z hzC)
  set ρ : ℝ := Real.exp (-(2 * Real.pi * C / N)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hsum : ∀ x : ℂ, ‖x‖ < ρ → Summable fun n => b n * x ^ n := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      have : n ≠ 0 := by simpa using hn
      simp [zero_pow this]
    · obtain ⟨z, hzC, hzx⟩ := fn_hsne_pre N hN C x hx0 hx
      have := key z hzC
      rw [hzx] at this
      exact this.summable
  obtain ⟨ρ', hρ'0, hρ'⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent b ρ hρ0 hb0 hsum
  refine ⟨max C (-(N * Real.log ρ') / (2 * Real.pi)), fun z hzi => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hzi
  have hz2 : -(N * Real.log ρ') / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hzi
  set x := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hxn : ‖x‖ < ρ' := by
    rw [hxdef, Complex.norm_exp, fn_hsne_re]
    rw [← Real.exp_log hρ'0, Real.exp_lt_exp]
    rw [div_lt_iff₀ (by positivity)] at hz2
    rw [neg_lt, lt_div_iff₀ hNr]
    nlinarith [hz2]
  have hne := (hρ' x hxn).1
  rw [(key z hzC).tsum_eq] at hne
  intro hφ
  apply hne
  rw [hφ, zero_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZeroStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_im_gt_ne_zero_of_hs : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → ∃ C' : ℝ, ∀ z : ℂ, C' < z.im → φ z ≠ 0 := by
  first | exact @GlobalTheory.fn_hasSum_ne_zero | exact GlobalTheory.fn_hasSum_ne_zero | (intros; apply GlobalTheory.fn_hasSum_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEq
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hs_uniq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  intro Ω _ ε C C' C'' φ φ' h h' hd hd' hs hs' heq
  obtain ⟨hmono, hadd, -, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  set C₀ : ℝ := max C (max C' C'') with hC₀
  have h1 : HS ε C₀ φ h := hmono C C₀ φ h (le_max_left _ _) hs
  have h2 : HS ε C₀ φ' h' := hmono C' C₀ φ' h' (le_trans (le_max_left _ _) (le_max_right _ _)) hs'
  have h3 : HS ε C₀ (φ - φ') (h - h') := ((hadd C₀ φ φ' h h') h1 h2).2
  have h4 : HS ε C₀ (fun _ => (0 : ℂ)) (h - h') := by
    refine hcongr C₀ (φ - φ') (fun _ => 0) (h - h') ?_ h3
    intro z hz
    have : C'' < z.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz
    simp [heq z this]
  have hdd : Den (h - h') := (((GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω).1 h h' hd hd').2.1)
  by_contra hne
  have hne' : h - h' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_im_gt_ne_zero_of_hs Ω ε C₀ (fun _ => (0 : ℂ)) (h - h') hdd hne' h4
  exact hD ((D + 1 : ℝ) * Complex.I) (by simp) rfl

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEqStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  first | exact @GlobalTheory.FN.hs_uniq | exact GlobalTheory.FN.hs_uniq | (intros; apply GlobalTheory.FN.hs_uniq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConverges
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConverges
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hahnSeries_inv_converges : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → Den h⁻¹ ∧ ∃ C' : ℝ, HS ε C' φ⁻¹ h⁻¹ := by
  intro Ω _ ε C φ h hD hne hS
  obtain ⟨N, n₀, a, hN, ha0, hcoef, hzero⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD hne
  obtain ⟨Φ, hΦ1, hΦ0⟩ := GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN
  set p : PowerSeries Ω := PowerSeries.mk a with hpdef
  have hp0 : PowerSeries.constantCoeff p ≠ 0 := by simpa [p] using ha0
  set q : PowerSeries Ω := p⁻¹ with hqdef
  have hdiv : ∀ (r : ℚ) (m : ℤ) (k : ℕ), r - (m : ℚ) / N = (k : ℚ) / N ↔ r = ((m + k : ℤ) : ℚ) / N := by
    intro r m k
    rw [sub_eq_iff_eq_add]
    push_cast
    constructor <;> intro hr <;> rw [hr] <;> ring
  have hh : h = HahnSeries.single ((n₀ : ℚ) / N) (1 : Ω) * Φ p := by
    ext r
    rw [HahnSeries.coeff_single_mul, one_mul]
    by_cases hr : ∃ k : ℕ, r = ((n₀ + k : ℤ) : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hcoef k, (hdiv _ n₀ k).2 rfl, hΦ1]
      simp [p]
    · push_neg at hr
      rw [hzero r hr, hΦ0]
      intro k hk
      exact hr k ((hdiv r n₀ k).1 hk)
  set g : HahnSeries ℚ Ω := HahnSeries.single (((-n₀ : ℤ) : ℚ) / N) (1 : Ω) * Φ q with hgdef
  have hg : h⁻¹ = g := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hh, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hqdef,
      PowerSeries.mul_inv_cancel _ hp0, map_one, mul_one, mul_one]
    have : (n₀ : ℚ) / N + ((-n₀ : ℤ) : ℚ) / N = 0 := by push_cast; ring
    rw [this, HahnSeries.single_zero_one]
  have hgc : ∀ k : ℕ, g.coeff (((-n₀ + k : ℤ) : ℚ) / N) = PowerSeries.coeff k q := by
    intro k
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul, (hdiv _ (-n₀) k).2 rfl, hΦ1]
  have hgz : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((-n₀ + k : ℤ) : ℚ) / N) → g.coeff r = 0 := by
    intro r hr
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul]
    apply hΦ0
    intro k hk
    exact hr k ((hdiv r (-n₀) k).1 hk)
  refine ⟨?_, ?_⟩
  · rw [hg]
    refine ⟨N, hN, fun r hr => ?_⟩
    by_contra H
    push_neg at H
    exact hr (hgz r fun k hk => H _ hk)

  set A : ℕ → ℂ := fun k => ε (a k) with hAdef
  have hA0 : A 0 ≠ 0 := (map_ne_zero ε).2 ha0
  have hnorm : ∀ z : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * z / N)‖ = Real.exp (-(2 * Real.pi * z.im / N)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    have hNc : ((N : ℂ)) = ((N : ℝ) : ℂ) := by push_cast; rfl
    rw [hNc, Complex.div_ofReal_re]
    simp
    ring
  have hred : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => A k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := by
    intro z hz
    exact (GlobalTheory.fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN hcoef hzero).1 (hS z hz)
  set t0 : ℝ := max C 0 + 1 with ht0
  set z0 : ℂ := (t0 : ℂ) * Complex.I with hz0
  have hz0im : C < z0.im := by
    simp [z0, t0]
    have := le_max_left C 0
    linarith
  set x0 : ℂ := Complex.exp (2 * Real.pi * Complex.I * z0 / N) with hx0
  have hx0pos : 0 < ‖x0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hsum0 := hred z0 hz0im
  have hconv : ∀ x : ℂ, ‖x‖ < ‖x0‖ → Summable fun n => A n * x ^ n := fun x hx =>
    summable_powerSeries_of_norm_lt hsum0.tendsto_sum_nat.cauchySeq hx
  obtain ⟨ρ', hρ', hmain⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent A ‖x0‖ hx0pos hA0 hconv
  have hmk : PowerSeries.mk A = PowerSeries.map ε p := by
    ext k
    simp [p, A]
  have hmapinv : PowerSeries.map ε q = (PowerSeries.mk A)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · rw [hmk, ← map_mul, hqdef, PowerSeries.inv_mul_cancel _ hp0, map_one]
    · simpa using hA0
  refine ⟨max C ((N : ℝ) * |Real.log ρ'| / (2 * Real.pi)), fun z hz => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  have hzL : (N : ℝ) * |Real.log ρ'| / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hx : ‖x‖ < ρ' := by
    rw [hxdef, hnorm, ← Real.exp_log hρ']
    apply Real.exp_lt_exp.2
    have hpi : 0 < 2 * Real.pi := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hpi] at hzL
    have h1 : |Real.log ρ'| < 2 * Real.pi * z.im / N := by
      rw [lt_div_iff₀ hNr]; linarith
    have h2 := neg_abs_le (Real.log ρ')
    have h3 : -(2 * Real.pi * z.im / N) = -(2 * Real.pi * z.im / N) := rfl
    linarith
  obtain ⟨hS0, hinv⟩ := hmain x hx
  have htsum : (∑' n, A n * x ^ n) = φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)) :=
    (hred z hzC).tsum_eq
  rw [hg]
  apply (GlobalTheory.fn_hasSum_reindex_nat Ω ε g N (-n₀) (fun k => PowerSeries.coeff k q) z (φ⁻¹ z) hN hgc hgz).2
  convert (preTransparency := .reducible) hinv using 1
  · funext k
    rw [← hmapinv, PowerSeries.coeff_map]
  · rw [htsum, mul_inv, ← Complex.exp_neg, Pi.inv_apply]
    congr 2
    push_cast
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConvergesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.den_inv_and_hs_inv_of_hs : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → Den h⁻¹ ∧ ∃ C' : ℝ, HS ε C' φ⁻¹ h⁻¹ := by
  first | exact @GlobalTheory.fn_hahnSeries_inv_converges | exact GlobalTheory.fn_hahnSeries_inv_converges | (intros; apply GlobalTheory.fn_hahnSeries_inv_converges <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveIm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveIm
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem upperHalfPlane_eq_zero_of_vanish_high :
    ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  intro f C hf hC
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have han := hd.analyticOnNhd hopen
  have hpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((|C| + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀im : z₀.im = |C| + 1 := by simp [hz₀]
  have hmem : z₀ ∈ {z : ℂ | 0 < z.im} := by
    show 0 < z₀.im
    rw [hz₀im]; positivity
  have hev : (f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds z₀] 0 := by
    have hopen2 : IsOpen {z : ℂ | max C 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hin : z₀ ∈ {z : ℂ | max C 0 < z.im} := by
      show max C 0 < z₀.im
      rw [hz₀im]
      have := le_abs_self C
      have := abs_nonneg C
      exact max_lt (by linarith) (by linarith)
    filter_upwards [hopen2.mem_nhds hin] with z hz
    have hz' : max C 0 < z.im := hz
    have h0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz'
    have h1 : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz'
    simp only [Function.comp_apply, Pi.zero_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h0]
    exact hC _ h1
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hmem hev
  funext τ
  have := heq (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveImStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im : ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  first | exact @GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | exact GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | (intros; apply GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMul
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNProd

theorem hs_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  intro Ω _ ε C φ ψ h h' H H' z hz
  set e : ℚ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with he
  set a : ℚ → ℂ := fun r => ε (h.coeff r) * e r with ha
  set b : ℚ → ℂ := fun r => ε (h'.coeff r) * e r with hb
  have hA : HasSum a (φ z) := H z hz
  have hB : HasSum b (ψ z) := H' z hz
  have hAn : Summable fun r => ‖a r‖ := summable_norm_iff.2 hA.summable
  have hBn : Summable fun r => ‖b r‖ := summable_norm_iff.2 hB.summable
  have hP : HasSum (fun p : ℚ × ℚ => a p.1 * b p.2) (φ z * ψ z) :=
    hA.mul hB (summable_mul_of_summable_norm hAn hBn)
  have hF := hP.tsum_fiberwise (fun p : ℚ × ℚ => p.1 + p.2)
  refine hF.congr_fun ?_
  intro s
  have hexp : ∀ p : ℚ × ℚ, p.1 + p.2 = s → a p.1 * b p.2 = ε (h.coeff p.1) * ε (h'.coeff p.2) * e s := by
    intro p hp
    simp only [ha, hb, he, ← hp]
    have : Complex.exp (2 * Real.pi * Complex.I * ((p.1 + p.2 : ℚ) : ℂ) * z) =
        Complex.exp (2 * Real.pi * Complex.I * (p.1 : ℂ) * z) * Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [tsum_subtype (f := fun p : ℚ × ℚ => a p.1 * b p.2)]
  rw [tsum_eq_sum (s := Finset.antidiagonal h.isPWO_support h'.isPWO_support s)]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [HahnSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [Set.indicator_of_mem (by simpa using hp.2.2)]
      exact (hexp p hp.2.2).symm
  · intro p hp
    by_cases hs : p.1 + p.2 = s
    · rw [Set.indicator_of_mem (by simpa using hs), hexp p hs]
      rw [Finset.mem_antidiagonal] at hp
      simp only [HahnSeries.mem_support, not_and] at hp
      by_cases h1 : h.coeff p.1 = 0
      · simp [h1]
      · have h2 : h'.coeff p.2 = 0 := by
          by_contra h2; exact hp h1 h2 hs
        simp [h2]
    · exact Set.indicator_of_notMem (by simpa using hs) _

end GlobalTheory.FNProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMulStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionSumAbove_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  first | exact @GlobalTheory.FNProd.hs_mul | exact GlobalTheory.FNProd.hs_mul | (intros; apply GlobalTheory.FNProd.hs_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExp

theorem up_add (f f' : ℍ → ℂ) : up (f + f') = up f + up f' := rfl
theorem up_sub (f f' : ℍ → ℂ) : up (f - f') = up f - up f' := rfl
theorem up_mul (f f' : ℍ → ℂ) : up (f * f') = up f * up f' := rfl
theorem up_inv (f : ℍ → ℂ) : up f⁻¹ = (up f)⁻¹ := rfl

theorem exp_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  intro Ω _ ε
  obtain ⟨hden, hsing⟩ := GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω
  obtain ⟨hmono, hadd, hmon, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro f f' h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    obtain ⟨d1, d2, d3⟩ := hden h h' hd hd'
    have e1 : HS ε (max C C') (up f) h := hmono _ _ _ _ (le_max_left _ _) hC
    have e2 : HS ε (max C C') (up f') h' := hmono _ _ _ _ (le_max_right _ _) hC'
    obtain ⟨s1, s2⟩ := hadd _ _ _ _ _ e1 e2
    refine ⟨⟨d1, max C C', ?_⟩, ⟨d2, max C C', ?_⟩, ⟨d3, max C C', ?_⟩⟩
    · rw [up_add]; exact s1
    · rw [up_sub]; exact s2
    · rw [up_mul]; exact GlobalTheory.T.hasQExpansionSumAbove_mul Ω ε _ _ _ _ _ e1 e2
  · rintro f h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    exact GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq Ω ε C C' 0 (up f) (up f) h h' hd hd' hC hC' (fun _ _ => rfl)
  · intro c
    have hC : HahnSeries.C c = (HahnSeries.single (0 : ℚ) c : HahnSeries ℚ Ω) := HahnSeries.C_apply c
    rw [hC]
    refine ⟨hsing 0 c, 0, ?_⟩
    refine hcongr 0 _ _ _ ?_ (hmon 0 0 c)
    intro z _
    simp [up]
  · rintro f hf ⟨_, C, hC⟩
    apply GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im f C hf
    intro τ hτ
    have hz := hC (τ : ℂ) (by simpa using hτ)
    have h0 : (fun r : ℚ => ε ((0 : HahnSeries ℚ Ω).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))) = fun _ => 0 := by
      funext r; simp
    rw [h0] at hz
    have := hz.unique hasSum_zero
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  · rintro f h hne ⟨hd, C, hC⟩
    obtain ⟨d, C', hC'⟩ := GlobalTheory.T.den_inv_and_hs_inv_of_hs Ω ε C (up f) h hd hne hC
    exact ⟨d, C', by rw [up_inv]; exact hC'⟩

end GlobalTheory.FNExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_properties : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  first | exact @GlobalTheory.FNExp.exp_props | exact GlobalTheory.FNExp.exp_props | (intros; apply GlobalTheory.FNExp.exp_props <;> assumption)
end
