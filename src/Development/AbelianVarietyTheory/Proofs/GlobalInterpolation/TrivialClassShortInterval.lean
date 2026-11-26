module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyPsiWithExceptionalZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRayClassLFunctionRealZeroFarFromOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionUniqueSimpleExceptionalZero
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionUniqueSimpleExceptionalZero
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RealZero

theorem order_ne_top (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ} (hz : 1 / 2 < z.re) :
    analyticOrderAt (𝓕.F χ) z ≠ ⊤ := by
  have hA := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1
  have hU : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 : ℝ) / 2 < (2 : ℂ).re
    norm_num
  have hF2 : 𝓕.F χ 2 ≠ 0 := (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 (by norm_num)).2.2.1
  have h2top : analyticOrderAt (𝓕.F χ) 2 ≠ ⊤ := by
    rw [(hA 2 h2).analyticOrderAt_eq_zero.mpr hF2]
    exact ENat.zero_ne_top
  exact hA.analyticOrderAt_ne_top_of_isPreconnected hU h2 hz h2top

theorem le_order (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ} (hz : 1 / 2 < z.re) (n : ℕ)
    (hn : ∀ i < n, iteratedDeriv i (𝓕.F χ) z = 0) :
    n ≤ analyticOrderNatAt (𝓕.F χ) z := by
  have hA := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1 z hz
  have h := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr hn
  rw [← Nat.cast_analyticOrderNatAt (order_ne_top 𝓕 χ hz)] at h
  exact_mod_cast h

theorem re_le_one (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ}
    (hz : 𝓕.F χ z = 0) : z.re ≤ 1 := by
  by_contra h
  exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ z (not_le.mp h)).2.2.1 hz

private lemma sum_real_zeros_div_sub_le_re_finsum_div_sub (m : ℂ → ℕ) (σ : ℝ) (S : Set ℂ) (hS : S.Finite) (T : Finset ℝ)
    (hTS : ∀ β ∈ T, (β : ℂ) ∈ S) (hre : ∀ w ∈ S, w.re < σ) :
    ∑ β ∈ T, (m β : ℝ) / (σ - β) ≤ (∑ᶠ w ∈ S, (m w : ℂ) / ((σ : ℂ) - w)).re := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Complex.re_sum]
  have hnn : ∀ w ∈ hS.toFinset, 0 ≤ ((m w : ℂ) / ((σ : ℂ) - w)).re := by
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have h1 := hre w hw
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
      Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Complex.normSq_nonneg _)
  have himg : ∑ β ∈ T, (m β : ℝ) / (σ - β)
      = ∑ w ∈ T.image (fun β : ℝ => (β : ℂ)), ((m w : ℂ) / ((σ : ℂ) - w)).re := by
    rw [Finset.sum_image (fun a _ b _ h => Complex.ofReal_injective h)]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    have e : (m β : ℂ) / ((σ : ℂ) - β) = (((m β : ℝ) / (σ - β) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
    rw [e, Complex.ofReal_re]
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w hw _ => hnn w hw)
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨β, hβ, rfl⟩ := hw
  rw [Set.Finite.mem_toFinset]
  exact hTS β hβ

private lemma neg_re_le_neg_add_of_norm_sub_le_of_le_re (A B : ℂ) (x y : ℝ) (h : ‖A - B‖ ≤ x) (hy : y ≤ B.re) :
    -A.re ≤ -y + x := by
  have h1 := Complex.re_le_norm (B - A)
  rw [norm_sub_rev, Complex.sub_re] at h1
  linarith

theorem exists_bound : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ),
    ∀ σ : ℝ, 1 < σ → σ ≤ 7 / 4 → ∀ T : Finset ℝ,
    (∀ β ∈ T, 3 / 4 ≤ β ∧ 𝓕.F χ β = 0) →
    (LSeries (𝓕.lamChi χ) σ).re ≤ (if χ = 1 then 1 / (σ - 1) else 0) + C * 𝓕.ell 0
      - ∑ β ∈ T, (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) := by
  obtain ⟨C, hC, hmain⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  refine ⟨C, hC, fun 𝓕 χ σ hσ1 hσ2 T hT => ?_⟩
  obtain ⟨hfin, -, happ⟩ := hmain 𝓕 χ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hfin happ
  have hs1 : 1 < (σ : ℂ).re := by simpa using hσ1
  obtain ⟨-, -, hFs, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ σ hs1
  have hnear : ‖(σ : ℂ) - 5 / 4‖ ≤ 1 / 2 := by
    have e : (σ : ℂ) - 5 / 4 = ((σ - 5 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := happ σ hnear hFs
  have hsum := sum_real_zeros_div_sub_le_re_finsum_div_sub (analyticOrderNatAt (𝓕.F χ)) σ _ hfin T ?_ ?_
  · have h2 := neg_re_le_neg_add_of_norm_sub_le_of_le_re _ _ _ _ hE hsum
    rw [← hL, Complex.add_re, Complex.neg_re]
    split_ifs with h1
    · have e : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
        rw [show (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) by
          rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one], Complex.ofReal_re]
      rw [e]
      linarith
    · rw [Complex.zero_re]
      linarith
  · intro β hβ
    obtain ⟨h34, hz⟩ := hT β hβ
    have hb1 : β ≤ 1 := by simpa using re_le_one 𝓕 χ hz
    refine ⟨?_, hz⟩
    have e : (β : ℂ) - 5 / 4 = ((β - 5 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · intro w hw
    have := re_le_one 𝓕 χ hw.2
    linarith

private lemma term_lemma_3 {c ℓ σ β : ℝ} (m : ℝ) (hm : 0 ≤ m) (hc : 0 < c) (hℓ : 0 < ℓ)
    (hσ : σ = 1 + 2 * c / ℓ) (h1 : 1 - c / ℓ ≤ β) (h2 : β ≤ 1) :
    m * (ℓ / (3 * c)) ≤ m / (σ - β) := by
  subst hσ
  have h2c : 0 < 2 * c / ℓ := by positivity
  have hpos : 0 < 1 + 2 * c / ℓ - β := by linarith
  have hle : 1 + 2 * c / ℓ - β ≤ 3 * c / ℓ := by
    have : 3 * c / ℓ = c / ℓ + 2 * c / ℓ := by ring
    linarith
  have key := one_div_le_one_div_of_le hpos hle
  rw [one_div_div] at key
  rw [div_eq_mul_one_div m]
  exact mul_le_mul_of_nonneg_left key hm

private lemma false_of_le_of_mul_hundred_mul_add_one_eq_one {C c ℓ X : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) (hcC : c * (100 * (C + 1)) = 1)
    (hc : 0 < c) (hX : 2 * (ℓ / (3 * c)) ≤ X) (h : 0 ≤ ℓ / (2 * c) + 4 * (C * ℓ) - X) : False := by
  have h1c : 1 / c = 100 * (C + 1) := by
    rw [eq_comm, eq_div_iff hc.ne']
    linear_combination hcC
  have e2 : ℓ / (2 * c) = ℓ / 2 * (1 / c) := by rw [div_mul_div_comm, mul_one]
  have e3 : ℓ / (3 * c) = ℓ / 3 * (1 / c) := by rw [div_mul_div_comm, mul_one]
  rw [e3, h1c] at hX
  rw [e2, h1c] at h
  nlinarith [mul_pos hℓ hC]

theorem main : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), χ * χ = 1 → ψ * ψ = 1 → 3 / 4 ≤ β → 3 / 4 ≤ β' → 1 - c / 𝓕.ell 0 ≤ β → 1 - c / 𝓕.ell 0 ≤ β' → 𝓕.F χ β = 0 → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
  obtain ⟨C, hC, hb⟩ := exists_bound
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / (100 * (C + 1)) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcC : c * (100 * (C + 1)) = 1 := by
    rw [hcdef, one_div, inv_mul_cancel₀ (by positivity)]
  refine ⟨c, hc, ?_⟩
  intro 𝓕 χ ψ β β' hχ hψ hβ hβ' hc1 hc1' hz hz'
  have hℓ2 : 2 < 𝓕.ell 0 := 𝓕.two_lt_ell 0
  have hℓ : 0 < 𝓕.ell 0 := by linarith
  have hCℓ : 0 < C * 𝓕.ell 0 := mul_pos hC hℓ
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 1 + 2 * c / 𝓕.ell 0 := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by
    have : 0 < 2 * c / 𝓕.ell 0 := by positivity
    linarith
  have hσ2 : σ ≤ 7 / 4 := by
    have hc' : c < 1 / 100 := by nlinarith [mul_pos hc hC]
    have : 2 * c / 𝓕.ell 0 ≤ 3 / 4 := by
      rw [div_le_iff₀ hℓ]
      linarith
    linarith
  have hpole : 1 / (σ - 1) = 𝓕.ell 0 / (2 * c) := by
    rw [hσdef, add_sub_cancel_left, one_div_div]
  have hq : 0 < 𝓕.ell 0 / (3 * c) := by positivity
  have tb : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ) (k : ℕ), 3 / 4 ≤ x → 1 - c / 𝓕.ell 0 ≤ x →
      𝓕.F φ x = 0 → (∀ i < k, iteratedDeriv i (𝓕.F φ) x = 0) →
      k * (𝓕.ell 0 / (3 * c)) ≤ (analyticOrderNatAt (𝓕.F φ) x : ℝ) / (σ - x) := by
    intro φ x k hx hxc hx0 hk
    have hx2 : 1 / 2 < (x : ℂ).re := by
      rw [Complex.ofReal_re]
      linarith
    have hx1 : x ≤ 1 := by simpa using re_le_one 𝓕 φ hx0
    have hm : (k : ℝ) ≤ analyticOrderNatAt (𝓕.F φ) x := by
      exact_mod_cast le_order 𝓕 φ hx2 k hk
    have ht := term_lemma_3 (analyticOrderNatAt (𝓕.F φ) x : ℝ) (by positivity) hc hℓ hσdef hxc hx1
    nlinarith
  have d1 : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 𝓕.F φ x = 0 → ∀ i < 1, iteratedDeriv i (𝓕.F φ) x = 0 := by
    intro φ x h0 i hi
    interval_cases i
    simpa using h0
  have tβ := tb χ β 1 hβ hc1 hz (d1 χ β hz)
  have tβ' := tb ψ β' 1 hβ' hc1' hz' (d1 ψ β' hz')
  push_cast at tβ tβ'
  have sg : ∀ (φ : AddChar 𝓕.G ℂ) (x : ℝ), 3 / 4 ≤ x → 𝓕.F φ x = 0 →
      ∀ y ∈ ({x} : Finset ℝ), 3 / 4 ≤ y ∧ 𝓕.F φ y = 0 := by
    intro φ x hx h0 y hy
    rw [Finset.mem_singleton] at hy
    rw [hy]
    exact ⟨hx, h0⟩
  by_cases hcp : χ = ψ
  · subst hcp
    refine ⟨rfl, ?_⟩
    by_contra hbad
    obtain ⟨T, hT, hXT⟩ : ∃ T : Finset ℝ, (∀ x ∈ T, 3 / 4 ≤ x ∧ 𝓕.F χ x = 0) ∧
        2 * (𝓕.ell 0 / (3 * c)) ≤ ∑ x ∈ T, (analyticOrderNatAt (𝓕.F χ) x : ℝ) / (σ - x) := by
      by_cases hne : β = β'
      · have hd : deriv (𝓕.F χ) β = 0 := by
          by_contra hd
          exact hbad ⟨hne, hd⟩
        refine ⟨{β}, sg χ β hβ hz, ?_⟩
        rw [Finset.sum_singleton]
        have h2 := tb χ β 2 hβ hc1 hz (by
          intro i hi
          interval_cases i
          · simpa using hz
          · simpa using hd)
        exact_mod_cast h2
      · refine ⟨{β, β'}, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨hβ, hz⟩
          · exact ⟨hβ', hz'⟩
        · rw [Finset.sum_pair hne]
          linarith
    by_cases h1 : χ = 1
    · subst h1
      have hB := hb 𝓕 1 σ hσ1 hσ2 T hT
      rw [if_pos rfl, hpole] at hB
      have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 1 1 σ 0 hσ1).2.1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)
    · have hB := hb 𝓕 χ σ hσ1 hσ2 T hT
      rw [if_neg h1] at hB
      have hB1 := hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)
      rw [if_pos rfl, hpole, Finset.sum_empty] at hB1
      have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc hXT (by linarith)
  · exfalso
    by_cases h1 : χ = 1
    · subst h1
      have hψ1 : ψ ≠ 1 := fun h => hcp h.symm
      have hB1 := hb 𝓕 1 σ hσ1 hσ2 {β} (sg 1 β hβ hz)
      rw [if_pos rfl, hpole, Finset.sum_singleton] at hB1
      have hBψ := hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')
      rw [if_neg hψ1, Finset.sum_singleton] at hBψ
      have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 ψ ψ σ 0 hσ1).2.2 hψ hψ).1
      exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F 1) β : ℝ) / (σ - β) +
        (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
    · by_cases h2 : ψ = 1
      · subst h2
        have hB1 := hb 𝓕 1 σ hσ1 hσ2 {β'} (sg 1 β' hβ' hz')
        rw [if_pos rfl, hpole, Finset.sum_singleton] at hB1
        have hBχ := hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)
        rw [if_neg h1, Finset.sum_singleton] at hBχ
        have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ σ 0 hσ1).2.2 hχ hχ).1
        exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) +
          (analyticOrderNatAt (𝓕.F 1) β' : ℝ) / (σ - β')) (by linarith) (by linarith)
      · have hχψ : χ * ψ ≠ 1 := by
          intro h
          apply hcp
          calc χ = χ * (ψ * ψ) := by rw [hψ, mul_one]
            _ = (χ * ψ) * ψ := (mul_assoc _ _ _).symm
            _ = ψ := by rw [h, one_mul]
        have hB1 := hb 𝓕 1 σ hσ1 hσ2 ∅ (by simp)
        rw [if_pos rfl, hpole, Finset.sum_empty] at hB1
        have hBχ := hb 𝓕 χ σ hσ1 hσ2 {β} (sg χ β hβ hz)
        rw [if_neg h1, Finset.sum_singleton] at hBχ
        have hBψ := hb 𝓕 ψ σ hσ1 hσ2 {β'} (sg ψ β' hβ' hz')
        rw [if_neg h2, Finset.sum_singleton] at hBψ
        have hBχψ := hb 𝓕 (χ * ψ) σ hσ1 hσ2 ∅ (by simp)
        rw [if_neg hχψ, Finset.sum_empty] at hBχψ
        have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ ψ σ 0 hσ1).2.2 hχ hψ).2
        exact false_of_le_of_mul_hundred_mul_add_one_eq_one hC hℓ hcC hc (X := (analyticOrderNatAt (𝓕.F χ) β : ℝ) / (σ - β) +
          (analyticOrderNatAt (𝓕.F ψ) β' : ℝ) / (σ - β')) (by linarith) (by linarith)

end GlobalTheory.Hk.RealZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionUniqueSimpleExceptionalZeroStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassLFunction_unique_simple_exceptional_zero : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), χ * χ = 1 → ψ * ψ = 1 → 3 / 4 ≤ β → 3 / 4 ≤ β' → 1 - c / 𝓕.ell 0 ≤ β → 1 - c / 𝓕.ell 0 ≤ β' → 𝓕.F χ β = 0 → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
  first | exact @GlobalTheory.Hk.RealZero.main | exact GlobalTheory.Hk.RealZero.main | (intros; apply GlobalTheory.Hk.RealZero.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionZeroFreeRegion
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionZeroFreeRegion
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.ZeroFree

theorem re_one_div (a b : ℝ) : (1 / ((a : ℂ) + b * I)).re = a / (a ^ 2 + b ^ 2) := by
  rw [one_div, inv_re, normSq_add_mul_I]
  simp

theorem re_le_one {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {w : ℂ} (hw : 𝓕.F χ w = 0) : w.re ≤ 1 := by
  by_contra h
  push_neg at h
  exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ w h).2.2.1 hw

theorem one_le_order {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {ρ : ℂ} (h : 1 / 2 < ρ.re)
    (hρ : 𝓕.F χ ρ = 0) : 1 ≤ analyticOrderNatAt (𝓕.F χ) ρ := by
  have hU := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1
  have hA : AnalyticAt ℂ (𝓕.F χ) ρ := hU ρ h
  have htop : analyticOrderAt (𝓕.F χ) ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have hc : Convex ℝ {s : ℂ | 1 / 2 < s.re} := convex_halfSpace_re_gt _
    have hE := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected h ht
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 h2).2.2.1 (hE (show (1 : ℝ) / 2 < (2 : ℂ).re by norm_num))
  have hz : analyticOrderAt (𝓕.F χ) ρ ≠ 0 := hA.analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hz
  rw [← Nat.cast_analyticOrderNatAt htop, h0]
  simp

theorem re_LSeries_le : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (a t P : ℝ),
    0 < a → a ≤ 1 / 2 → 0 ≤ P → (χ = 1 → a / (a ^ 2 + t ^ 2) ≤ P) → ∀ S : Finset ℂ,
    (∀ w ∈ S, ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0) →
    (LSeries (𝓕.lamChi χ) (((1 + a : ℝ) : ℂ) + t * I)).re
      ≤ P + C * 𝓕.ell t - ∑ w ∈ S, (1 / (((1 + a : ℝ) : ℂ) + t * I - w)).re := by
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.T.rayClassLFunction_logDeriv_local_formula
  refine ⟨C, hC, ?_⟩
  intro 𝓕 χ a t P ha ha2 hP hχ S hS
  obtain ⟨hfin, -, hD⟩ := hCb 𝓕 χ t
  set s : ℂ := ((1 + a : ℝ) : ℂ) + t * I with hs
  have hsre : s.re = 1 + a := by simp [hs]
  have hsre1 : 1 < s.re := by rw [hsre]; linarith
  obtain ⟨-, -, hFne, hL⟩ := GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ s hsre1
  have hsd : ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 := by
    have e : s - (5 / 4 + t * I) = ((a - 1 / 4 : ℝ) : ℂ) := by rw [hs]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hE := hD s hsd hFne
  have hfpos : ∀ w, 𝓕.F χ w = 0 → 0 ≤ (1 / (s - w)).re := by
    intro w hw
    rw [one_div, inv_re]
    apply div_nonneg _ (normSq_nonneg _)
    rw [sub_re, hsre]
    linarith [re_le_one hw]
  have hsum : (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0},
      (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)).re
      = ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, re_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [div_eq_mul_one_div, ← ofReal_natCast, re_ofReal_mul]
  have hSZ : ∑ w ∈ S, (1 / (s - w)).re
      ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
    calc ∑ w ∈ S, (1 / (s - w)).re
        ≤ ∑ w ∈ S, (analyticOrderNatAt (𝓕.F χ) w : ℝ) * (1 / (s - w)).re := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨hw1, hw2⟩ := hS w hw
          have hre : 1 / 2 < w.re := by
            have h1 := (abs_le.mp ((abs_re_le_norm _).trans hw1)).1
            simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h1
            norm_num at h1
            linarith
          have hm : (1 : ℝ) ≤ analyticOrderNatAt (𝓕.F χ) w := by
            exact_mod_cast one_le_order hre hw2
          nlinarith [hfpos w hw2]
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro w hw
            rw [Set.Finite.mem_toFinset]
            exact hS w hw
          · intro w hw _
            exact mul_nonneg (Nat.cast_nonneg _) (hfpos w ((Set.Finite.mem_toFinset hfin).mp hw).2)
  have hpole : (if χ = 1 then 1 / (s - 1) else 0 : ℂ).re ≤ P := by
    split_ifs with h1
    · have e : s - 1 = (a : ℂ) + t * I := by rw [hs]; push_cast; ring
      rw [e, re_one_div]
      exact hχ h1
    · simpa using hP
  rw [← hL, add_re, neg_re]
  have hre := (abs_le.mp ((abs_re_le_norm _).trans hE)).1
  rw [sub_re, hsum] at hre
  linarith

theorem one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  have := 𝓕.two_lt_ell t
  linarith

theorem ell_zero_le (𝓕 : LFam) (t : ℝ) : 𝓕.ell 0 ≤ 𝓕.ell t := by
  unfold LFam.ell
  have hB : (0 : ℝ) < 𝓕.B := by linarith [𝓕.B_ge]
  rw [abs_zero]
  apply Real.log_le_log
  · positivity
  · apply mul_le_mul_of_nonneg_left _ hB.le
    linarith [abs_nonneg t]

theorem ell_two_le (𝓕 : LFam) (t : ℝ) : 𝓕.ell (2 * t) ≤ 2 * 𝓕.ell t := by
  unfold LFam.ell
  have hB : (4 : ℝ) ≤ 𝓕.B := 𝓕.B_ge
  have hu := abs_nonneg t
  have e : 2 * Real.log (𝓕.B * (|t| + 2)) = Real.log ((𝓕.B * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [e, abs_mul, abs_two]
  apply Real.log_le_log
  · positivity
  · have h1 : 2 * |t| + 2 ≤ 4 * (|t| + 2) ^ 2 := by nlinarith
    have h2 : 4 * (|t| + 2) ^ 2 ≤ 𝓕.B * (|t| + 2) ^ 2 := by nlinarith [sq_nonneg (|t| + 2)]
    calc 𝓕.B * (2 * |t| + 2) ≤ 𝓕.B * (𝓕.B * (|t| + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (𝓕.B * (|t| + 2)) ^ 2 := by ring

theorem pole_le {ε y : ℝ} (hε : 0 < ε) (hy : (30 * ε) ^ 2 ≤ y ^ 2) :
    6 * ε / ((6 * ε) ^ 2 + y ^ 2) ≤ 1 / 156 * (1 / ε) := by
  have hD : 0 < (6 * ε) ^ 2 + y ^ 2 := by positivity
  have e : 1 / 156 * (1 / ε) = 1 / (156 * ε) := by ring
  rw [e, div_le_div_iff₀ hD (by positivity)]
  nlinarith

private lemma norm_ofReal_add_mul_I_le_abs_add_abs (x y : ℝ) : ‖(x : ℂ) + y * I‖ ≤ |x| + |y| := by
  simpa using norm_le_abs_re_add_abs_im ((x : ℂ) + y * I)

theorem inv_le_ell : ∃ K : ℝ, 0 < K ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (ε δ γ : ℝ),
    𝓕.F χ (((1 - δ : ℝ) : ℂ) + γ * I) = 0 → (χ * χ ≠ 1 ∨ γ ≠ 0) →
    0 < ε → ε ≤ 1 / 400 → 0 ≤ δ → δ ≤ ε → 1 / ε ≤ K * 𝓕.ell γ := by
  obtain ⟨C, hC, hR⟩ := re_LSeries_le
  refine ⟨300 * C, by positivity, ?_⟩
  intro 𝓕 χ ε δ γ hz hχ hε hε1 hδ hδε
  set ρ : ℂ := ((1 - δ : ℝ) : ℂ) + γ * I with hρ
  have hℓ0 := ell_zero_le 𝓕 γ
  have hℓ2 := ell_two_le 𝓕 γ
  have hℓ1 := one_le_ell 𝓕 γ
  have hCℓ0 : C * 𝓕.ell 0 ≤ C * 𝓕.ell γ := mul_le_mul_of_nonneg_left hℓ0 hC.le
  have hCℓ2 : C * 𝓕.ell (2 * γ) ≤ 2 * (C * 𝓕.ell γ) := by nlinarith
  have hCℓ : 0 ≤ C * 𝓕.ell γ := mul_nonneg hC.le (by linarith)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 1 / ε := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; positivity
  rw [← hv]
  by_cases hB : χ * χ = 1 ∧ γ ^ 2 < (30 * ε) ^ 2
  · obtain ⟨hχ2, hγ⟩ := hB
    have hγ0 : γ ≠ 0 := hχ.resolve_left (not_not.mpr hχ2)
    have ha0 : 0 < 60 * ε := by positivity
    have ha2 : 60 * ε ≤ 1 / 2 := by linarith
    set ρ' : ℂ := ((1 - δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I with hρ'
    have hz' : 𝓕.F χ ρ' = 0 := by
      have hc := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).2.2.2 hχ2 ρ
      have e : (starRingEnd ℂ) ρ = ρ' := by
        rw [hρ, hρ']
        apply Complex.ext <;> simp
      rw [← e, hc, hz]
      simp
    have hne : ρ ≠ ρ' := by
      intro h
      have := congrArg Complex.im h
      simp [hρ, hρ'] at this
      exact hγ0 (by linarith)
    have hγa : |γ| < 30 * ε := abs_lt_of_sq_lt_sq hγ (by linarith)
    have hnorm : ∀ g : ℝ, |g| < 30 * ε →
        ‖(((1 - δ : ℝ) : ℂ) + g * I) - (5 / 4 + ((0 : ℝ) : ℂ) * I)‖ ≤ 3 / 5 := by
      intro g hg
      have e : (((1 - δ : ℝ) : ℂ) + g * I) - (5 / 4 + ((0 : ℝ) : ℂ) * I)
          = ((-(1 / 4 + δ) : ℝ) : ℂ) + g * I := by push_cast; ring
      rw [e]
      refine (norm_ofReal_add_mul_I_le_abs_add_abs _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by linarith)]
      linarith
    have hnear : ∀ w ∈ ({ρ, ρ'} : Finset ℂ),
        ‖w - (5 / 4 + ((0 : ℝ) : ℂ) * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with h | h
      · rw [h]; exact ⟨hnorm γ hγa, hz⟩
      · rw [Finset.mem_singleton.mp h]
        exact ⟨hnorm (-γ) (by rwa [abs_neg]), hz'⟩
    have hsum : ∑ w ∈ ({ρ, ρ'} : Finset ℂ),
        (1 / (((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - w)).re
        = 2 * ((60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2)) := by
      rw [Finset.sum_pair hne]
      have e1 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ρ
          = ((60 * ε + δ : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
      have e2 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I - ρ'
          = ((60 * ε + δ : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I := by rw [hρ']; push_cast; ring
      rw [e1, e2, re_one_div, re_one_div, neg_sq]
      ring
    have hP : 60 * ε / ((60 * ε) ^ 2 + (0 : ℝ) ^ 2) ≤ 1 / (60 * ε) := by
      apply le_of_eq
      rw [show (60 * ε) ^ 2 + (0 : ℝ) ^ 2 = 60 * ε * (60 * ε) by ring, div_mul_eq_div_div,
        div_self ha0.ne']
    have e0 : ((1 + 60 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((1 + 60 * ε : ℝ) : ℂ) := by
      push_cast; ring
    have hmain : 2 * ((60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2))
        ≤ 1 / (60 * ε) + 2 * (C * 𝓕.ell 0) := by
      by_cases h1 : χ = 1
      · have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 60 * ε) 0 (by linarith)).2.1
        have hb := hR 𝓕 χ (60 * ε) 0 (1 / (60 * ε)) ha0 ha2 (by positivity) (fun _ => hP)
          {ρ, ρ'} hnear
        rw [hsum, e0, h1] at hb
        have hC0 : 0 ≤ C * 𝓕.ell 0 := mul_nonneg hC.le (by linarith [one_le_ell 𝓕 0])
        linarith
      · have h0 := ((GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 60 * ε) 0 (by linarith)).2.2 hχ2 hχ2).1
        have hb1 := hR 𝓕 1 (60 * ε) 0 (1 / (60 * ε)) ha0 ha2 (by positivity) (fun _ => hP)
          ∅ (by simp)
        have hb2 := hR 𝓕 χ (60 * ε) 0 0 ha0 ha2 le_rfl (fun h => absurd h h1) {ρ, ρ'} hnear
        rw [hsum, e0] at hb2
        rw [e0, Finset.sum_empty] at hb1
        linarith
    have hlow : 60 / (4621 * ε) ≤ (60 * ε + δ) / ((60 * ε + δ) ^ 2 + γ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 60 * ε + δ - 60 * ε by linarith)
        (show (0 : ℝ) ≤ 61 * ε - (60 * ε + δ) by linarith), mul_pos hε hε]
    have i1 : 1 / (60 * ε) = v / 60 := by rw [hv]; ring
    have i2 : 60 / (4621 * ε) = 60 / 4621 * v := by rw [hv]; ring
    nlinarith
  · have hcase1 : χ = 1 → (30 * ε) ^ 2 ≤ γ ^ 2 := by
      intro h
      by_contra hc
      push_neg at hc
      exact hB ⟨by rw [h, mul_one], hc⟩
    have hcase2 : χ * χ = 1 → (30 * ε) ^ 2 ≤ (2 * γ) ^ 2 := by
      intro h
      have : (30 * ε) ^ 2 ≤ γ ^ 2 := by
        by_contra hc
        push_neg at hc
        exact hB ⟨h, hc⟩
      nlinarith [sq_nonneg γ]
    have ha0 : 0 < 6 * ε := by positivity
    have ha2 : 6 * ε ≤ 1 / 2 := by linarith
    have hP0 : 0 ≤ 1 / 156 * (1 / ε) := by positivity
    have hP1 : 6 * ε / ((6 * ε) ^ 2 + (0 : ℝ) ^ 2) ≤ 1 / (6 * ε) := by
      apply le_of_eq
      rw [show (6 * ε) ^ 2 + (0 : ℝ) ^ 2 = 6 * ε * (6 * ε) by ring, div_mul_eq_div_div,
        div_self ha0.ne']
    have h0 := (GlobalTheory.T.rayClassLFunctionFamily_logDeriv_positivity 𝓕 χ χ (1 + 6 * ε) γ (by linarith)).1
    have hb1 := hR 𝓕 1 (6 * ε) 0 (1 / (6 * ε)) ha0 ha2 (by positivity) (fun _ => hP1) ∅ (by simp)
    have hρn : ∀ w ∈ ({ρ} : Finset ℂ), ‖w - (5 / 4 + γ * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0 := by
      intro w hw
      rw [Finset.mem_singleton.mp hw]
      refine ⟨?_, hz⟩
      have e : ρ - (5 / 4 + γ * I) = ((-(1 / 4 + δ) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by
        rw [hρ]; push_cast; ring
      rw [e]
      refine (norm_ofReal_add_mul_I_le_abs_add_abs _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by linarith), abs_zero]
      linarith
    have hb2 := hR 𝓕 χ (6 * ε) γ (1 / 156 * (1 / ε)) ha0 ha2 hP0
      (fun h => pole_le hε (hcase1 h)) {ρ} hρn
    have hb3 := hR 𝓕 (χ * χ) (6 * ε) (2 * γ) (1 / 156 * (1 / ε)) ha0 ha2 hP0
      (fun h => pole_le hε (hcase2 h)) ∅ (by simp)
    have e0 : ((1 + 6 * ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((1 + 6 * ε : ℝ) : ℂ) := by
      push_cast; ring
    have e2 : ((1 + 6 * ε : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I
        = ((1 + 6 * ε : ℝ) : ℂ) + 2 * (γ : ℂ) * I := by push_cast; ring
    have e1 : ((1 + 6 * ε : ℝ) : ℂ) + (γ : ℂ) * I - ρ
        = ((6 * ε + δ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
    rw [e0, Finset.sum_empty] at hb1
    rw [e2, Finset.sum_empty] at hb3
    rw [Finset.sum_singleton, e1, re_one_div] at hb2
    have hlow : 1 / (7 * ε) ≤ (6 * ε + δ) / ((6 * ε + δ) ^ 2 + (0 : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (show 6 * ε + δ ≤ 7 * ε by linarith)
        (show (0 : ℝ) ≤ 6 * ε + δ by linarith)]
    have i1 : 1 / (6 * ε) = v / 6 := by rw [hv]; ring
    have i2 : 1 / (7 * ε) = v / 7 := by rw [hv]; ring
    have i3 : 1 / 156 * (1 / ε) = v / 156 := by rw [hv]; ring
    nlinarith

theorem zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  obtain ⟨K, hK, hKb⟩ := inv_le_ell
  refine ⟨1 / (4 * K + 400), by positivity, ?_⟩
  intro 𝓕 χ s _ hs hχ
  by_contra hlt
  push_neg at hlt
  have hℓ2 := 𝓕.two_lt_ell s.im
  have hℓpos : 0 < 𝓕.ell s.im := by linarith
  have hpos : 0 < (2 * K + 200) * 𝓕.ell s.im := mul_pos (by linarith) hℓpos
  have hε : 0 < 1 / ((2 * K + 200) * 𝓕.ell s.im) := by positivity
  have hε1 : 1 / ((2 * K + 200) * 𝓕.ell s.im) ≤ 1 / 400 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [mul_pos hK hℓpos]
  have hδ : 0 ≤ 1 - s.re := by linarith [re_le_one hs]
  have hδε : 1 - s.re ≤ 1 / ((2 * K + 200) * 𝓕.ell s.im) := by
    have h1 : 1 - s.re ≤ 1 / (4 * K + 400) / 𝓕.ell s.im := by linarith
    refine h1.trans ?_
    rw [div_div]
    apply one_div_le_one_div_of_le hpos
    nlinarith [mul_pos hK hℓpos]
  have hz : 𝓕.F χ (((1 - (1 - s.re) : ℝ) : ℂ) + s.im * I) = 0 := by
    rw [show (1 - (1 - s.re) : ℝ) = s.re by ring, re_add_im]
    exact hs
  have h := hKb 𝓕 χ _ (1 - s.re) s.im hz hχ hε hε1 hδ hδε
  rw [one_div_one_div] at h
  nlinarith [mul_pos hK hℓpos]

end GlobalTheory.Hk.ZeroFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionZeroFreeRegionStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassLFunction_zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  first | exact @GlobalTheory.Hk.ZeroFree.zero_free_region | exact GlobalTheory.Hk.ZeroFree.zero_free_region | (intros; apply GlobalTheory.Hk.ZeroFree.zero_free_region <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortInterval
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.ShortInt

lemma one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  unfold LFam.ell
  have hB := 𝓕.B_ge
  have ht := abs_nonneg t
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  nlinarith

lemma zeros : ∃ c₀ A c : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 20 ∧ 0 < A ∧ 0 < c ∧ c ≤ 1 ∧ ∀ 𝓕 : LFam,
    ∃ Z : AddChar 𝓕.G ℂ → Finset ℝ, (∀ χ, 𝓕.ExcZ χ c₀ (Z χ)) ∧
      (∀ χ ψ β β', β ∈ Z χ → β' ∈ Z ψ → χ = ψ ∧ β = β') ∧
      ∀ χ, ∀ β ∈ Z χ, 3 / 4 ≤ β ∧ c / 𝓕.B ^ A ≤ 1 - β := by
  obtain ⟨c4, hc4, h4⟩ := GlobalTheory.T.rayClassLFunction_zero_free_region
  obtain ⟨c5, hc5, h5⟩ := GlobalTheory.T.rayClassLFunction_unique_simple_exceptional_zero
  obtain ⟨A, c9, hA, hc9, h9⟩ := GlobalTheory.T.exists_rayClassLFunction_real_zero_far_from_one
  refine ⟨min (1 / 20) (min c4 c5), A, min c9 1, by positivity, min_le_left _ _, hA, by positivity,
    min_le_right _ _, fun 𝓕 => ?_⟩
  set c₀ := min (1 / 20) (min c4 c5) with hc₀
  have h01 : c₀ ≤ 1 / 20 := min_le_left _ _
  have h04 : c₀ ≤ c4 := (min_le_right _ _).trans (min_le_left _ _)
  have h05 : c₀ ≤ c5 := (min_le_right _ _).trans (min_le_right _ _)
  have h0 : 0 < c₀ := by positivity
  have hBpos : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have key : ∀ (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 - c₀ / 𝓕.ell s.im ≤ s.re → 𝓕.F χ s = 0 →
      3 / 4 ≤ s.re ∧ χ * χ = 1 ∧ s.im = 0 := by
    intro χ s hs hF
    have hl := one_le_ell 𝓕 s.im
    have h1 : c₀ / 𝓕.ell s.im ≤ 1 / 20 := (div_le_self h0.le hl).trans h01
    have h2 : c₀ / 𝓕.ell s.im ≤ c4 / 𝓕.ell s.im := by gcongr
    have h34 : 3 / 4 ≤ s.re := by linarith
    refine ⟨h34, ?_⟩
    by_contra hne
    have := h4 𝓕 χ s h34 hF (by tauto)
    linarith
  have keyR : ∀ (χ : AddChar 𝓕.G ℂ) (β : ℝ), 1 - c₀ / 𝓕.ell 0 ≤ β → 𝓕.F χ β = 0 →
      3 / 4 ≤ β ∧ χ * χ = 1 ∧ 1 - c5 / 𝓕.ell 0 ≤ β := by
    intro χ β hβ hF
    have := key χ β (by simpa using hβ) hF
    have hl := one_le_ell 𝓕 0
    have h2 : c₀ / 𝓕.ell 0 ≤ c5 / 𝓕.ell 0 := by gcongr
    exact ⟨by simpa using this.1, this.2.1, by linarith⟩
  have uniq : ∀ (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), 1 - c₀ / 𝓕.ell 0 ≤ β → 𝓕.F χ β = 0 →
      1 - c₀ / 𝓕.ell 0 ≤ β' → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
    intro χ ψ β β' h1 h2 h3 h4
    obtain ⟨a1, a2, a3⟩ := keyR χ β h1 h2
    obtain ⟨b1, b2, b3⟩ := keyR ψ β' h3 h4
    exact h5 𝓕 χ ψ β β' a2 b2 a1 b1 a3 b3 h2 h4
  have gap : ∀ (χ : AddChar 𝓕.G ℂ) (β : ℝ), 1 - c₀ / 𝓕.ell 0 ≤ β → 𝓕.F χ β = 0 →
      min c9 1 / 𝓕.B ^ A ≤ 1 - β := by
    intro χ β h1 h2
    obtain ⟨a1, a2, a3⟩ := keyR χ β h1 h2
    refine le_trans ?_ (h9 𝓕 χ β a2 a1 h2)
    gcongr
    exact min_le_left _ _
  have ex : ∀ χ : AddChar 𝓕.G ℂ, ∃ Z : Finset ℝ,
      ∀ β : ℝ, β ∈ Z ↔ (1 - c₀ / 𝓕.ell 0 ≤ β ∧ 𝓕.F χ β = 0) := by
    intro χ
    by_cases h : ∃ β : ℝ, 1 - c₀ / 𝓕.ell 0 ≤ β ∧ 𝓕.F χ β = 0
    · obtain ⟨β, h1, h2⟩ := h
      refine ⟨{β}, fun γ => ?_⟩
      rw [Finset.mem_singleton]
      constructor
      · rintro rfl; exact ⟨h1, h2⟩
      · rintro ⟨h3, h4⟩; exact (uniq χ χ γ β h3 h4 h1 h2).2.1
    · exact ⟨∅, fun γ => ⟨fun hh => by simp at hh, fun hh => absurd ⟨γ, hh⟩ h⟩⟩
  choose Z hZ using ex
  refine ⟨Z, fun χ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.card_le_one]
    intro a ha b hb
    rw [hZ] at ha hb
    exact (uniq χ χ a b ha.1 ha.2 hb.1 hb.2).2.1
  · intro β hβ
    rw [hZ] at hβ
    have hg := gap χ β hβ.1 hβ.2
    have : 0 < min c9 1 / 𝓕.B ^ A := by positivity
    exact ⟨hβ.1, by linarith, hβ.2, (uniq χ χ β β hβ.1 hβ.2 hβ.1 hβ.2).2.2⟩
  · intro s hs hF
    obtain ⟨_, _, him⟩ := key χ s hs hF
    have hs' : s = (s.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    refine ⟨s.re, ?_, hs'⟩
    rw [hZ]
    exact ⟨by rw [him] at hs; exact hs, by rw [← hs']; exact hF⟩
  · intro χ ψ β β' h1 h2
    rw [hZ] at h1 h2
    have := uniq χ ψ β β' h1.1 h1.2 h2.1 h2.2
    exact ⟨this.1, this.2.1⟩
  · intro χ β hβ
    rw [hZ] at hβ
    exact ⟨(keyR χ β hβ.1 hβ.2).1, gap χ β hβ.1 hβ.2⟩

lemma sum_psi (𝓕 : LFam) (u : ℝ) :
    ∑ χ : AddChar 𝓕.G ℂ, 𝓕.psi χ u =
      (((Fintype.card 𝓕.G : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 𝓕.lam 0 n : ℝ) : ℂ) := by
  unfold LFam.psi LFam.lamChi
  rw [Finset.sum_comm]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  simp

lemma exc_le {X h β δ : ℝ} (hX : Real.exp 1 ≤ X) (hh : 0 ≤ h) (hβ : 3 / 4 ≤ β) (hδ : 0 < δ)
    (hδβ : δ ≤ 1 - β) : (X * (1 + h)) ^ β / β - X ^ β / β ≤ h * X * (1 - δ / 2) := by
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hβ0 : 0 < β := by linarith
  have h1 : (1 + h) ^ β ≤ 1 + β * h := rpow_one_add_le_one_add_mul_self (by linarith) hβ0.le (by linarith)
  have hlog : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX
  have h2 : X ^ β ≤ X * (1 - δ / 2) := by
    have e1 : X ^ β = X * Real.exp (-(Real.log X * (1 - β))) := by
      rw [Real.rpow_def_of_pos hX0]
      conv_rhs => rw [← Real.exp_log hX0]
      rw [Real.log_exp, ← Real.exp_add]
      congr 1; ring
    rw [e1]
    gcongr
    have e2 : Real.exp (-(Real.log X * (1 - β))) ≤ Real.exp (-δ) := by
      apply Real.exp_le_exp.2
      nlinarith
    refine e2.trans ?_
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have := Real.add_one_le_exp δ
    have h3 : 0 ≤ 1 - δ / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h3]
  rw [Real.mul_rpow hX0.le (by linarith), ← sub_div, div_le_iff₀ hβ0]
  have hp : 0 ≤ X ^ β := by positivity
  calc X ^ β * (1 + h) ^ β - X ^ β ≤ X ^ β * (1 + β * h) - X ^ β := by gcongr
    _ = X ^ β * (β * h) := by ring
    _ ≤ X * (1 - δ / 2) * (β * h) := by gcongr
    _ = _ := by ring

lemma sum_est (𝓕 : LFam) (Z : AddChar 𝓕.G ℂ → Finset ℝ) (u E : ℝ) (hu : 0 ≤ u) (hE : 0 ≤ E)
    (h : ∀ χ : AddChar 𝓕.G ℂ, ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) +
      ∑ β ∈ Z χ, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ E) :
    |(Fintype.card 𝓕.G : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 𝓕.lam 0 n - u +
      ∑ χ, ∑ β ∈ Z χ, u ^ β / β| ≤ 𝓕.B * E := by
  have e : (((Fintype.card 𝓕.G : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 𝓕.lam 0 n - u +
      ∑ χ, ∑ β ∈ Z χ, u ^ β / β : ℝ) : ℂ) = ∑ χ : AddChar 𝓕.G ℂ, (𝓕.psi χ u -
        (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z χ, (u : ℂ) ^ (β : ℂ) / (β : ℂ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_psi, ofReal_add, ofReal_sub]
    congr 1
    · simp
    · rw [ofReal_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [ofReal_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [ofReal_div, ofReal_cpow hu]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ E fun χ _ => h χ).trans ?_
  rw [Finset.card_univ, AddChar.card_eq, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right 𝓕.card_le hE

lemma sum_le_of_unique {ι : Type} [Fintype ι] (Z : ι → Finset ℝ) (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ i j β β', β ∈ Z i → β' ∈ Z j → i = j ∧ β = β') (hf : ∀ i, ∀ β ∈ Z i, f β ≤ M) :
    ∑ i, ∑ β ∈ Z i, f β ≤ M := by
  rw [Finset.sum_sigma']
  have hc : ((Finset.univ : Finset ι).sigma Z).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, a⟩ ha ⟨j, b⟩ hb
    rw [Finset.mem_sigma] at ha hb
    obtain ⟨rfl, rfl⟩ := hu i j a b ha.2 hb.2
    rfl
  refine (Finset.sum_le_card_nsmul _ _ M fun x hx => hf x.1 x.2 (Finset.mem_sigma.1 hx).2).trans ?_
  rw [nsmul_eq_mul]
  have : ((((Finset.univ : Finset ι).sigma Z).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

lemma err_le {B A c c₇ c₉ C L h : ℝ} (hB : 4 ≤ B) (hA : 0 < A) (hc : 0 < c) (hc₇ : 0 < c₇) (hc₉ : 0 < c₉)
    (hC : 0 < C) (h1 : (A + 2) * c ≤ c₇ / 2) (h2 : c ≤ c₇ * c₉ / (24 * C))
    (hL : Real.log B ≤ c * L) (hh : Real.exp (-c * L) ≤ h) :
    3 * B * C * Real.exp (-c₇ * L) ≤ h * (c₉ / B ^ A) / 4 := by
  have hB0 : 0 < B := by linarith
  have hlog : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hcL : 1 ≤ c * L := hlog.trans hL
  have hL0 : 0 < L := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith
  have a1 : B ≤ Real.exp (c * L) := by
    rw [← Real.exp_log hB0]; exact Real.exp_le_exp.2 hL
  have a2 : B ^ A ≤ Real.exp (c * L * A) := by
    rw [Real.rpow_def_of_pos hB0]; apply Real.exp_le_exp.2; gcongr
  have a3 : 12 * C ≤ c₉ * Real.exp (c₇ / 2 * L) := by
    have := Real.add_one_le_exp (c₇ / 2 * L)
    rw [le_div_iff₀ (by positivity)] at h2
    have b1 : c * (24 * C) * L ≤ c₇ * c₉ * L := by gcongr
    have b2 : 24 * C * 1 ≤ 24 * C * (c * L) := by gcongr
    nlinarith
  have hBA : 0 < B ^ A := by positivity
  have a4 : Real.exp (c * L) * Real.exp (c * L * A) * Real.exp (c₇ / 2 * L) * Real.exp (-c₇ * L) ≤
      Real.exp (-c * L) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right h1 hL0.le]
  rw [mul_div_assoc', div_div, le_div_iff₀ (by positivity)]
  calc 3 * B * C * Real.exp (-c₇ * L) * (B ^ A * 4)
      = B * B ^ A * (12 * C) * Real.exp (-c₇ * L) := by ring
    _ ≤ Real.exp (c * L) * Real.exp (c * L * A) * (c₉ * Real.exp (c₇ / 2 * L)) * Real.exp (-c₇ * L) := by
      gcongr
    _ = Real.exp (c * L) * Real.exp (c * L * A) * Real.exp (c₇ / 2 * L) * Real.exp (-c₇ * L) * c₉ := by
      ring
    _ ≤ h * c₉ := by gcongr; exact a4.trans hh

theorem trivialClass_shortInterval : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (𝓕 : LFam) (X h : ℝ), 1 ≤ X → Real.log 𝓕.B ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / 𝓕.B ^ A ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
  obtain ⟨c₀, A, c₉, hc₀, hc₀', hA, hc₉, hc₉', hz⟩ := zeros
  obtain ⟨c₇, C, hc₇, hC, h7⟩ := GlobalTheory.T.rayClassFamily_psi_with_exceptional_zero c₀ hc₀ hc₀'
  refine ⟨A + 1, min 1 (min (c₇ / 2 / (A + 2)) (c₇ * c₉ / (24 * C))), c₉ / 4, by positivity,
    by positivity, by positivity, ?_⟩
  set c := min 1 (min (c₇ / 2 / (A + 2)) (c₇ * c₉ / (24 * C))) with hcdef
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hc2 : (A + 2) * c ≤ c₇ / 2 := by
    have : c ≤ c₇ / 2 / (A + 2) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hc3 : c ≤ c₇ * c₉ / (24 * C) := (min_le_right _ _).trans (min_le_right _ _)
  intro 𝓕 X h hX hL hh hh1
  obtain ⟨Z, hZ, huniq, hgap⟩ := hz 𝓕
  have hB := 𝓕.B_ge
  have hB0 : 0 < 𝓕.B := by linarith
  have hX0 : 0 < X := by linarith
  have hh0 : 0 < h := (Real.exp_pos _).trans_le hh
  have herr := err_le hB hA hc hc₇ hc₉ hC hc2 hc3 hL hh
  have hL0 := Real.sqrt_nonneg (Real.log X)
  have hL' : Real.log 𝓕.B ≤ Real.sqrt (Real.log X) := hL.trans (mul_le_of_le_one_left hL0 hc1)
  have hlogB : 1 ≤ Real.log 𝓕.B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hlogX : 1 ≤ Real.log X := Real.one_le_sqrt.1 (hlogB.trans hL')
  have hXe : Real.exp 1 ≤ X := (Real.le_log_iff_exp_le hX0).1 hlogX
  have hX2 : 2 ≤ X := by linarith [Real.exp_one_gt_d9]
  have hXY : X ≤ X * (1 + h) := by nlinarith
  have hY2 : X * (1 + h) ≤ 2 * X := by nlinarith
  have hLY : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log (X * (1 + h))) :=
    Real.sqrt_le_sqrt (Real.log_le_log hX0 hXY)
  set E := Real.exp (-c₇ * Real.sqrt (Real.log X)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 := sum_est 𝓕 Z X (C * X * E) hX0.le (by positivity) fun χ => h7 𝓕 χ (Z χ) X (hZ χ) hX2 hL'
  have e2 := sum_est 𝓕 Z (X * (1 + h)) (C * (2 * X) * E) (by positivity) (by positivity) fun χ =>
    (h7 𝓕 χ (Z χ) (X * (1 + h)) (hZ χ) (hX2.trans hXY) (hL'.trans hLY)).trans (by
      have : Real.exp (-c₇ * Real.sqrt (Real.log (X * (1 + h)))) ≤ E :=
        Real.exp_le_exp.2 (by nlinarith)
      gcongr)
  set δ := c₉ / 𝓕.B ^ A with hδ
  have hBA : 1 ≤ 𝓕.B ^ A := Real.one_le_rpow (by linarith) hA.le
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (div_le_self hc₉.le hBA).trans hc₉'
  have e3 := sum_le_of_unique Z (fun β => (X * (1 + h)) ^ β / β - X ^ β / β) (h * X * (1 - δ / 2))
    (by have : 0 ≤ 1 - δ / 2 := by linarith
        positivity) huniq
    fun χ β hβ => exc_le hXe hh0.le (hgap χ β hβ).1 hδ0 (hgap χ β hβ).2
  simp only [Finset.sum_sub_distrib] at e3
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, 𝓕.lam 0 n +
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
    have := Finset.sum_Ioc_consecutive (fun n => 𝓕.lam 0 n) (Nat.zero_le ⌊X⌋₊) (Nat.floor_le_floor hXY)
    exact this.symm
  set S := ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => 𝓕.lam_nonneg 0 n
  rw [hsplit] at e2
  have e1' := (abs_le.1 e1).2
  have e2' := (abs_le.1 e2).1
  have herrX := mul_le_mul_of_nonneg_left herr hX0.le
  have main : h * X * δ / 4 ≤ (Fintype.card 𝓕.G : ℝ) * S := by nlinarith
  have main2 : h * X * δ / 4 ≤ 𝓕.B * S := main.trans (mul_le_mul_of_nonneg_right 𝓕.card_le hS0)
  rw [Real.rpow_add_one hB0.ne', ← div_div, div_le_iff₀ hB0]
  calc c₉ / 4 * h * X / 𝓕.B ^ A = h * X * δ / 4 := by rw [hδ]; ring
    _ ≤ 𝓕.B * S := main2
    _ = S * 𝓕.B := mul_comm _ _

end GlobalTheory.Hk.ShortInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortIntervalStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lam_zero_sum_shortInterval_ge : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (𝓕 : LFam) (X h : ℝ), 1 ≤ X → Real.log 𝓕.B ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / 𝓕.B ^ A ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
  first | exact @GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | exact GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | (intros; apply GlobalTheory.Hk.ShortInt.trivialClass_shortInterval <;> assumption)
end
