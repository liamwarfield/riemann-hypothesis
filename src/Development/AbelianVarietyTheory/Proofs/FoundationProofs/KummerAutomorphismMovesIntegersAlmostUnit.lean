module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadius
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLe
namespace GlobalTheory.AlmostEt

open scoped NNReal

theorem valuation_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) :
    v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

theorem valuation_add_pow_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ)
    (hp : p.Prime) (y β : L) :
    v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have key : (y + β) ^ (q + 1) - y ^ (q + 1) - β ^ (q + 1) =
      ∑ i ∈ Finset.range q, y ^ (i + 1) * β ^ (q + 1 - (i + 1)) * ((q + 1).choose (i + 1) : L) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  rw [key]
  apply Valuation.map_sum_le
  intro i hi
  have hi : i < q := Finset.mem_range.mp hi
  set M := max (v y) (v β)
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hsub : q + 1 - (i + 1) = (q - (i + 1)) + 1 := by omega
  rw [hk, hsub]
  push_cast
  simp only [map_mul, map_pow]
  have h1 : v y ^ (i + 1) ≤ M ^ (i + 1) := pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have h2 : v β ^ (q - (i + 1)) ≤ M ^ (q - (i + 1)) := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  have h3 : v (k : L) ≤ 1 := valuation_natCast_le_one v k
  have hM : M ^ (i + 1) * M ^ (q - (i + 1)) = M ^ q := by
    rw [← pow_add]; congr 1; omega
  rw [pow_succ (v β)]
  calc _ ≤ M ^ (i + 1) * (M ^ (q - (i + 1)) * v β) * (v ((q : L) + 1) * 1) := by gcongr
    _ = _ := by simp only [Nat.add_sub_cancel, ← hM]; ring

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLeStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ y β : L, v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.valuation_add_pow_sub_le | exact GlobalTheory.AlmostEt.valuation_add_pow_sub_le | (intros; apply GlobalTheory.AlmostEt.valuation_add_pow_sub_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGenerator
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

lemma nnreal_mul_max_le (a b c : ℝ≥0) (hc : c ≤ 1) : c * max a b ≤ max a (c * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact (mul_le_of_le_one_left (by positivity) hc).trans (le_max_left _ _)

theorem exists_approxRoot_step : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 →
    (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F →
    v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤
      max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  intro L _ v p hp F θ hθ hvp hF α y hα hy hβα
  set β := α - y with hβ
  set A := v (p : L) * v β * v α ^ (p - 1) with hA
  have hyα : v y ≤ v α := by
    have : y = α - β := by rw [hβ]; ring
    rw [this]; exact (Valuation.map_sub v α β).trans (max_le le_rfl hβα)
  have hpp : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  set u := α ^ p - y ^ p with hu
  have huF : u ∈ F := F.sub_mem hα (F.pow_mem hy p)
  have h1 : v (u - β ^ p) ≤ A := by
    have := GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp y β
    have e : y + β = α := by rw [hβ]; ring
    rw [e] at this
    refine this.trans ?_
    rw [hA]
    gcongr
    exact max_le hyα hβα
  set M := max A (v β ^ p) with hM
  have hvu : v u ≤ M := by
    have : u = (u - β ^ p) + β ^ p := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans ?_
    rw [Valuation.map_pow]; exact max_le_max h1 le_rfl
  obtain ⟨w, hwF, hw⟩ := hF u huF
  have hw' : v (u - w ^ p) ≤ v u := hw.trans (mul_le_of_le_one_left (by positivity) hθ)
  have hwM : v w ^ p ≤ M := by
    have : w ^ p = u - (u - w ^ p) := by ring
    rw [← Valuation.map_pow, this]
    exact ((Valuation.map_sub v _ _).trans (max_le le_rfl hw')).trans hvu
  have h2 : v (β ^ p - w ^ p) ≤ max A (θ * v β ^ p) := by
    have : β ^ p - w ^ p = -(u - β ^ p) + (u - w ^ p) := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact h1.trans (le_max_left _ _)
    · exact (hw.trans (mul_le_mul_of_nonneg_left hvu (by positivity))).trans (nnreal_mul_max_le _ _ _ hθ)
  refine ⟨y + w, F.add_mem hy hwF, ?_⟩
  set γ := β - w with hγ
  have e2 : α - (y + w) = γ := by rw [hγ, hβ]; ring
  rw [e2]
  set m := max (v w) (v γ) with hm
  have hmβ : m ≤ max (v β) (v w) :=
    max_le (le_max_right _ _) ((Valuation.map_sub v β w))
  have hmM : m ^ p ≤ M := by
    refine (pow_le_pow_left₀ (by positivity) hmβ p).trans ?_
    rcases le_total (v β) (v w) with h | h
    · rw [max_eq_right h]; exact hwM
    · rw [max_eq_left h]; exact le_max_right _ _
  have h3 : v ((w + γ) ^ p - w ^ p - γ ^ p) ≤ max A (v (p : L) * v β ^ p) := by
    refine (GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp w γ).trans ?_
    have : v (p : L) * v γ * m ^ (p - 1) ≤ v (p : L) * m ^ p := by
      rw [mul_assoc, ← hpp, pow_succ, mul_comm (m ^ (p - 1)) m, hpp]
      gcongr
      exact le_max_right _ _
    refine this.trans ((mul_le_mul_of_nonneg_left hmM (by positivity)).trans (nnreal_mul_max_le _ _ _ hvp))
  have e3 : γ ^ p = (β ^ p - w ^ p) - ((w + γ) ^ p - w ^ p - γ ^ p) := by
    have : w + γ = β := by rw [hγ]; ring
    rw [this]; ring
  rw [← Valuation.map_pow, e3]
  refine (Valuation.map_sub v _ _).trans (max_le (h2.trans ?_) (h3.trans ?_))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGeneratorStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_improved_approx_kummer_generator : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 → (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F → v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤ max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  first | exact @GlobalTheory.AlmostEt.exists_approxRoot_step | exact GlobalTheory.AlmostEt.exists_approxRoot_step | (intros; apply GlobalTheory.AlmostEt.exists_approxRoot_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadius
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_approx_critical : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) →
    ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  intro L _ v p hp F hF hvp α hα hvp0 s hs
  obtain ⟨θ, hθ, hθF⟩ := hF
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : p - 1 ≠ 0 := by omega
  by_cases hα0 : α = 0
  · refine ⟨0, F.zero_mem, ?_⟩
    simp [hα0, zero_pow hp1]
  by_contra hcon
  push_neg at hcon
  have hs0 : (0 : ℝ≥0) < s := zero_lt_one.trans hs
  have ha : 0 < v α := (Valuation.pos_iff v).2 hα0
  set a := v α with ha_def
  set c := s * v (p : L) * a ^ (p - 1) with hc_def
  have hc : 0 < c := by positivity
  set η : ℝ≥0 := max s⁻¹ (max θ (v (p : L))) with hη_def
  have hη : η < 1 := by
    simp only [hη_def, max_lt_iff]
    exact ⟨inv_lt_one_of_one_lt₀ hs, hθ, hvp⟩
  have step : ∀ y ∈ F, v (α - y) ≤ a → ∃ y' ∈ F, v (α - y') ^ p ≤ η * v (α - y) ^ p := by
    intro y hy hya
    obtain ⟨y', hy', h⟩ := GlobalTheory.T.exists_improved_approx_kummer_generator L v p hp F θ hθ.le hvp.le hθF α y hα hy hya
    refine ⟨y', hy', h.trans ?_⟩
    have hcb := hcon y hy
    set b := v (α - y)
    apply max_le
    · have h0 : s * (v (p : L) * a ^ (p - 1)) ≤ b ^ (p - 1) := by
        calc s * (v (p : L) * a ^ (p - 1)) = c := by rw [hc_def]; ring
          _ ≤ _ := hcb.le
      have h2 : v (p : L) * a ^ (p - 1) ≤ s⁻¹ * b ^ (p - 1) := by
        calc v (p : L) * a ^ (p - 1) = s⁻¹ * (s * (v (p : L) * a ^ (p - 1))) := (inv_mul_cancel_left₀ hs0.ne' _).symm
          _ ≤ s⁻¹ * b ^ (p - 1) := by gcongr
      have h1 : v (p : L) * b * a ^ (p - 1) ≤ s⁻¹ * b ^ p := by
        calc v (p : L) * b * a ^ (p - 1) = b * (v (p : L) * a ^ (p - 1)) := by ring
          _ ≤ b * (s⁻¹ * b ^ (p - 1)) := by gcongr
          _ = s⁻¹ * (b ^ (p - 1) * b) := by ring
          _ = s⁻¹ * b ^ p := by rw [← pow_succ]; congr 2; omega
      exact h1.trans (by gcongr; exact le_max_left _ _)
    · gcongr; exact le_max_right _ _
  have iter : ∀ k : ℕ, ∃ y ∈ F, v (α - y) ≤ a ∧ v (α - y) ^ p ≤ η ^ k * a ^ p := by
    intro k
    induction k with
    | zero => exact ⟨0, F.zero_mem, by simp [ha_def], by simp [ha_def]⟩
    | succ k ih =>
      obtain ⟨y, hy, hya, hyk⟩ := ih
      obtain ⟨y', hy', h'⟩ := step y hy hya
      have hle : v (α - y') ^ p ≤ v (α - y) ^ p :=
        h'.trans (mul_le_of_le_one_left (by positivity) hη.le)
      refine ⟨y', hy', ?_, ?_⟩
      · exact ((pow_le_pow_iff_left₀ (by positivity) (by positivity) hp.ne_zero).1 hle).trans hya
      · calc v (α - y') ^ p ≤ η * v (α - y) ^ p := h'
          _ ≤ η * (η ^ k * a ^ p) := by gcongr
          _ = η ^ (k + 1) * a ^ p := by ring
  have hA : 0 < (a ^ p) ^ (p - 1) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hc p) hA) hη
  obtain ⟨y, hy, -, hyk⟩ := iter k
  have hcb := hcon y hy
  have e1 : c ^ p < (v (α - y) ^ p) ^ (p - 1) := by
    calc c ^ p < (v (α - y) ^ (p - 1)) ^ p := pow_lt_pow_left₀ hcb (by positivity) hp.ne_zero
      _ = _ := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : (v (α - y) ^ p) ^ (p - 1) ≤ η ^ k * (a ^ p) ^ (p - 1) := by
    calc (v (α - y) ^ p) ^ (p - 1) ≤ (η ^ k * a ^ p) ^ (p - 1) := pow_le_pow_left₀ (by positivity) hyk _
      _ = (η ^ k) ^ (p - 1) * (a ^ p) ^ (p - 1) := mul_pow _ _ _
      _ ≤ η ^ k * (a ^ p) ^ (p - 1) :=
          mul_le_mul_of_nonneg_right (pow_le_of_le_one (by positivity) (pow_le_one₀ (by positivity) hη.le) hp1) (by positivity)
  have e3 : η ^ k * (a ^ p) ^ (p - 1) < c ^ p := (lt_div_iff₀ hA).1 hk
  exact lt_irrefl _ ((e1.trans_le e2).trans e3)

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadiusStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_generator_approx_critical_radius : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) → ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.kummer_approx_critical | exact GlobalTheory.AlmostEt.kummer_approx_critical | (intros; apply GlobalTheory.AlmostEt.kummer_approx_critical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnit
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) →
    ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ σ hσ ζ α hζ hα hαp hσα r hr
  obtain ⟨t, hrt, ht1⟩ := exists_between hr
  have ht0 : 0 < t := lt_of_le_of_lt (zero_le') hrt
  set s : ℝ≥0 := t⁻¹ with hs_def
  have hs1 : 1 < s := by rw [hs_def]; exact one_lt_inv₀ ht0 |>.mpr ht1
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hrs : r * s < 1 := by
    rw [hs_def, ← div_eq_mul_inv]; exact (div_lt_one ht0).mpr hrt
  obtain ⟨y, hyF, hy⟩ := GlobalTheory.T.kummer_generator_approx_critical_radius L v p hp F hF hp1 α hαp hp0 s hs1
  have hz := GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq L v p hp ζ hζ
  have hp2 : 2 ≤ p := hp.two_le
  have hpn : p - 1 ≠ 0 := by omega
  set β := α - y with hβ_def
  have hσβ : σ • β - β = (ζ - 1) * α := by
    rw [hβ_def, smul_sub, hσα, hσ y hyF]; ring
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hne : σ • β - β ≠ 0 := by
    rw [hσβ]; exact mul_ne_zero (sub_ne_zero.mpr hζ1) hα
  have hβ0 : β ≠ 0 := by
    intro h; apply hne; rw [h, smul_zero, sub_zero]

  have hvβ : v β ≤ s * v (σ • β - β) := by
    have h1 : v β ^ (p - 1) ≤ (s * v (σ • β - β)) ^ (p - 1) := by
      rw [hσβ, map_mul, mul_pow, mul_pow, hz]
      calc v β ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := hy
        _ ≤ s ^ (p - 1) * v (p : L) * v α ^ (p - 1) := by
          gcongr
          exact le_self_pow₀ hs1.le hpn
        _ = s ^ (p - 1) * (v (p : L) * v α ^ (p - 1)) := by ring
    exact le_of_pow_le_pow_left₀ hpn (zero_le') h1
  obtain ⟨d, hdF, hd0, hdlo, hdhi⟩ := GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 (r * s) hrs β hβ0
  refine ⟨β * d ^ p, Subfield.mem_top _, hdhi, ?_⟩
  have hσx : σ • (β * d ^ p) - β * d ^ p = d ^ p * (σ • β - β) := by
    rw [smul_mul', smul_pow', hσ d hdF]; ring
  rw [hσx]
  have hvx : v (β * d ^ p) ≤ s * v (d ^ p * (σ • β - β)) := by
    rw [map_mul, map_mul]
    calc v β * v (d ^ p) ≤ s * v (σ • β - β) * v (d ^ p) := by gcongr
      _ = s * (v (d ^ p) * v (σ • β - β)) := by ring
  have : r * s < s * v (d ^ p * (σ • β - β)) := lt_of_lt_of_le hdlo hvx
  rw [mul_comm] at this
  exact lt_of_mul_lt_mul_left this (zero_le')

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnitStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_automorphism_moves_integers_almost_unit : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) → ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.kummer_moves | exact GlobalTheory.AlmostEt.kummer_moves | (intros; apply GlobalTheory.AlmostEt.kummer_moves <;> assumption)
end
