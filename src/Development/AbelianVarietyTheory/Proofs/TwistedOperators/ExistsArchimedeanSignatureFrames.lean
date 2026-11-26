module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothVectorMatrixCoeffIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransversalCoefficientDecayAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEven
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEven
open Formalism.L2.Theta

namespace GlobalTheory.HCEnum

open GlobalTheory.SignedHC GlobalTheory.SignedHC.GridData

theorem isHCParam_parPi_zero_parD0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m →
    IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  intro G n lam ε mu ε' hk hm hn hl hmu
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hkR : (G.k : ℝ) = k' + k' := by rw [hk']; push_cast; ring
  have hmR : (G.m : ℝ) = m' + m' := by rw [hm']; push_cast; ring
  have hnR : (n : ℝ) = (G.k : ℝ) + G.m - 1 := by
    have : ((n + 1 : ℕ) : ℝ) = ((G.k + G.m : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  refine ⟨⟨hl.1, fun a => ?_⟩, ⟨hmu.1, fun a => ?_⟩⟩
  · obtain ⟨-, q, hq, hS⟩ := hl
    have hmem : (q a, ε a) ∈ G.parPi 0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [parPi_zero, mem_lam] at hmem
    rw [hq a]
    rcases hmem with ⟨i, -, he⟩ | ⟨hc, -⟩
    · have e : q a = G.a i := congrArg Prod.fst he
      refine ⟨G.v 2 + ((G.m : ℤ) + 1 - i) * G.ga + 1 - (k' + m'), ?_⟩
      rw [e]; simp only [GridData.a]; push_cast; rw [hnR, hkR, hmR]; ring
    · obtain ⟨i, -, -, hx⟩ := mem_cloudHalf.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m'), ?_⟩
      rw [hx]; simp only [vHalf]; push_cast; rw [hnR, hkR, hmR]; ring
  · obtain ⟨-, q, hq, hS⟩ := hmu
    have hmem : (q a, ε' a) ∈ G.parD0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [mem_discrete_parameter_iff] at hmem
    rw [hq a]
    rcases hmem with ⟨hc, -⟩ | ⟨l, -, -, he⟩
    · obtain ⟨i, -, -, hx⟩ := mem_cloud.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m' - 1), ?_⟩
      rw [hx]; push_cast; rw [hnR, hkR, hmR]; ring
    · have e : q a = -(G.b l : ℚ) := congrArg Prod.fst he
      refine ⟨-G.b l - (k' + m' - 1), ?_⟩
      rw [e]; push_cast; rw [hnR, hkR, hmR]; ring

end GlobalTheory.HCEnum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEvenStatement
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_param_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  first | exact @GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | exact GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | (intros; apply GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedParametersBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedParametersBounded
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

theorem v_bounds_of_mem (G : GridData) {i : ℕ} (h2 : 2 ≤ i) (hk : i ≤ G.k) : G.v G.k ≤ G.v i ∧ G.v i ≤ G.v 2 := by
  constructor
  · rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt (G.v_anti i G.k h2 h le_rfl)
  · rcases eq_or_lt_of_le h2 with h | h
    · rw [← h]
    · exact le_of_lt (G.v_anti 2 i le_rfl h hk)

theorem b_bounds_of_mem (G : GridData) {l : ℕ} (h1 : 1 ≤ l) (hm : l ≤ G.m) : G.b 1 ≤ G.b l ∧ G.b l ≤ G.b G.m := by
  constructor
  · rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]
    · exact le_of_lt (G.b_mono 1 l le_rfl h hm)
  · rcases eq_or_lt_of_le hm with h | h
    · rw [h]
    · exact le_of_lt (G.b_mono l G.m h1 h le_rfl)

theorem abs_le_a_zero_of_mem_lam (G : GridData) (hv : 0 ≤ G.v G.k) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    |x.1| ≤ G.a 0 := by
  have hv2 : (0 : ℚ) ≤ G.v 2 := by
    have := (G.v_bounds_of_mem le_rfl G.two_le_k).1
    exact_mod_cast hv.trans this
  have hga : (0 : ℚ) ≤ G.ga := by positivity
  rcases G.mem_lam.1 hx with ⟨l, hl, rfl⟩ | ⟨hc, -⟩
  · have e := G.a_sub_a 0 l
    simp only [Nat.cast_zero, sub_zero] at e
    have hm := G.a_m
    have e2 := G.a_sub_a l G.m
    have hl' : (l : ℚ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℚ) ≤ l := by positivity
    have h1 : (0 : ℚ) ≤ (l : ℚ) * G.ga := mul_nonneg hl0 hga
    have h2 : (0 : ℚ) ≤ ((G.m : ℚ) - l) * G.ga := mul_nonneg (by linarith) hga
    simp only
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, h2, hk, e⟩ := G.mem_cloudHalf.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, vHalf, abs_le]; constructor <;> linarith

theorem abs_le_of_mem_D0 (G : GridData) (hv : 0 ≤ G.v G.k) (hb : 0 < G.b 1) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    |x.1| ≤ G.a 0 ∨ |x.1| ≤ G.b G.m := by
  rcases G.mem_discrete_parameter_iff.1 hx with ⟨hc, -⟩ | ⟨l, h1, hm, rfl⟩
  · left
    obtain ⟨i, h2, hk, e⟩ := G.mem_cloud.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, abs_le]; constructor <;> linarith
  · right
    obtain ⟨hlo, hhi⟩ := G.b_bounds_of_mem h1 hm
    have hlo' : (0 : ℚ) < G.b l := by exact_mod_cast hb.trans_le hlo
    have hhi' : (G.b l : ℚ) ≤ G.b G.m := by exact_mod_cast hhi
    simp only
    rw [abs_le]; constructor <;> linarith

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.Twist

open GlobalTheory.SignedHC

theorem parPi_parD0_entries_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 →
    ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  intro G n lam ε mu ε' B hv hb hA hBm hP hD
  obtain ⟨-, q, hq, hS⟩ := hP
  obtain ⟨-, q', hq', hS'⟩ := hD
  constructor
  · intro a
    have hmem : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have h := G.abs_le_a_zero_of_mem_lam hv hmem
    rw [hq a]
    have h' : |((q a : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
    exact h'.trans hA
  · intro i
    have hmem : (q' i, ε' i) ∈ G.parD0 := by
      rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [hq' i]
    rcases G.abs_le_of_mem_D0 hv hb hmem with h | h
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
      exact h'.trans hA
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.b G.m : ℤ) : ℝ) := by
        rw [← Rat.cast_abs]
        have : ((G.b G.m : ℤ) : ℝ) = (((G.b G.m : ℤ) : ℚ) : ℝ) := by push_cast; rfl
        rw [this]; exact_mod_cast h
      exact h'.trans hBm

end GlobalTheory.Twist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedParametersBoundedStatement
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signed_parameters_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 → ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  first | exact @GlobalTheory.Twist.parPi_parD0_entries_bounded | exact GlobalTheory.Twist.parPi_parD0_entries_bounded | (intros; apply GlobalTheory.Twist.parPi_parD0_entries_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InterlacedSignedParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InterlacedSignedParameters
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

def mergedDecreasingWordPiZeroDZero (G : GridData) (p : ℕ) : ℚ :=
  if p ≤ G.m then G.a p
  else if p ≤ G.m + 2 * (G.k - 1) then
    (if (p - G.m) % 2 = 1 then (G.v ((p - G.m + 3) / 2) : ℚ) else G.vHalf ((p - G.m + 2) / 2))
  else -(G.b (p - G.m - 2 * (G.k - 1)) : ℚ)

def mergedDecreasingWordParity (G : GridData) (p : ℕ) : Bool := decide ((G.m + p) % 2 = 1)

theorem merged_word_succ_lt (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p : ℕ}
    (hp : p < 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero (p + 1) < G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  have hg : (0 : ℚ) < G.ga := by exact_mod_cast hga
  unfold mergedDecreasingWordPiZeroDZero
  rcases lt_trichotomy p G.m with h | rfl | h
  · rw [if_pos (by omega : p + 1 ≤ G.m), if_pos h.le, G.a_eq_succ_add p]; linarith
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos le_rfl,
      show (G.m + 1 - G.m + 3) / 2 = 2 by omega, G.a_m]
    linarith
  · rw [if_neg (show ¬ p + 1 ≤ G.m by omega), if_neg (show ¬ p ≤ G.m by omega)]
    rcases lt_trichotomy p (G.m + 2 * (G.k - 1)) with h' | h' | h'
    · rw [if_pos (show p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos h'.le]
      by_cases hj : (p - G.m) % 2 = 1
      · rw [if_neg (show ¬ (p + 1 - G.m) % 2 = 1 by omega), if_pos hj, show (p + 1 - G.m + 2) / 2 = (p - G.m + 3) / 2 by omega, vHalf]
        linarith
      · rw [if_pos (show (p + 1 - G.m) % 2 = 1 by omega), if_neg hj, show (p + 1 - G.m + 3) / 2 = (p - G.m + 2) / 2 + 1 by omega, vHalf]
        have := G.v_anti ((p - G.m + 2) / 2) ((p - G.m + 2) / 2 + 1) (by omega) (by omega) (by omega)
        have : ((G.v ((p - G.m + 2) / 2 + 1) : ℤ) : ℚ) + 1 ≤ (G.v ((p - G.m + 2) / 2) : ℚ) := by
          exact_mod_cast this
        linarith
    · subst h'
      rw [if_neg (show ¬ G.m + 2 * (G.k - 1) + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos le_rfl,
        if_neg (show ¬ (G.m + 2 * (G.k - 1) - G.m) % 2 = 1 by omega),
        show G.m + 2 * (G.k - 1) + 1 - G.m - 2 * (G.k - 1) = 1 by omega,
        show (G.m + 2 * (G.k - 1) - G.m + 2) / 2 = G.k by omega, vHalf]
      have : (1 : ℚ) ≤ (G.v G.k : ℚ) + (G.b 1 : ℚ) := by exact_mod_cast hvb
      linarith
    · rw [if_neg (show ¬ p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_neg (show ¬ p ≤ G.m + 2 * (G.k - 1) by omega),
        show p + 1 - G.m - 2 * (G.k - 1) = (p - G.m - 2 * (G.k - 1)) + 1 by omega]
      have := G.b_mono (p - G.m - 2 * (G.k - 1)) (p - G.m - 2 * (G.k - 1) + 1) (by omega) (by omega) (by omega)
      have : ((G.b (p - G.m - 2 * (G.k - 1)) : ℤ) : ℚ) < (G.b (p - G.m - 2 * (G.k - 1) + 1) : ℚ) := by
        exact_mod_cast this
      linarith

theorem merged_word_strict_anti (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p p' : ℕ} (h : p < p')
    (hp' : p' ≤ 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero p' < G.mergedDecreasingWordPiZeroDZero p := by
  induction p' with
  | zero => omega
  | succ p' ih =>
    have h1 := G.merged_word_succ_lt hga hvb (p := p') (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact h1.trans (ih h (by omega))
    · exact h1

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.SignedHC.GridData

theorem exists_pos_of_mem_lam (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ (!x.2) = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hc, hs⟩
  · refine ⟨i, by omega, by simp [mergedDecreasingWordPiZeroDZero, hi], ?_⟩
    simp only [mergedDecreasingWordParity, Nat.even_iff]
    by_cases h : (G.m - i) % 2 = 0
    · simp [h]; omega
    · simp [h]; omega
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloudHalf.1 hc
    refine ⟨G.m + 2 * i - 2, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 2 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 2 ≤ G.m + 2 * (G.k - 1) by omega),
        if_neg (show ¬ (G.m + 2 * i - 2 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 2 - G.m + 2) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega

theorem exists_position_of_mem_D0 (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ x.2 = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_discrete_parameter_iff.1 hx with ⟨hc, hs⟩ | ⟨l, hl1, hlm, rfl⟩
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloud.1 hc
    refine ⟨G.m + 2 * i - 3, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 3 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 3 ≤ G.m + 2 * (G.k - 1) by omega),
        if_pos (show (G.m + 2 * i - 3 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 3 - G.m + 3) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega
  · refine ⟨G.m + 2 * (G.k - 1) + l, by omega, ?_, ?_⟩
    · rw [mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m by omega),
        if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m + 2 * (G.k - 1) by omega),
        show G.m + 2 * (G.k - 1) + l - G.m - 2 * (G.k - 1) = l by omega]
    · simp only [mergedDecreasingWordParity, Nat.even_iff]
      by_cases h : (l - 1) % 2 = 0
      · simp [h]; omega
      · simp [h]; omega

theorem mem_of_pos (G : GridData) {p : ℕ} (hp : p ≤ 2 * G.m + 2 * (G.k - 1)) :
    (∃ x ∈ G.lam, x.1 = G.mergedDecreasingWordPiZeroDZero p) ∨ ∃ x ∈ G.parD0, x.1 = G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  by_cases h1 : p ≤ G.m
  · exact Or.inl ⟨(G.a p, decide (Even (G.m - p))), mem_lam.2 (Or.inl ⟨p, h1, rfl⟩), by simp [mergedDecreasingWordPiZeroDZero, h1]⟩
  by_cases h2 : p ≤ G.m + 2 * (G.k - 1)
  · by_cases h3 : (p - G.m) % 2 = 1
    · refine Or.inr ⟨((G.v ((p - G.m + 3) / 2) : ℚ), true), mem_discrete_parameter_iff.2 (Or.inl ⟨mem_cloud.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
    · refine Or.inl ⟨(G.vHalf ((p - G.m + 2) / 2), true), mem_lam.2 (Or.inr ⟨mem_cloudHalf.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
  · refine Or.inr ⟨(-(G.b (p - G.m - 2 * (G.k - 1)) : ℚ), decide (Even (p - G.m - 2 * (G.k - 1) - 1))),
      mem_discrete_parameter_iff.2 (Or.inr ⟨_, by omega, by omega, rfl⟩), ?_⟩
    simp [mergedDecreasingWordPiZeroDZero, h1, h2]

theorem interlaced_pi_zero_and_D0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε →
    IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  intro G n lam ε mu ε' hga hvb ⟨hA, q, hq, hS⟩ ⟨hB, q', hq', hD⟩ x y hlt hbtw
  rw [parPi_zero] at hS
  set N := 2 * G.m + 2 * (G.k - 1) with hN
  have hV : ∀ z : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu z = ((Sum.elim q q' z : ℚ) : ℝ) := by
    rintro (a | b)
    · exact hq a
    · exact hq' b
  have key : ∀ z : Fin (n + 1) ⊕ Fin n, ∃ p ≤ N, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p ∧
      xor (Sum.elim ε ε' z) z.isLeft = G.mergedDecreasingWordParity p := by
    rintro (a | b)
    · have hm : (q a, ε a) ∈ G.lam := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_pos_of_mem_lam hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
    · have hm : (q' b, ε' b) ∈ G.parD0 := by rw [hD]; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_position_of_mem_D0 hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
  have surj : ∀ p ≤ N, ∃ z : Fin (n + 1) ⊕ Fin n, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p := by
    intro p hp
    rcases G.mem_of_pos hp with ⟨x, hx, hx1⟩ | ⟨x, hx, hx1⟩
    · rw [hS] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inl a, hx1⟩
    · rw [hD] at hx
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inr b, hx1⟩
  obtain ⟨px, hpx, hx1, hx2⟩ := key x
  obtain ⟨py, hpy, hy1, hy2⟩ := key y
  rw [hV, hV, hx1, hy1, Rat.cast_lt] at hlt
  have hlt' : px < py := by
    by_contra h
    rcases (not_lt.1 h).eq_or_lt with h | h
    · subst h; exact lt_irrefl _ hlt
    · exact lt_asymm hlt (G.merged_word_strict_anti hga hvb h hpx)
  have hsucc : py = px + 1 := by
    by_contra h
    obtain ⟨z, hz⟩ := surj (px + 1) (by omega)
    refine hbtw z ⟨?_, ?_⟩
    · rw [hV, hV, hy1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (by omega) hpy
    · rw [hV, hV, hx1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (Nat.lt_succ_self px) (by omega)
  have hpar : G.mergedDecreasingWordParity py = !G.mergedDecreasingWordParity px := by
    subst hsucc; simp only [mergedDecreasingWordParity]
    by_cases h : (G.m + px) % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [← hx2, ← hy2] at hpar
  revert hpar
  cases Sum.elim ε ε' x <;> cases Sum.elim ε ε' y <;> cases x.isLeft <;> cases y.isLeft <;> decide

end GlobalTheory.SignedHC.GridData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InterlacedSignedParametersStatement
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interlaced_signed_parameters : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  first | exact @GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 | exact GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 | (intros; apply GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGap
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

theorem isEnum_mem {n : ℕ} {S : Finset (ℚ × Bool)} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε)
    (a : Fin n) : ∃ x ∈ S, lam a = (x.1 : ℝ) ∧ ε a = x.2 := by
  obtain ⟨-, q, hq, rfl⟩ := h
  exact ⟨(q a, ε a), Finset.mem_image_of_mem _ (Finset.mem_univ a), hq a, rfl⟩

variable {G : GridData}

theorem v_add_two_le_of_gaps (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) :
    ∀ d i, 2 ≤ i → i + d + 1 ≤ G.k → G.v (i + d + 1) + 2 ≤ G.v i := by
  intro d
  induction d with
  | zero => intro i hi hk; exact hv i hi (by omega)
  | succ d ih =>
    intro i hi hk
    have h1 := ih i hi (by omega)
    have h2 := hv (i + d + 1) (by omega) (by omega)
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega]
    omega

theorem v_sep_of_gaps (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) {i j : ℕ} (hi : 2 ≤ i) (hik : i ≤ G.k)
    (hj : 2 ≤ j) (hjk : j ≤ G.k) (h : G.v j < G.v i) : G.v j + 2 ≤ G.v i := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    exact v_add_two_le_of_gaps hv d i hi hjk
  · omega
  · have := G.v_anti j i hj hij hik; omega

theorem v_le_v_two {i : ℕ} (hi : 2 ≤ i) (hik : i ≤ G.k) : G.v G.k ≤ G.v i ∧ G.v i ≤ G.v 2 := by
  constructor
  · rcases hik.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti i G.k hi h le_rfl).le
  · rcases hi.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti 2 i le_rfl h hik).le

theorem b_add_le_of_gaps {H : ℝ} (hH : 0 ≤ H) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) :
    ∀ d l, 1 ≤ l → l + d + 1 ≤ G.m → (G.b l : ℝ) + H ≤ G.b (l + d + 1) := by
  intro d
  induction d with
  | zero => intro l hl hm; exact hb l hl (by omega)
  | succ d ih =>
    intro l hl hm
    have h1 := ih l hl (by omega)
    have h2 := hb (l + d + 1) (by omega) (by omega)
    rw [show l + (d + 1) + 1 = l + d + 1 + 1 by omega]
    linarith

theorem b_sep_of_gaps {H : ℝ} (hH : 0 ≤ H) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) {l l' : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ G.m) (hl' : 1 ≤ l') (hlm' : l' ≤ G.m) (h : l < l') : (G.b l : ℝ) + H ≤ G.b l' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  exact b_add_le_of_gaps hH hb d l hl hlm'

theorem b_abs_of_gaps {H : ℝ} (hH : 0 ≤ H) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) {l l' : ℕ}
    (hl : 1 ≤ l) (hlm : l ≤ G.m) (hl' : 1 ≤ l') (hlm' : l' ≤ G.m) (h : l ≠ l') : H ≤ |(G.b l : ℝ) - G.b l'| := by
  rcases lt_or_gt_of_ne h with h | h
  · have := b_sep_of_gaps hH hb hl hlm hl' hlm' h
    rw [abs_sub_comm]; exact le_abs.2 (Or.inl (by linarith))
  · have := b_sep_of_gaps hH hb hl' hlm' hl hlm h
    exact le_abs.2 (Or.inl (by linarith))

theorem b_one_le {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ G.m) : G.b 1 ≤ G.b l := by
  rcases hl.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.b_mono 1 l le_rfl h hlm).le

theorem a_real (i : ℕ) : ((G.a i : ℚ) : ℝ) = (G.v 2 : ℝ) + 1 / 2 + ((G.m : ℝ) + 1 - i) * G.ga := by
  simp only [GridData.a]; push_cast; ring

theorem vHalf_real (i : ℕ) : ((G.vHalf i : ℚ) : ℝ) = (G.v i : ℝ) - 1 / 2 := by
  simp only [GridData.vHalf]; push_cast; ring

theorem a_sub_vHalf {i j : ℕ} (hi : i ≤ G.m) (hj : 2 ≤ j) (hjk : j ≤ G.k) :
    (G.ga : ℝ) + 1 ≤ ((G.a i : ℚ) : ℝ) - ((G.vHalf j : ℚ) : ℝ) := by
  rw [a_real, vHalf_real]
  have h1 : (G.v j : ℝ) ≤ G.v 2 := by exact_mod_cast (v_le_v_two hj hjk).2
  have h2 : (i : ℝ) ≤ G.m := by exact_mod_cast hi
  have h3 : (0 : ℝ) ≤ G.ga := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 h2) h3]

theorem a_abs_sub {i j : ℕ} (h : i ≠ j) : (G.ga : ℝ) ≤ |((G.a i : ℚ) : ℝ) - ((G.a j : ℚ) : ℝ)| := by
  rw [a_real, a_real]
  have h3 : (0 : ℝ) ≤ G.ga := by positivity
  rcases lt_or_gt_of_ne h with h | h
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ j - i - 1) h3]))
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ i - j - 1) h3]))

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.SignedHC.GridData

variable {G : GridData}

theorem lam_wide {H : ℝ} (hH : 2 ≤ H) (hga : H ≤ G.ga) (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) :
    ∀ x ∈ G.lam, ∀ y ∈ G.lam, ((y.1 : ℚ) : ℝ) < x.1 → 2 ≤ ((x.1 : ℚ) : ℝ) - y.1 := by
  intro x hx y hy hxy
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hx1, -⟩ <;> rcases mem_lam.1 hy with ⟨j, hj, rfl⟩ | ⟨hy1, -⟩
  · simp only at hxy ⊢
    have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ hxy
    have := a_abs_sub (G := G) hij
    rw [abs_of_pos (by linarith)] at this
    linarith
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloudHalf.1 hy1
    simp only at hxy ⊢
    rw [hye]
    have := a_sub_vHalf (G := G) hi hj2 hjk
    linarith
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloudHalf.1 hx1
    simp only at hxy ⊢
    rw [hxe] at hxy
    have := a_sub_vHalf (G := G) hj hi2 hik
    linarith
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloudHalf.1 hx1
    obtain ⟨j, hj2, hjk, hye⟩ := mem_cloudHalf.1 hy1
    rw [hxe, hye, vHalf_real, vHalf_real] at hxy ⊢
    have h1 : G.v j < G.v i := by
      have : (G.v j : ℝ) < G.v i := by linarith
      exact_mod_cast this
    have := v_sep_of_gaps hv hi2 hik hj2 hjk h1
    have : (G.v j : ℝ) + 2 ≤ G.v i := by exact_mod_cast this
    linarith

theorem lam_gap {H : ℝ} (hH : 2 ≤ H) (hga : H ≤ G.ga) :
    ∀ x ∈ G.lam, ∀ y ∈ G.lam, x.2 ≠ y.2 → H ≤ |((x.1 : ℚ) : ℝ) - y.1| := by
  intro x hx y hy hs
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hx1, hx2⟩ <;> rcases mem_lam.1 hy with ⟨j, hj, rfl⟩ | ⟨hy1, hy2⟩
  · have hij : i ≠ j := by rintro rfl; exact hs rfl
    exact hga.trans (a_abs_sub hij)
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloudHalf.1 hy1
    simp only
    rw [hye]
    have := a_sub_vHalf (G := G) hi hj2 hjk
    exact le_abs.2 (Or.inl (by linarith))
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloudHalf.1 hx1
    simp only
    rw [hxe]
    have := a_sub_vHalf (G := G) hj hi2 hik
    exact le_abs.2 (Or.inr (by linarith))
  · exact absurd (hx2.trans hy2.symm) hs

theorem two_le_sub_of_mem_parD0_of_lt {H : ℝ} (hH : 2 ≤ H) (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i)
    (hvb : 2 ≤ G.v G.k + G.b 1) (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) :
    ∀ x ∈ G.parD0, ∀ y ∈ G.parD0, ((y.1 : ℚ) : ℝ) < x.1 → 2 ≤ ((x.1 : ℚ) : ℝ) - y.1 := by
  intro x hx y hy hxy
  have cl : ∀ i l, 2 ≤ i → i ≤ G.k → 1 ≤ l → l ≤ G.m → (2 : ℝ) ≤ (G.v i : ℝ) + G.b l := by
    intro i l hi hik hl hlm
    have h1 := (v_le_v_two (G := G) hi hik).1
    have h2 := b_one_le (G := G) hl hlm
    have : (2 : ℤ) ≤ G.v i + G.b l := by omega
    exact_mod_cast this
  rcases mem_discrete_parameter_iff.1 hx with ⟨hx1, -⟩ | ⟨l, hl, hlm, rfl⟩ <;>
    rcases mem_discrete_parameter_iff.1 hy with ⟨hy1, -⟩ | ⟨l', hl', hlm', rfl⟩
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloud.1 hx1
    obtain ⟨j, hj2, hjk, hye⟩ := mem_cloud.1 hy1
    rw [hxe, hye] at hxy ⊢
    push_cast at hxy ⊢
    have h1 : G.v j < G.v i := by exact_mod_cast hxy
    have := v_sep_of_gaps hv hi2 hik hj2 hjk h1
    have : (G.v j : ℝ) + 2 ≤ G.v i := by exact_mod_cast this
    linarith
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloud.1 hx1
    rw [hxe]
    simp only
    push_cast
    linarith [cl i l' hi2 hik hl' hlm']
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloud.1 hy1
    rw [hye] at hxy
    simp only at hxy
    push_cast at hxy
    linarith [cl j l hj2 hjk hl hlm]
  · simp only at hxy ⊢
    push_cast at hxy ⊢
    have hll : l < l' := by
      by_contra h
      rcases (not_lt.1 h).eq_or_lt with rfl | h
      · exact lt_irrefl _ hxy
      · have := G.b_mono l' l hl' h hlm
        have : (G.b l' : ℝ) < G.b l := by exact_mod_cast this
        linarith
    have := b_sep_of_gaps (by linarith) hb hl hlm hl' hlm' hll
    linarith

theorem le_abs_sub_of_mem_parD0_of_ne_sign {H : ℝ} (hH : 2 ≤ H) (hvb : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) :
    ∀ x ∈ G.parD0, ∀ y ∈ G.parD0, x.2 ≠ y.2 → H ≤ |((x.1 : ℚ) : ℝ) - y.1| := by
  intro x hx y hy hs

  have cl : ∀ i l, 2 ≤ i → i ≤ G.k → 1 ≤ l → l ≤ G.m → decide (Even (l - 1)) = false →
      H ≤ (G.v i : ℝ) + G.b l := by
    intro i l hi hik hl hlm hsl
    have hl2 : 2 ≤ l := by
      rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | h
      · simp at hsl
      · exact h
    have h1 := (v_le_v_two (G := G) hi hik).1
    have h2 := b_sep_of_gaps (by linarith) hb le_rfl (by omega) (by omega) hlm (by omega : 1 < l)
    have h3 : (G.v G.k : ℝ) ≤ G.v i := by exact_mod_cast h1
    have h4 : (2 : ℝ) ≤ G.v G.k + G.b 1 := by exact_mod_cast hvb
    linarith
  rcases mem_discrete_parameter_iff.1 hx with ⟨hx1, hx2⟩ | ⟨l, hl, hlm, rfl⟩ <;>
    rcases mem_discrete_parameter_iff.1 hy with ⟨hy1, hy2⟩ | ⟨l', hl', hlm', rfl⟩
  · exact absurd (hx2.trans hy2.symm) hs
  · obtain ⟨i, hi2, hik, hxe⟩ := mem_cloud.1 hx1
    rw [hxe]
    simp only at hs ⊢
    rw [hx2] at hs
    have := cl i l' hi2 hik hl' hlm' (by simpa [eq_comm] using hs)
    push_cast
    exact le_abs.2 (Or.inl (by linarith))
  · obtain ⟨j, hj2, hjk, hye⟩ := mem_cloud.1 hy1
    rw [hye]
    simp only at hs ⊢
    rw [hy2] at hs
    have := cl j l hj2 hjk hl hlm (by simpa using hs)
    push_cast
    exact le_abs.2 (Or.inr (by linarith))
  · simp only at hs ⊢
    have hll : l ≠ l' := by rintro rfl; exact hs rfl
    have := b_abs_of_gaps (by linarith) hb hl hlm hl' hlm' hll
    push_cast
    rw [abs_sub_comm] at this
    rwa [show -(G.b l : ℝ) - -(G.b l' : ℝ) = (G.b l' : ℝ) - G.b l by ring]

theorem pi_zero_and_D0_spacing : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {H : ℝ}, 2 ≤ H → H ≤ G.ga →
    (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 →
    (∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a c, a < c → 2 ≤ lam a - lam c) ∧ (∀ a c, a < c → 2 ≤ mu a - mu c) ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam H ∧
      Formalism.QuantumDeterminants.GapAtLeast ε' mu H := by
  intro G n lam ε mu ε' H hH hga hv hvb hb hl hm
  rw [G.parPi_zero] at hl
  refine ⟨fun a c hac => ?_, fun a c hac => ?_, fun a c hs => ?_, fun a c hs => ?_⟩
  · obtain ⟨x, hx, hxa, -⟩ := isEnum_mem hl a
    obtain ⟨y, hy, hyc, -⟩ := isEnum_mem hl c
    have := hl.1 hac
    rw [hxa, hyc] at this ⊢
    exact lam_wide hH hga hv x hx y hy this
  · obtain ⟨x, hx, hxa, -⟩ := isEnum_mem hm a
    obtain ⟨y, hy, hyc, -⟩ := isEnum_mem hm c
    have := hm.1 hac
    rw [hxa, hyc] at this ⊢
    exact two_le_sub_of_mem_parD0_of_lt hH hv hvb hb x hx y hy this
  · obtain ⟨x, hx, hxa, hxe⟩ := isEnum_mem hl a
    obtain ⟨y, hy, hyc, hye⟩ := isEnum_mem hl c
    rw [hxa, hyc]
    exact lam_gap hH hga x hx y hy (by rw [← hxe, ← hye]; exact hs)
  · obtain ⟨x, hx, hxa, hxe⟩ := isEnum_mem hm a
    obtain ⟨y, hy, hyc, hye⟩ := isEnum_mem hm c
    rw [hxa, hyc]
    exact le_abs_sub_of_mem_parD0_of_ne_sign hH hvb hb x hx y hy (by rw [← hxe, ← hye]; exact hs)

end GlobalTheory.SignedHC.GridData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGapStatement
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameters_spacing_and_gap : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {H : ℝ}, 2 ≤ H → H ≤ G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 → (∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a c, a < c → 2 ≤ lam a - lam c) ∧ (∀ a c, a < c → 2 ≤ mu a - mu c) ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam H ∧ Formalism.QuantumDeterminants.GapAtLeast ε' mu H := by
  first | exact @GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing | exact GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing | (intros; apply GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsInterlacedSubSingleOfSpread
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsInterlacedSubSingleOfSpread
namespace GlobalTheory.SepReal

theorem interlaced_sub_single : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ},
    GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) →
      (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  intro n ε lam ε' mu hI hw hm hne s
  have h01 : ∀ a, (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 0 ∨ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 1 := by
    intro a
    by_cases h : a = s
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hb : ∀ a, 0 ≤ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ∧ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ≤ 1 := by
    intro a
    rcases h01 a with h | h <;> rw [h] <;> norm_num
  have key : ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim (lam - Pi.single s 1) mu y < Sum.elim (lam - Pi.single s 1) mu x ↔
      Sum.elim lam mu y < Sum.elim lam mu x := by
    rintro (a | i) (c | j)
    · simp only [Sum.elim_inl, Pi.sub_apply]
      by_cases hac : a = c
      · subst hac; simp
      · have hw' := hw a c hac
        have ha := h01 a
        have hc := h01 c
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = da at ha
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) c = dc at hc
        rcases le_abs.1 hw' with h | h <;> rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
          constructor <;> intro h' <;> linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hba := hb a
      constructor
      · intro h; linarith
      · intro h; have := hm a j h; linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hbc := hb c
      constructor
      · intro h
        by_contra h'
        have hlt : mu i < lam c := lt_of_le_of_ne (not_lt.1 h') (fun e => hne c i e.symm)
        have := hm c i hlt
        linarith
      · intro h; linarith
    · simp
  intro x y h hz
  rw [key] at h
  exact hI x y h (fun z hz' => hz z ⟨(key z y).2 hz'.1, (key x z).2 hz'.2⟩)

end GlobalTheory.SepReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsInterlacedSubSingleOfSpreadStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInterlaced_sub_single_of_spread : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}, GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) → (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  first | exact @GlobalTheory.SepReal.interlaced_sub_single | exact GlobalTheory.SepReal.interlaced_sub_single | (intros; apply GlobalTheory.SepReal.interlaced_sub_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquiv
namespace GlobalTheory.SepReal

private def optSumLeft (α β : Type) : Option (α ⊕ β) ≃ Option α ⊕ β where
  toFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | _) <;> rfl

theorem exists_signs_equiv {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card) :
    ∃ e : Option (Fin n) ≃ Fin (n + 1), Signs e ε ε' := by
  classical
  have hF : Fintype.card {a // ¬ ε a = true} = Fintype.card {i // ¬ ε' i = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Bool.not_eq_true] using h
  have hT : Fintype.card {a // ε a = true} = Fintype.card (Option {i // ε' i = true}) := by
    have h1 := Fintype.card_subtype_compl (fun a => ε a = true)
    have h2 := Fintype.card_subtype_compl (fun i => ε' i = true)
    have h3 := Fintype.card_subtype_le (fun a => ε a = true)
    have h4 := Fintype.card_subtype_le (fun i => ε' i = true)
    simp only [Fintype.card_fin] at h1 h2 h3 h4
    rw [Fintype.card_option]
    omega
  let eT := Fintype.equivOfCardEq hT
  let eF := Fintype.equivOfCardEq hF
  let e : Option (Fin n) ≃ Fin (n + 1) :=
    ((Equiv.optionCongr (Equiv.sumCompl fun i => ε' i = true).symm).trans
      (optSumLeft _ _)).trans ((Equiv.sumCongr eT.symm eF.symm).trans (Equiv.sumCompl fun a => ε a = true))
  refine ⟨e, ?_, ?_⟩
  · show ε ((eT.symm none : {a // ε a = true}) : Fin (n + 1)) = true
    exact (eT.symm none).2
  · intro i
    by_cases hi : ε' i = true
    · have : e (some i) = ((eT.symm (some ⟨i, hi⟩) : {a // ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this, (eT.symm (some ⟨i, hi⟩)).2, hi]
    · have : e (some i) = ((eF.symm ⟨i, hi⟩ : {a // ¬ ε a = true}) : Fin (n + 1)) := by
        simp [e, Equiv.sumCompl, hi, optSumLeft]
      rw [this]
      have := (eF.symm ⟨i, hi⟩).2
      simp only [Bool.not_eq_true] at this hi
      rw [this, hi]

end GlobalTheory.SepReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquivStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card → ∃ e : Option (Fin n) ≃ Fin (n + 1), GlobalTheory.SepReal.Signs e ε ε' := by
  first | exact @GlobalTheory.SepReal.exists_signs_equiv | exact GlobalTheory.SepReal.exists_signs_equiv | (intros; apply GlobalTheory.SepReal.exists_signs_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

private theorem dualPar_dualPar' (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  rw [Finset.image_image]
  simp [Function.comp_def]

private theorem shift_zero_lemma_2 (S : SPar) : GlobalTheory.SignedHC.shift 0 S = S := by
  unfold GlobalTheory.SignedHC.shift
  simp

private theorem exists_par_of_gridData_bounds {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {ε : Fin (n + 1) → Bool}
    {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {B : ℝ}
    (hke : Even G.k) (hme : Even G.m) (hm2 : 2 ≤ G.m) (hn : n + 1 = G.k + G.m) (h3 : 3 ≤ n)
    (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hvk : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.b (l + 1))
    (hga : 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.ga) (hvk0 : 0 ≤ G.v G.k) (hb1 : 0 < G.b 1)
    (ha0 : ((G.a 0 : ℚ) : ℝ) ≤ B) (hbm : (G.b G.m : ℝ) ≤ B)
    (hl : IsEnum (G.parPi 0) lam ε) (hm : IsEnum G.parD0 mu ε') :
    ∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu B := by
  have hga0 : 0 < G.ga := by
    have h0 : (0 : ℝ) < 1000 * ((n : ℝ) + 1) ^ 3 := by positivity
    exact_mod_cast h0.trans_le hga
  have hH : (2 : ℝ) ≤ 1000 * ((n : ℝ) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hvk1 : 1 ≤ G.v G.k + G.b 1 := by omega
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.card_minus_signs_half_of_even hme hga0 hl hm
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv ε ε' (hc.trans hc'.symm)
  obtain ⟨hHl, hHm⟩ := GlobalTheory.T.harish_chandra_param_of_even hke hme hn hl hm
  have hw := GlobalTheory.T.interlaced_signed_parameters hga0 hvk1 hl hm
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parameters_separated_by_one hga0 hv (by omega) hl hm
  obtain ⟨hwl, hwm, hgl, hgm⟩ := GlobalTheory.T.parameters_spacing_and_gap hH hga hv hvk hb hl hm
  have habs : ∀ a c, a ≠ c → 2 ≤ |lam a - lam c| := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact (hwl a c h).trans (le_abs_self _)
    · rw [abs_sub_comm]
      exact (hwl c a h).trans (le_abs_self _)
  have hB := GlobalTheory.T.signed_parameters_bounded hvk0 hb1 ha0 hbm hl hm
  have hk2 := G.two_le_k
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => ε' i = false)
  have hneg : ∃ i, ε' i = false := by
    have hpos : 0 < (Finset.univ.filter fun i => ε' i = false).card := by
      rw [hc']
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hpos : (Finset.univ.filter fun i => ε' i = false).card ≤ (Finset.univ.filter fun i => ε' i = true).card := by
    have heq : (Finset.univ.filter fun i => ¬ ε' i = false) = Finset.univ.filter fun i => ε' i = true := by
      ext i
      simp
    rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
    omega
  exact ⟨e, he, h3, hHl, hHm, hw, GlobalTheory.T.isInterlaced_sub_single_of_spread hw habs hs1 hs2, hwl, hwm, hgl, hgm, hneg, hpos, hB⟩

theorem realInputPar : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ)
    (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε →
    IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧
      Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  intro _ _ _
  refine ⟨0, fun D large₂ _ _ hS T L μ0 _ Gr W M _ => ?_⟩
  intro τ ε lam ε' mu hlam hmu
  obtain ⟨hv, hvk, hb, hga, hvk0, hb1, ha0, hbm, hb1', hb4⟩ := GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds D large₂ hS τ
  have hl : IsEnum ((GlobalTheory.ChiGrid.num D 1 τ).parPi 0) lam ε := hlam
  have hD : dualPar (parB (Ptw D) 0 τ) = (GlobalTheory.ChiGrid.num D 1 τ).parD0 := by
    rw [← GlobalTheory.SignedHC.GridData.parD_zero_zero, parB, ← parV_zero D 1 (Nat.zero_le _) τ, dualPar_dualPar']
    show GlobalTheory.SignedHC.shift (if Odd (0 + 0) then -(1 / 2) else 0) _ = _
    rw [if_neg (by decide), shift_zero_lemma_2]
  have hm' : IsEnum (GlobalTheory.ChiGrid.num D 1 τ).parD0 mu ε' := hD ▸ hmu
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  refine ⟨exists_par_of_gridData_bounds (n := D.R.r) D.R.k_even D.R.m_even h2m
    (by show D.R.r + 1 = D.R.k + D.R.m; omega) (by omega) hv hvk hb hga hvk0 hb1 ha0 hbm hl hm', ?_,
    Real.log_nonneg hb1'⟩
  have hbpos : 0 < large₂.sc.b := by linarith
  show Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2) ≤ 6 * Real.log large₂.sc.b
  have h6 := Real.log_pow large₂.sc.b 6
  push_cast at h6
  rw [← h6]
  apply Real.log_le_log (by positivity)
  calc 8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2 ≤ large₂.sc.b ^ 4 * large₂.sc.b ^ 2 := by gcongr
    _ = large₂.sc.b ^ 6 := by ring

end GlobalTheory.SepPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScaleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingHypotheses_gridParameters_largeScale : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ) (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε → IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧ Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  first | exact @GlobalTheory.SepPer.realInputPar | exact GlobalTheory.SepPer.realInputPar | (intros; apply GlobalTheory.SepPer.realInputPar <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

theorem isEnum_cast' {S : SPar} {n k : ℕ} (h : k = n) {lam : Fin n → ℝ} {ε : Fin n → Bool} (hE : IsEnum S lam ε) :
    IsEnum S (fun i : Fin k => lam (Fin.cast h i)) (fun i => ε (Fin.cast h i)) := by
  subst h
  simpa using hE

theorem UH_mul' {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem conj_mul' {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (x y : Matrix (Fin n) (Fin n) ℂ) :
    B * (x * y) * B⁻¹ = B * x * B⁻¹ * (B * y * B⁻¹) := by
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  calc B * (x * y) * B⁻¹ = B * x * (B⁻¹ * B) * y * B⁻¹ := by rw [hBi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = B * x * B⁻¹ * (B * y * B⁻¹) := by simp only [Matrix.mul_assoc]

end GlobalTheory.PackLoc

end
