module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMul
open Polynomial

namespace GlobalTheory

theorem rcout_coeff_succ {K : Type} [NormedField K] (g : K[X]) (a : K) (k : ℕ) :
    ((X - C a) * g).coeff (k + 1) = g.coeff k - a * g.coeff (k + 1) := by
  rw [mul_comm, coeff_mul_X_sub_C]; ring

theorem rcout_coeff_zero {K : Type} [NormedField K] (g : K[X]) (a : K) :
    ((X - C a) * g).coeff 0 = -(a * g.coeff 0) := by
  rw [mul_coeff_zero]; simp

theorem rcout_ultra {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem newton_step_root_outside_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  intro K _ _ g a ρ d hρ ha hle hlt
  set M := ‖g.coeff d‖ * ρ ^ d with hM
  have hMpos : 0 < M := by
    have := hlt (d + 1) (Nat.lt_succ_self d)
    exact lt_of_le_of_lt (by positivity) this
  have hapos : 0 < ‖a‖ := hρ.trans ha

  have hshift : ∀ k, ‖g.coeff k‖ * ρ ^ (k + 1) ≤ ρ * M := by
    intro k
    have := hle k
    calc ‖g.coeff k‖ * ρ ^ (k + 1) = ρ * (‖g.coeff k‖ * ρ ^ k) := by ring
      _ ≤ ρ * M := mul_le_mul_of_nonneg_left this hρ.le
  have hρM : ρ * M < ‖a‖ * M := mul_lt_mul_of_pos_right ha hMpos

  have haterm : ∀ j, ‖a * g.coeff j‖ * ρ ^ j = ‖a‖ * (‖g.coeff j‖ * ρ ^ j) := by
    intro j; rw [norm_mul]; ring

  have hup : ∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖a‖ * M := by
    intro j
    have hpj : 0 ≤ ρ ^ j := by positivity
    cases j with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
      exact mul_le_mul_of_nonneg_left (hle 0) hapos.le
    | succ k =>
      rw [rcout_coeff_succ]
      calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
          ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
        _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
            max_mul_of_nonneg _ _ hpj
        _ ≤ ‖a‖ * M := by
            apply max_le
            · exact (hshift k).trans hρM.le
            · rw [haterm]; exact mul_le_mul_of_nonneg_left (hle (k + 1)) hapos.le

  have hupl : ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖a‖ * M := by
    intro j hj
    have hpj : 0 ≤ ρ ^ j := by positivity
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [rcout_coeff_succ]
    calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hpj
      _ < ‖a‖ * M := by
          apply max_lt
          · exact lt_of_le_of_lt (hshift k) hρM
          · rw [haterm]; exact mul_lt_mul_of_pos_left (hlt (k + 1) hj) hapos

  have hlow : ‖a‖ * M ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
    have hpd : 0 < ρ ^ d := by positivity
    cases d with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
    | succ k =>
      rw [rcout_coeff_succ]
      set c := g.coeff k - a * g.coeff (k + 1)
      have key : a * g.coeff (k + 1) = g.coeff k - c := by simp [c]
      have h1 : ‖a‖ * M = ‖g.coeff k - c‖ * ρ ^ (k + 1) := by
        rw [← key, haterm]
      have h2 : ‖g.coeff k - c‖ * ρ ^ (k + 1) ≤
          max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖c‖ * ρ ^ (k + 1)) := by
        rw [← max_mul_of_nonneg _ _ hpd.le]
        exact mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpd.le
      rcases le_max_iff.mp (h1 ▸ h2 : ‖a‖ * M ≤ _) with h | h
      · exact absurd (lt_of_le_of_lt ((hshift k)) hρM) (not_lt.mpr h)
      · exact h
  exact ⟨fun j => (hup j).trans hlow, fun j hj => (hupl j hj).trans_le hlow⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMulStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  first | exact @GlobalTheory.newton_step_root_outside_disc | exact GlobalTheory.newton_step_root_outside_disc | (intros; apply GlobalTheory.newton_step_root_outside_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonLastDominantIndexMulXSubC
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonLastDominantIndexMulXSubC
open Polynomial

namespace GlobalTheory

theorem newton_step_root_in_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ),
      0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧
        ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j <
          ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  intro K _ _ g a ρ d hρ ha hle hlt
  have hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hcoef : ∀ k, ((X - C a) * g).coeff (k + 1) = g.coeff k - g.coeff (k + 1) * a := by
    intro k
    rw [mul_comm]
    exact coeff_mul_X_sub_C
  have hcoef0 : ((X - C a) * g).coeff 0 = -a * g.coeff 0 := by
    rw [mul_coeff_zero]
    simp

  have hM : 0 < ‖g.coeff d‖ * ρ ^ d := by
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    linarith
  have hsmall : ‖g.coeff (d + 1) * a‖ < ‖g.coeff d‖ := by
    rw [norm_mul]
    have hp : 0 < ρ ^ (d + 1) := by positivity
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have hn : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    have h2 : ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1) < ‖g.coeff d‖ * ρ ^ (d + 1) := by
      calc ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1)
          = (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ‖a‖ := by ring
        _ ≤ (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
        _ < (‖g.coeff d‖ * ρ ^ d) * ρ := mul_lt_mul_of_pos_right h hρ
        _ = ‖g.coeff d‖ * ρ ^ (d + 1) := by ring
    exact lt_of_mul_lt_mul_right h2 hp.le
  have htopn : ‖((X - C a) * g).coeff (d + 1)‖ = ‖g.coeff d‖ := by
    rw [hcoef d, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hsmall.ne'),
      norm_neg]
    exact max_eq_left hsmall.le
  have htop : ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) = ρ * (‖g.coeff d‖ * ρ ^ d) := by
    rw [htopn]; ring

  have key : ∀ k, ‖((X - C a) * g).coeff (k + 1)‖ * ρ ^ (k + 1) ≤
      max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
    intro k
    rw [hcoef k]
    have h1 := hsub (g.coeff k) (g.coeff (k + 1) * a)
    rw [norm_mul] at h1
    have hp : 0 ≤ ρ ^ (k + 1) := by positivity
    have hn : 0 ≤ ‖g.coeff (k + 1)‖ * ρ ^ (k + 1) := by positivity
    calc ‖g.coeff k - g.coeff (k + 1) * a‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ (‖g.coeff (k + 1)‖ * ‖a‖) * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right h1 hp
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hp
      _ ≤ max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
          apply max_le_max
          · exact le_of_eq (by ring)
          · calc ‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)
                = (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ‖a‖ := by ring
              _ ≤ (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
              _ = ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) := by ring
  constructor
  · intro j
    rw [htop]
    cases j with
    | zero =>
      rw [hcoef0, norm_mul, norm_neg, pow_zero, mul_one]
      have h0 := hle 0
      rw [pow_zero, mul_one] at h0
      calc ‖a‖ * ‖g.coeff 0‖ ≤ ρ * ‖g.coeff 0‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ ρ * (‖g.coeff d‖ * ρ ^ d) := mul_le_mul_of_nonneg_left h0 hρ.le
    | succ k =>
      exact (key k).trans (max_le (mul_le_mul_of_nonneg_left (hle k) hρ.le)
        (mul_le_mul_of_nonneg_left (hle (k + 1)) hρ.le))
  · intro j hj
    rw [htop]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (key k).trans_lt (max_lt (mul_lt_mul_of_pos_left (hlt k (by omega)) hρ)
      (mul_lt_mul_of_pos_left (hlt (k + 1) (by omega)) hρ))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonLastDominantIndexMulXSubCStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧ ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  first | exact @GlobalTheory.newton_step_root_in_disc | exact GlobalTheory.newton_step_root_in_disc | (intros; apply GlobalTheory.newton_step_root_in_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndex
open Polynomial
open Classical

namespace GlobalTheory

theorem dominantIndex_prod_X_sub_C (K : Type) [NormedField K] [IsUltrametricDist K]
    (ρ : ℝ) (hρ : 0 < ρ) (s : Multiset K) :
    ∀ c : K, c ≠ 0 →
      (∀ j, ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j ≤
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ)) ∧
      ∀ j, Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) < j →
        ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j <
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro c hc
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.filter_zero,
      Multiset.card_zero, pow_zero, coeff_C_zero]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp
      · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp h)]; simp
    · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp hj)]; simp [hc]
  | cons a s ih =>
    intro c hc
    obtain ⟨h1, h2⟩ := ih c hc
    have heq : C c * ((a ::ₘ s).map fun a => X - C a).prod =
        (X - C a) * (C c * (s.map fun a => X - C a).prod) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm]
    rw [heq, Multiset.filter_cons]
    by_cases ha : ‖a‖ ≤ ρ
    · rw [if_pos ha, Multiset.singleton_add, Multiset.card_cons]
      exact GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C K _ a ρ _ hρ ha h1 h2
    · rw [if_neg ha, zero_add]
      exact GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul K _ a ρ _ hρ (not_le.mp ha) h1 h2

theorem card_roots_closedBall_eq_dominantIndex :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  intro K _ _ _ f ρ hρ hf
  have key := dominantIndex_prod_X_sub_C K ρ hρ f.roots f.leadingCoeff
    (leadingCoeff_ne_zero.mpr hf)
  rw [C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree] at key
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndexStatement
open Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_roots_closedBall_dominant_coeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  first | exact @GlobalTheory.card_roots_closedBall_eq_dominantIndex | exact GlobalTheory.card_roots_closedBall_eq_dominantIndex | (intros; apply GlobalTheory.card_roots_closedBall_eq_dominantIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametric
open Polynomial
open Classical

namespace GlobalTheory

theorem card_roots_le_radius_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ),
      0 < ρ → f.coeff d ≠ 0 →
      ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) →
          d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧
      ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) →
          Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  intro K _ _ _ f ρ d hρ hd
  have hf : f ≠ 0 := by
    rintro rfl
    exact hd (by simp)
  obtain ⟨hA, hB⟩ := GlobalTheory.T.card_roots_closedBall_dominant_coeff K f ρ hρ hf
  set e := Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) with he
  refine ⟨fun H => ?_, fun H => ?_⟩
  · by_contra hlt
    push_neg at hlt
    have h1 := hB d hlt
    have h2 := H e
    linarith
  · by_contra hlt
    push_neg at hlt
    have h1 := H e hlt
    have h2 := hA d
    linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametricStatement
open Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_roots_closedBall_bounds_ultrametric : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ), 0 < ρ → f.coeff d ≠ 0 → ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) → d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) → Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  first | exact @GlobalTheory.card_roots_le_radius_bounds | exact GlobalTheory.card_roots_le_radius_bounds | (intros; apply GlobalTheory.card_roots_le_radius_bounds <;> assumption)
end
