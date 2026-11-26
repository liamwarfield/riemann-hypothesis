module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

theorem isUnit_l : IsUnit (l : (PreDisc l (0 : W) 1)⟦X⟧) := by
  rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧)]
  refine IsUnit.map _ ?_
  rw [← map_natCast (algebraMap W (PreDisc l (0 : W) 1))]
  exact IsLocalization.Away.algebraMap_isUnit _

def phi : PreDisc l (X : W⟦X⟧) ρ →+* (PreDisc l (0 : W) 1)⟦X⟧ :=
  IsLocalization.Away.lift (l : W⟦X⟧) (g := PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1))) (by
    rw [map_natCast]; exact isUnit_l l)

theorem phi_alg (s : W⟦X⟧) :
    phi l ρ (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) s) = PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) s :=
  IsLocalization.Away.lift_eq _ _ s

theorem phi_inv :
    phi l ρ (IsLocalization.Away.invSelf (l : W⟦X⟧)) = C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) := by
  have h := congrArg (phi l ρ) (IsLocalization.Away.mul_invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧))
  rw [map_mul, phi_alg, map_natCast, map_one] at h
  have h2 : (l : (PreDisc l (0 : W) 1)⟦X⟧) * C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) = 1 := by
    rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧), ← map_mul,
      ← map_natCast (algebraMap W (PreDisc l (0 : W) 1)), IsLocalization.Away.mul_invSelf, map_one]
  exact (isUnit_l l).mul_left_cancel (h.trans h2.symm)

def aPre (n : ℕ) : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (0 : W) 1 :=
  (coeff n : (PreDisc l (0 : W) 1)⟦X⟧ →ₗ[PreDisc l (0 : W) 1] PreDisc l (0 : W) 1).toAddMonoidHom.comp
    (phi l ρ).toAddMonoidHom

theorem aPre_apply (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n y = coeff n (phi l ρ y) := rfl

theorem aPre_mono (n a b c : ℕ) :
    aPre l ρ n (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ a * X ^ b) *
      IsLocalization.Away.invSelf (l : W⟦X⟧) ^ c) =
    if n = b then algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c else 0 := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv]
  have e : PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) ((l : W⟦X⟧) ^ a * X ^ b) *
      C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) ^ c =
      C (algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) * X ^ b := by
    simp only [map_mul, map_pow, map_natCast, map_X]; ring
  rw [e, coeff_C_mul_X_pow]

theorem norm_W_mono (hl : 0 < l) (a c : ℕ) :
    ‖algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c‖ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a := by
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  exact gauge_le l (0 : W) 1 (by positivity) (Submodule.subset_span ⟨a, 0, c, by field_simp; simp, by simp⟩)

theorem norm_aPre_le (hl : 0 < l) (hρ : ρ ≤ 1) (y : PreDisc l (X : W⟦X⟧) ρ) (n : ℕ) :
    ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
  suffices h : ∀ r : ℝ, 0 < r → y ∈ ball l (X : W⟦X⟧) ρ r → ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r from
    le_of_forall_gt_imp_ge_of_dense fun r hr =>
      h r ((norm_nonneg y).trans_lt hr) (mem_ball_of_gauge_lt l _ ρ hr) n
  have hρ' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hadd : ∀ (r : ℝ) (n : ℕ) (z w : PreDisc l (0 : W) 1), ‖z‖ * (ρ : ℝ) ^ n ≤ r → ‖w‖ * (ρ : ℝ) ^ n ≤ r →
      ‖z + w‖ * (ρ : ℝ) ^ n ≤ r := fun r n z w hz hw =>
    (mul_le_mul_of_nonneg_right (gauge_add_le_max l (0 : W) 1 z w) (by positivity)).trans
      (by rw [max_mul_of_nonneg _ _ (by positivity)]; exact max_le hz hw)
  intro r hr hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, h1, rfl⟩ := hx
    intro n
    rw [aPre_mono]
    split_ifs with hn
    · subst hn
      calc _ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a * (ρ : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (norm_W_mono l hl a c) (by positivity)
        _ ≤ r := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; exact h1
    · rw [norm_zero, zero_mul]; exact hr.le
  | zero => intro n; rw [map_zero, norm_zero, zero_mul]; exact hr.le
  | add x y _ _ hx hy => intro n; rw [map_add (f := _)]; exact hadd r n _ _ (hx n) (hy n)
  | smul s x _ hx =>
    intro n
    rw [aPre_apply, Algebra.smul_def, map_mul, phi_alg, coeff_mul]
    refine Finset.sum_induction _ (fun z => ‖z‖ * (ρ : ℝ) ^ n ≤ r) (fun z w hz hw => hadd r n z w hz hw)
      (by rw [norm_zero, zero_mul]; exact hr.le) (fun p hp => ?_)
    have hp2 : p.2 ≤ n := by have := _root_.Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega
    rw [coeff_map]
    calc ‖algebraMap W (PreDisc l (0 : W) 1) (coeff p.1 s) * coeff p.2 (phi l ρ x)‖ * (ρ : ℝ) ^ n
        ≤ (1 * ‖coeff p.2 (phi l ρ x)‖) * (ρ : ℝ) ^ p.2 :=
          mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _) (norm_nonneg _)))
            (pow_le_pow_of_le_one (by positivity) hρ' hp2) (by positivity) (by positivity)
      _ ≤ r := by rw [one_mul]; exact hx p.2

theorem norm_X_pow_le (hρ0 : 0 < ρ) (m : ℕ) :
    ‖algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m)‖ ≤ (ρ : ℝ) ^ m := by
  have := norm_toDisc_pow_le (l := l) (u := (X : W⟦X⟧)) (ρ := ρ) m hρ0
  rwa [toDisc, RingHom.comp_apply, norm_ofPre] at this

theorem norm_le_of_aPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r) : ‖y‖ ≤ r := by
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  have hco : ∀ n, aPre l ρ n y =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
    intro n
    rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have ht0 : 0 < t := hr.trans_lt ht
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ht0 (pow_pos hl c)) (show (ρ : ℝ) < 1 by exact_mod_cast hρ)
  set hd : W⟦X⟧ := ∑ m ∈ Finset.range N, C (coeff m s) * X ^ m with hhd
  obtain ⟨s', hs'⟩ : (X : W⟦X⟧) ^ N ∣ s - hd := X_pow_dvd_iff.2 fun m hm => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hhd, map_sub, coeff_C_mul_X_pow, map_sum, Finset.mem_range, hm]
  have hsplit : y = ∑ m ∈ Finset.range N, algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c +
      algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, ← Finset.sum_mul, ← map_sum, ← add_mul, ← map_add (f := _), ← hs', ← hhd, add_sub_cancel]
  rw [hsplit]
  refine (gauge_add_le_max l _ ρ _ _).trans (max_le ?_ ?_)
  · refine Finset.sum_induction _ (fun z => ‖z‖ ≤ t)
      (fun a b ha hb => (gauge_add_le_max l _ ρ a b).trans (max_le ha hb)) (by rw [norm_zero]; exact ht0.le)
      fun m _ => ?_
    have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        preMap (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C (algebraMap W _ (coeff m s) *
          IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) *
          algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m) := by
      rw [map_mul (preMap (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C), map_pow (preMap (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C), preMap_alg, preMap_inv,
        map_mul (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ))]; ring
    rw [e]
    have hpm := norm_preMap_le (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C (by simp)
      (algebraMap W _ (coeff m s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c)
    refine (norm_mul_le _ _).trans ((mul_le_mul hpm (norm_X_pow_le l ρ hρ0 m) (norm_nonneg _)
      (norm_nonneg _)).trans ?_)
    rw [← hco]; exact (h m).trans ht.le
  · have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        s' • (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ 0 * X ^ N) *
          IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
      rw [Algebra.smul_def, pow_zero, one_mul, mul_comm ((X : W⟦X⟧) ^ N) s', map_mul, mul_assoc]
    rw [e]
    refine gauge_le l _ ρ ht0 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, N, c, ?_, rfl⟩))
    rw [lt_div_iff₀ (by positivity)] at hN
    rw [pow_zero, mul_one, mul_comm]; exact hN.le

theorem continuous_aPre (hl : 0 < l) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) (n : ℕ) : Continuous (aPre l ρ n (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ ((ρ : ℝ) ^ n)⁻¹ fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact norm_aPre_le l ρ hl hρ y n

theorem norm_aPre_le_const (hl : 0 < l) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ∃ C : ℝ, ∀ n, ‖aPre l ρ n y‖ ≤ C := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(l : ℝ) ^ c / (l : ℝ) ^ 0, fun n => ?_⟩
  rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine (norm_mul_le _ _).trans ((mul_le_mul (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _)
    le_rfl (norm_nonneg _) zero_le_one).trans ?_)
  rw [one_mul]
  have := norm_W_mono (W := W) l hl 0 c
  rwa [pow_zero, map_one, one_mul] at this

theorem exists_coeff_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1),
      (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧
      (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧
      (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧
      ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  intro l _ K bk ρ hρ0 hρ1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hc := fun n => continuous_aPre l (W := Wq l bk.a) ρ hl hρ0 hρ1.le n
  let A : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1) := fun n => (aPre l ρ n).completion (hc n)
  have hA : ∀ n y, A n (ofPre l (X : bk.S) ρ y) = ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n y) := fun n y =>
    AddMonoidHom.completion_coe _ _ y
  have hAc : ∀ n, Continuous (A n) := fun n => AddMonoidHom.continuous_completion _ _
  have h2 : ∀ n y, ‖A n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
    intro n y
    refine (denseRange_ofPre l (X : bk.S) ρ).induction_on y
      (isClosed_le (((hAc n).norm).mul continuous_const) continuous_norm) fun y => ?_
    rw [hA, norm_ofPre, norm_ofPre]
    exact norm_aPre_le l ρ hl hρ1.le y n
  refine ⟨A, fun n x => ?_, h2, fun y r hr h => ?_, fun y => ?_⟩
  · change A n (ofPre l (X : bk.S) ρ (algebraMap _ _ x)) = ofPre l (0 : Wq l bk.a) 1 (algebraMap _ _ (coeff n x))
    rw [hA, aPre_apply, phi_alg, coeff_map]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    have hz' : ‖z‖ ≤ r + ε / 2 := by
      refine norm_le_of_aPre l ρ hρ0 hρ1 z _ (by positivity) fun n => ?_
      rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm, show ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) =
        A n y - A n (y - ofPre l (X : bk.S) ρ z) by rw [map_sub, sub_sub_cancel, hA]]
      refine (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)).trans ?_
      rw [add_mul]
      exact add_le_add (h n) ((h2 n _).trans hz.le)
    calc ‖y‖ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + ‖ofPre l (X : bk.S) ρ z‖ := norm_le_norm_sub_add _ _
      _ ≤ ε / 2 + (r + ε / 2) := add_le_add hz.le (by rw [norm_ofPre]; exact hz')
      _ = r + ε := by ring
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    obtain ⟨C, hC⟩ := norm_aPre_le_const l ρ hl z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) (show (0 : ℝ) < C + 1 by linarith))
      (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hρn : (ρ : ℝ) ^ n ≤ (ρ : ℝ) ^ N := pow_le_pow_of_le_one (by positivity) (by exact_mod_cast hρ1.le) hn
    rw [lt_div_iff₀ (by linarith)] at hN
    have e : A n y = A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) := by
      rw [← hA, ← map_add (f := _), sub_add_cancel]
    rw [e]
    calc ‖A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ * (ρ : ℝ) ^ n
        ≤ (‖A n (y - ofPre l (X : bk.S) ρ z)‖ + ‖aPre l ρ n z‖) * (ρ : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm]
          exact norm_add_le _ _
      _ = ‖A n (y - ofPre l (X : bk.S) ρ z)‖ * (ρ : ℝ) ^ n + ‖aPre l ρ n z‖ * (ρ : ℝ) ^ n := add_mul _ _ _
      _ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + C * (ρ : ℝ) ^ N :=
          add_le_add (h2 n _) (mul_le_mul (hC n) hρn (by positivity) hC0)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_lt_of_le hz ?_
          nlinarith [pow_nonneg (show (0 : ℝ) ≤ ρ by positivity) N]
      _ = ε := add_halves ε

end GlobalTheory.BSP.DiscSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussNorm_coeff_wittDisc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1), (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧ (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧ ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.BSP.DiscSer.exists_coeff_disc | exact GlobalTheory.BSP.DiscSer.exists_coeff_disc | (intros; apply GlobalTheory.BSP.DiscSer.exists_coeff_disc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResConjTriv

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem continuous_cConj : Continuous (GlobalTheory.TwistDet.cConj X) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om s).1 hs
  have h := GlobalTheory.TwistDet.isOpen_comap_cConj X (H := L.fixingSubgroup) (IntermediateField.fixingSubgroup_isOpen L)
  rw [Filter.mem_map]
  exact Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLs hg

theorem cycZ_cConj (l : ℕ) [Fact l.Prime] (g : GE N) :
    cycZ (F := D.host.E) (Ω := N.Om) l (GlobalTheory.TwistDet.cConj X g) = cycZ (F := D.host.E) (Ω := N.Om) l g := by
  have e : (GlobalTheory.TwistDet.cConj X g).toRingEquiv = X.cc * g.toRingEquiv * X.cc⁻¹ := by
    ext x; rfl
  change cyclotomicCharacter N.Om l (GlobalTheory.TwistDet.cConj X g).toRingEquiv = cyclotomicCharacter N.Om l g.toRingEquiv
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem auxiliaryCharacter_complexConj_invariant (i : X.Tw) (g : GE N) : eps0 X i (GlobalTheory.TwistDet.cConj X g) = eps0 X i g := by
  simp only [eps0, MonoidHom.comp_apply, cycZ_cConj]

theorem resTriv_cConj (i : X.Tw) (s : X.Sig i) (hS : SelfDual i s) (g : GE N) (hg : ResTriv i s g) :
    ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  obtain ⟨A, hA⟩ := hS
  obtain ⟨h1, h2⟩ := hg
  have h3 := hA g _ (GlobalTheory.TwistDet.cConj_apply X g)
  refine ⟨?_, by rw [auxiliaryCharacter_complexConj_invariant, h2]⟩
  set φ := IsLocalRing.residue (X.O0 i) with hφ
  have hsm : ∀ (c : X.O0 i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)), φ c = 1 → (c • M).map φ = M.map φ := by
    intro c M hc
    ext a b
    simp [hc]
  have h4 := congrArg (fun M => M.map φ) h3
  simp only [Tdual] at h4
  rw [hsm _ _ (by rw [auxiliaryCharacter_complexConj_invariant, h2]), Matrix.map_mul, Matrix.map_mul, hsm _ _ (by rw [map_pow, h2, one_pow]), h1,
    mul_one, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.transpose_map,
    Matrix.transpose_eq_one] at h4
  have hu : IsUnit (Tmat i s (GlobalTheory.TwistDet.cConj X g)).det := by
    rw [← Tgl_coe]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := congrArg (fun M => M.map φ) (Matrix.mul_nonsing_inv _ hu)
  rwa [Matrix.map_mul, h4, mul_one, Matrix.map_one _ (map_zero φ) (map_one φ)] at h5

theorem continuous_cConj_and_resTriv : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) :=
  fun _ _ X => ⟨continuous_cConj X, resTriv_cConj X⟩

end GlobalTheory.ResConjTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConjStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_and_residualTriv_complexConj : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  first | exact @GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv | exact GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv | (intros; apply GlobalTheory.ResConjTriv.continuous_cConj_and_resTriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadius
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_E_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  intro l hl K bk A _ s
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ : ((bk.ρ₀ : ℝ≥0) : ℝ) = (l : ℝ) ^ (-(1 / (bk.Ep.natDegree : ℝ))) := by
    simp [BK.ρ₀, NNReal.coe_rpow]
  have hρpos : 0 < bk.ρ₀ := by
    rw [← NNReal.coe_pos, hρ]; exact Real.rpow_pos_of_pos hl0 _
  have hρe : ((bk.ρ₀ : ℝ)) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    have : -(1 / (bk.Ep.natDegree : ℝ)) * (bk.Ep.natDegree : ℝ) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
  refine ⟨hρpos, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hρ, NNReal.coe_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))
  · rw [hρ, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hl1.le ?_
    have : 1 / (bk.Ep.natDegree : ℝ) ≤ 1 := by
      rw [div_le_one he]; exact_mod_cast bk.deg_pos
    linarith
  · have hE : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
      show (bk.Ep : (Wq l bk.a)⟦X⟧) = _
      conv_lhs => rw [bk.monic.as_sum]
      simp only [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      simp
    have hmem : algebraMap A (PreDisc l (s X) bk.ρ₀) (s bk.E) ∈ ball l (s X) bk.ρ₀ (l : ℝ)⁻¹ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hE, map_add (f := _), map_add (f := _), map_sum, map_sum]
      refine add_mem ?_ (Submodule.sum_mem _ fun i hi => ?_)
      · refine Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, ?_⟩
        · simp [hρe]
        · simp [map_pow]
      · obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
        have h2 : algebraMap A (PreDisc l (s X) bk.ρ₀) (s (C (bk.Ep.coeff i) * X ^ i)) =
            s (C c * X ^ i) • (algebraMap A (PreDisc l (s X) bk.ρ₀) ((l : A) ^ 1 * (s X) ^ 0) *
              IsLocalization.Away.invSelf (l : A) ^ 0) := by
          rw [hc, Algebra.smul_def]
          simp only [map_mul, map_natCast, map_pow, pow_one, pow_zero, mul_one]
          ring
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], rfl⟩)
    exact (norm_ofPre l (s X) bk.ρ₀ _).trans_le (gauge_le l (s X) bk.ρ₀ (by positivity) hmem)
end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  first | exact @GlobalTheory.BSP.norm_E_le_radius | exact GlobalTheory.BSP.norm_E_le_radius | (intros; apply GlobalTheory.BSP.norm_E_le_radius <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulIdemFromCenter
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem exists_central_lift {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra B Γ)
    (hx : ∀ z, x * z = z * x) (hr : ∀ h, x.coeff h ∈ f.range) :
    ∃ z ∈ Subalgebra.center A (MonoidAlgebra A Γ), ∀ h : Γ, f (z.coeff h) = x.coeff h := by
  choose c hc using hr
  let z : MonoidAlgebra A Γ := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have hz : ∀ h, f (z.coeff h) = x.coeff h := fun h => hc h
  have hco : ∀ (y : MonoidAlgebra A Γ) h, (MonoidAlgebra.mapRingHom Γ f y).coeff h = f (y.coeff h) := by
    intro y h; simp
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom Γ f) := by
    intro a b hab
    ext h
    apply hf
    rw [← hco, ← hco, hab]
  have hzx : MonoidAlgebra.mapRingHom Γ f z = x := by
    ext h
    rw [hco, hz]
  refine ⟨z, ?_, hz⟩
  rw [Subalgebra.mem_center_iff]
  intro b
  apply hinj
  rw [map_mul, map_mul, hzx, hx]

theorem card_mul_idem_from_center : ∀ (D : D7) (i : D.nd.Loc) (Γ : Type) [Group Γ] [Finite Γ] (e : MonoidAlgebra ℂ Γ), e * e = e → (∀ z, e * z = z * e) → (∃ ζ : D.nd.O i, IsPrimitiveRoot (iotaO D.nd D.naut i ζ) (Nat.card Γ)) → ∃ z ∈ Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) Γ), ∀ h : Γ, iotaO D.nd D.naut i (MonoidAlgebra.coeff z h) = (Nat.card Γ : ℂ) * e.coeff h := by
  intro D i Γ _ _ e he hc ⟨ζ, hζ⟩
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  have hco : ∀ h, ((Nat.card Γ : ℂ) • e).coeff h = (Nat.card Γ : ℂ) * e.coeff h := by
    intro h; simp
  obtain ⟨z, hz, hz'⟩ := exists_central_lift (iotaO D.nd D.naut i) hinj ((Nat.card Γ : ℂ) • e)
    (fun z => by rw [smul_mul_assoc, mul_smul_comm, hc]) (fun h => by
      rw [hco]
      have h1 := centralIdemCoeff Γ e he hc _ hζ h
      have h2 : Algebra.adjoin ℤ ({iotaO D.nd D.naut i ζ} : Set ℂ) ≤
          subalgebraOfSubring (iotaO D.nd D.naut i).range :=
        Algebra.adjoin_le (by rintro _ rfl; exact ⟨ζ, rfl⟩)
      exact h2 h1)
  exact ⟨z, hz, fun h => by rw [hz', hco]⟩

end GlobalTheory.CentralIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs
noncomputable section

namespace GlobalTheory.Pass.CentralStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepCentral := by
  intro _ D P i s
  classical
  have hcard : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g D.nd) := by
    rw [D.nd.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change _ = ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  haveI : Finite (G0g D.nd) := Nat.finite_of_card_ne_zero (hcard ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  have key : ∀ L : List (Σ k : Fin 2, D.nd.PlG k),
      let e := (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (s kv))).prod
      e * e = e ∧ ∀ z, e * z = z * e := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      obtain ⟨h1, h2⟩ := ih
      have hc := Subalgebra.mem_center_iff.1 (GlobalTheory.SeriesSupportTest.atPlace_central D a.1 a.2 _
        (D.ntypes.eSer_central a.1 (s a)))
      have hi : ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) * ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) =
          ArithmeticCylinders.atPlace D a.1 a.2 (D.ntypes.eSer a.1 (s a)) := by
        rw [GlobalTheory.SeriesSupportTest.atPlace_eq, ← map_mul, D.ntypes.eSer_idem]
      simp only [List.map_cons, List.prod_cons]
      refine ⟨?_, fun z => ?_⟩
      · rw [mul_assoc, ← mul_assoc _ (ArithmeticCylinders.atPlace D a.1 a.2 _), hc, mul_assoc, h1, ← mul_assoc, hi]
      · rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
  obtain ⟨h1, h2⟩ := key Finset.univ.toList
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i
  have hinj : Function.Injective (iotaO D.nd D.naut i) :=
    ((D.naut.iotaQC i).injective.comp (D.naut.iotaQ i).injective).comp (IsFractionRing.injective _ _)
  obtain ⟨z, hz, hz'⟩ := GlobalTheory.CentralIdem.card_mul_idem_from_center D i (G0g D.nd) _ h1 h2
    ⟨ζ, hcard ▸ hζ.map_of_injective hinj⟩
  refine ⟨⟨z, hz⟩, Finset.univ.toList, Finset.nodup_toList _, by simp, ?_⟩
  ext h
  rw [hcard]
  simpa [PairedCharacterCondition.mapCoef] using hz' h

end GlobalTheory.Pass.CentralStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffsStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_elements_from_idempotent_coeffs : StepCentral := by
  first | exact @GlobalTheory.Pass.CentralStep.main | exact GlobalTheory.Pass.CentralStep.main | (intros; apply GlobalTheory.Pass.CentralStep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedTateFilQuot
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFilQuotTied

theorem tied_tate_fil_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.TateFilteredInvariants (P.PD K) := by
  intro l _ P AI TT K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact GlobalTheory.TateFilQuot.tied_invariant_mod l P AI TT K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuotTied
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CobCrisLift

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem tmul_mem (v : V) {a : ℤ} {b : BdR} (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] (⟨b, hb⟩ : (PD.Fil a).restrictScalars Qp), by simp⟩

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    rw [AlgebraTensorModule.map_tmul]
    exact tmul_mem PD _ (PD.Fil_anti a b.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem filV_exhaustive (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.inductionOn with
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem PD v ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem φVB_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ιV_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem sub_φ_mem_Dcris (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  refine (Submodule.mem_iInf _).2 fun g => ?_
  have h1 : φVB PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : B) := by
    simp [φVB]
  rw [hx g, map_sub, φVB_act] at h1
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_sub_sub_comm, h1,
    sub_self]

theorem act_ιV_sub_mem (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g : G) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) - ιV PD (LL := LL) (V := V) x ∈
      FilV PD (LL := LL) (V := V) 0 := by
  rw [← ιV_act, ← map_sub, ← hx g]
  have h1 : ιV PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : BdR) := by
    simp [ιV]
  rw [h1]
  exact tmul_mem PD _ PD.one_mem

end General

theorem coboundary_lift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → ∀ (c : ↥(GK K) → A.V) (x : A.V ⊗[ℚ_[l]] P.R.B), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x) → x - φVB (P.PD K) (LL := LL) (V := A.V) x ∈ Dcris (P.PD K) A.ρ ∧ ∃ d ∈ DdR (P.PD K) A.ρ, ιV (P.PD K) (LL := LL) (V := A.V) x - d ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 := by
  intro l _ P AI hT K LL _ _ _ O _ _ hO A hdR c x hx
  refine ⟨sub_φ_mem_Dcris (P.PD K) A.ρ c x hx, ?_⟩
  obtain ⟨a, ha⟩ := filV_exhaustive (P.PD K) (LL := LL) (ιV (P.PD K) (LL := LL) (V := A.V) x)
  obtain ⟨w, hw, hw'⟩ := GlobalTheory.TateFilQuotTied.tied_tate_fil_quot l P AI hT K LL O hO A hdR a 0 _ ha
    (act_ιV_sub_mem (P.PD K) A.ρ c x hx)
  exact ⟨w, hw.1, hw'⟩

end GlobalTheory.CobCrisLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLiftStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_coboundary_lift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) A.ρ → ∀ (c : ↥(GK K) → A.V) (x : A.V ⊗[ℚ_[l]] P.R.B), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x) → x - φVB (P.PD K) (LL := LL) (V := A.V) x ∈ Dcris (P.PD K) A.ρ ∧ ∃ d ∈ DdR (P.PD K) A.ρ, ιV (P.PD K) (LL := LL) (V := A.V) x - d ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 := by
  first | exact @GlobalTheory.CobCrisLift.coboundary_lift | exact GlobalTheory.CobCrisLift.coboundary_lift | (intros; apply GlobalTheory.CobCrisLift.coboundary_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResDual

def CupCob {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup M']
    [Module k M'] (χ : Γ → k) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → k, IsLocallyConstant f ∧ ∀ g h, P (x g) (ρ' g (y h)) = χ g * f h - f (g * h) + f g

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i))

def IsFCoc {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) (y : ↥(DecV N v) → Fin r → X.O0 i) : Prop :=
  (fun g a => (bkP.br i v hv).toLL (y ((bkP.br i v hv).e.symm g) a)) ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ)

variable {bkP i v hv}

theorem isFCoc_iff {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i} :
    IsFCoc bkP i v hv ρ y ↔ ∃ c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv ρ),
      ∀ g a, c ((bkP.br i v hv).e g) a = (bkP.br i v hv).toLL (y g a) := by
  constructor
  · intro h
    exact ⟨_, h, fun g a => by simp only [MulEquiv.symm_apply_apply]⟩
  · rintro ⟨c, hc, h⟩
    have : (fun g a => (bkP.br i v hv).toLL (y ((bkP.br i v hv).e.symm g) a)) = c := by
      funext g a
      rw [← h, MulEquiv.apply_symm_apply]
    unfold IsFCoc
    rw [this]
    exact hc

theorem IsFCoc.continuous {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i}
    (h : IsFCoc bkP i v hv ρ y) : Continuous y := by
  obtain ⟨c, hc, e⟩ := isFCoc_iff.1 h
  refine continuous_pi fun a => ?_
  have h1 : Continuous fun g => (bkP.br i v hv).toLL (y g a) := by
    simp_rw [← e]
    exact (continuous_apply a).comp (hc.1.1.comp (bkP.br i v hv).e_cont)
  have h2 : Continuous fun g => (bkP.br i v hv).eO (y g a) := continuous_induced_rng.2 h1
  simpa [Function.comp_def] using (bkP.br i v hv).eO_symm_cont.comp h2

theorem IsFCoc.cocycle {r : ℕ} {ρ : GE N →* GL (Fin r) (X.O0 i)} {y : ↥(DecV N v) → Fin r → X.O0 i}
    (h : IsFCoc bkP i v hv ρ y) (g g' : ↥(DecV N v)) :
    y (g * g') = y g + ((ρ g : GL (Fin r) (X.O0 i)) : Matrix (Fin r) (Fin r) (X.O0 i)).mulVec (y g') := by
  have e := h.1.2 ((bkP.br i v hv).e g) ((bkP.br i v hv).e g')
  funext a
  have inj : Function.Injective (bkP.br i v hv).toLL := Subtype.val_injective.comp (bkP.br i v hv).eO.injective
  apply inj
  have e2 := congrFun e a
  simp only [← map_mul, MulEquiv.symm_apply_apply, Pi.add_apply] at e2
  rw [e2, Pi.add_apply, map_add (f := _)]
  congr 1
  simp [LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply]

end GlobalTheory.ResDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem rootT_pow_eq_untilt (e : Per.Fl l) (n : ℕ) : rootT e n ^ (l ^ n) = e.untilt := by
  induction n generalizing e with
  | zero => simp [rootT]
  | succ n ih =>
    have h : rootT e (n + 1) = rootT ((frobeniusEquiv (Per.Fl l) l).symm e) n := by
      rw [rootT, rootT, Function.iterate_succ_apply]
    rw [h, pow_succ, pow_mul, ih, ← map_pow, frobeniusEquiv_symm_pow_p]

end GlobalTheory.MemLoc

namespace GlobalTheory.BSP

theorem rootT_flat_alg_and_fix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ n : ℕ, ∃ z : Om l, ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) = (z : ℂ_[l])) ∧ ∀ (g : GQ l) (y : OCb l), (∀ n : ℕ, Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) = GlobalTheory.MemLoc.rootT y n) → Per.σF g bk.flat = y := by
  intro l _ K bk
  refine ⟨fun n => ?_, fun g y hy => ?_⟩
  · set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
    have h1 : (GlobalTheory.MemLoc.rootT bk.flat n) ^ (l ^ n) = intToOC K r := by
      rw [GlobalTheory.MemLoc.rootT_pow_eq_untilt, ← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
      exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
    set a : Om l := ((r : ↥K.1) : Om l)
    have hf : (Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos n) a
    have hroot : ((Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)).map (algebraMap (Om l) ℂ_[l])).IsRoot
        ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) := by
      have h2 := congrArg (fun x : OC l => (x : ℂ_[l])) h1
      rw [SubmonoidClass.coe_pow] at h2
      rw [coe_intToOC] at h2
      simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [h2]
      exact sub_self _
    obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
    exact ⟨z, hz.symm⟩
  · refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g bk.flat) = PreTilt.coeff n y
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g bk.flat) =
        Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => exact Eq.refl (Per.σF g bk.flat)
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : GlobalTheory.MemLoc.rootT (Per.σF g bk.flat) n = Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) := by
      rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, hit, GlobalTheory.RingBasics.untilt_σF]
    rw [GlobalTheory.MemLoc.coeff_eq_mk_rootT, GlobalTheory.MemLoc.coeff_eq_mk_rootT, hsig, hy n]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ n : ℕ, ∃ z : Om l, ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) = (z : ℂ_[l])) ∧ ∀ (g : GQ l) (y : OCb l), (∀ n : ℕ, Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) = GlobalTheory.MemLoc.rootT y n) → Per.σF g bk.flat = y := by
  first | exact @GlobalTheory.BSP.rootT_flat_alg_and_fix | exact GlobalTheory.BSP.rootT_flat_alg_and_fix | (intros; apply GlobalTheory.BSP.rootT_flat_alg_and_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.SplitBelow

theorem ef_eq_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P)
    (hN : Ideal.absNorm P = p) : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 1 := by

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmZ : ((p : ℤ) : 𝓞 E) ∈ P := by simpa using hm
  have hU : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd P hP hmZ
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one P ℤ
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpZ).mpr hmZ
  have hf : P.inertiaDeg ℤ = 1 := by
    have h := Ideal.pow_inertiaDeg p P
    rw [hN] at h
    exact Nat.pow_right_injective hp.two_le (by simpa using h)
  have het := Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 F)) P
  have hft := Ideal.inertiaDeg_tower (R := ℤ) (P.under (𝓞 F)) P
  rw [he] at het
  rw [hf] at hft
  rw [(mul_eq_one.mp het.symm).2, (mul_eq_one.mp hft.symm).2]
  exact mul_one 1

theorem splits_below_of_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by

  intro E _ _ _ p hp hd hN P hPm
  classical
  by_contra hns
  have hO : ∀ Q : HeightOneSpectrum (𝓞 E), GlobalTheory.CMVal.Over Q (below P) → Q = P := by
    intro Q hQ
    by_contra hne
    exact hns ⟨Q, P, hne, hQ, over_below P⟩
  have hq1 : ∀ q : (below P).asIdeal.primesOver (𝓞 E), q.1 = P.asIdeal := by
    intro q
    have hq := q.2
    have := hq.1
    have := hq.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (below P).ne_bot q.1
    have h := hO ⟨q.1, hq.1, hne⟩ (Ideal.LiesOver.over (P := q.1) (p := (below P).asIdeal)).symm
    exact congrArg HeightOneSpectrum.asIdeal h
  have hterm : ∀ q : (below P).asIdeal.primesOver (𝓞 E),
      q.1.ramificationIdx (OF E) * q.1.inertiaDeg (OF E) = 1 := by
    intro q
    rw [hq1 q]
    have := P.isPrime
    exact ef_eq_one (maximalRealSubfield E) E hp hd P.asIdeal hPm (hN P hPm)
  have hfr : Module.finrank (OF E) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (OF E) (maximalRealSubfield E) (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (below P).asIdeal (𝓞 E)
  rw [Finset.sum_congr rfl (fun q _ => hterm q), hfr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hle : Fintype.card ((below P).asIdeal.primesOver (𝓞 E)) ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun a b => Subtype.ext ((hq1 a).trans (hq1 b).symm))
  omega

end GlobalTheory.LamTie.SplitBelow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplitStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitsInCMField_placeBelow_of_completelySplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by
  first | exact @GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm | exact GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm | (intros; apply GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeConjugateSplit
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair

namespace GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_cong_one [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  obtain ⟨b, hb⟩ := exists_int_cong P z hz
  obtain ⟨a, ha⟩ := (hef P hP).2.2 b
  have h3 := OrderUnits.val_int_le P 1 _ (by simpa using ha)
  refine ⟨a, ?_⟩
  rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
  have := Valuation.map_sub_le _ hb h3
  rw [sub_sub_sub_cancel_left] at this
  exact this

theorem exists_cong [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (m : ℕ) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-(m : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  induction m with
  | zero => exact ⟨0, by simpa [iota_zero, zero_coord] using hz⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨t, ht, ht'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top m
    have hv : Valued.v (iota t P) = WithZero.exp (-(m : ℤ)) := by
      refine eq_exp_of_le (val_iota_le_of_mem hP m ht) fun h3 => ht' ?_
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      convert h3 using 2
      push_cast; ring
    have ht0 : iota t P ≠ 0 := fun h => by
      rw [h, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨c, hc⟩ := exists_cong_one hs hP ((iota a P - z) / iota t P) (by
      rw [map_div₀, hv, div_le_one₀ WithZero.exp_pos]; exact ha)
    refine ⟨a - t * c, ?_⟩
    have : iota (a - t * c) P - z = -(iota t P * (iota c P - (iota a P - z) / iota t P)) := by
      rw [iota_sub, iota_mul, sub_coord, mul_coord]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, hv]
    refine (mul_le_mul' le_rfl hc).trans_eq ?_
    rw [← WithZero.exp_add]
    congr 1
    push_cast; ring


end GlobalTheory.LamTie.ConjLevel
end
end
