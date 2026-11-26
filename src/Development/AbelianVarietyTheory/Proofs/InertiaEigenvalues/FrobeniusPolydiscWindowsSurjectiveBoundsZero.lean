module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrders
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedRowCoefficientMatricesDetNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMono
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMono
open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem iter_frobSymm_pow {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (m : ℕ) (y : F) : (((frobeniusEquiv F p).symm)^[m] y) ^ p ^ m = y := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

theorem norm_pw_mono {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℤ) (y y' : F) (hy : ‖y‖ ≤ ‖y'‖) : ‖pw p k y‖ ≤ ‖pw p k y'‖ := by
  unfold pw
  split_ifs with hk
  · rw [norm_pow, norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy _
  · set m := (-k).toNat
    have hN : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    have e1 := iter_frobSymm_pow p m y
    have e2 := iter_frobSymm_pow p m y'
    by_contra hc
    push_neg at hc
    have := pow_lt_pow_left₀ hc (norm_nonneg _) hN
    rw [← norm_pow, ← norm_pow, e1, e2] at this
    linarith

theorem term_norm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  intro F _ p _ _ _ h ϖ lam π x hx r j n
  unfold term
  rw [norm_mul, norm_mul (lam j * _)]
  exact mul_le_mul_of_nonneg_left (norm_pw_mono p _ _ _ (hx j)) (norm_nonneg _)

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFrobeniusWindowSeriesTermMonoStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π x : Fin h → F), (∀ j, ‖x j‖ ≤ ‖π j‖) → ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam x r j n‖ ≤ ‖term p ϖ lam π r j n‖ := by
  first | exact @GlobalTheory.PMonE.term_norm_mono | exact GlobalTheory.PMonE.term_norm_mono | (intros; apply GlobalTheory.PMonE.term_norm_mono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalOfInvMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalOfInvMul
open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

open Finset

theorem norm_det_le_one_of_entries {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, one_mul]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA _ _)

theorem norm_adjugate_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : m) : ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one_of_entries _ fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simp
    · simp [Pi.single_apply, hb]
  · rw [Matrix.updateRow_ne h]; exact hA a b

theorem norm_inv_le_one_of_det {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    [DecidableEq m] (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) (i j : m) :
    ‖A⁻¹ i j‖ ≤ 1 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd, inv_one, one_mul]
  exact norm_adjugate_le_one A hA i j

theorem norm_mul_apply_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (i j : m) :
    ‖(A * B) i j‖ ≤ 1 := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

theorem norm_mul_apply_lt_one {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A B : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ < 1) (i j : m) :
    ‖(A * B) i j‖ < 1 := by
  rw [Matrix.mul_apply]
  rcases isEmpty_or_nonempty m with hm | hm
  · simp
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image (univ : Finset m) (fun k => ‖A i k * B k j‖) univ_nonempty
  have hlt : ‖A i k₀ * B k₀ j‖ < 1 := by
    rw [norm_mul]
    calc ‖A i k₀‖ * ‖B k₀ j‖ ≤ 1 * ‖B k₀ j‖ := mul_le_mul_of_nonneg_right (hA i k₀) (norm_nonneg _)
      _ = ‖B k₀ j‖ := one_mul _
      _ < 1 := hB k₀ j
  exact lt_of_le_of_lt
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k hk => hk₀ k hk) hlt

theorem normal_of_inv_mul : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m]
    [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) →
    (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 →
    Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  intro F _ _ m _ _ N B hint hsmall hd
  have hinv : ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := norm_inv_le_one_of_det (B N) (hint N) hd
  have hunit : IsUnit (B N).det := by
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0, norm_zero] at hd; exact zero_ne_one hd
  refine ⟨⟨fun n i j => norm_mul_apply_le_one _ _ hinv (hint n) i j, ?_,
    fun n hn i j => norm_mul_apply_lt_one _ _ hinv (hsmall n hn) i j⟩, hinv⟩
  exact Matrix.nonsing_inv_mul _ hunit

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalOfInvMulStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m] [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) → (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 → Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by
  first | exact @GlobalTheory.PMonE.normal_of_inv_mul | exact GlobalTheory.PMonE.normal_of_inv_mul | (intros; apply GlobalTheory.PMonE.normal_of_inv_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuter
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section WinInner

variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

def frobPerm : Equiv.Perm F := (frobeniusEquiv F p).toEquiv

theorem frobPerm_pow_apply (n : ℕ) (x : F) : (frobPerm (F := F) p ^ n) x = x ^ p ^ n := by
  rw [Equiv.Perm.coe_pow]
  have : (⇑(frobPerm (F := F) p)) = frobenius F p := by
    funext y; simp [frobPerm]
  rw [this, iterate_frobenius]

theorem pw_eq_zpow (k : ℤ) (x : F) : pw p k x = (frobPerm (F := F) p ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frobPerm_pow_apply]
    simp
  · push_neg at hk
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]
    simp only [neg_neg, Int.toNat_natCast]
    rfl

theorem pw_pow (k : ℤ) (h : ℕ) (y : F) : pw p k (y ^ p ^ h) = pw p (k + h) y := by
  rw [pw_eq_zpow, pw_eq_zpow, ← frobPerm_pow_apply, ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]

theorem term_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (r j : Fin h) (n : ℤ) :
    term p ϖ lam (fun i => x' i ^ p ^ h) r j n = ϖ * term p ϖ lam x' r j (n + 1) := by
  unfold term
  rw [pw_pow]
  have h1 : ((r : ℤ) + n * h + h) = (r : ℤ) + (n + 1) * h := by ring
  have h2 : ϖ ^ (-n) = ϖ * ϖ ^ (-(n + 1)) := by
    rw [show -n = -(n + 1) + 1 by ring, zpow_add_one₀ hϖ]; ring
  rw [h1, h2]; ring

theorem rowT_pow {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam x' : Fin h → F) (K : ℕ) (hK : 1 ≤ K) (r : Fin h) :
    rowT p ϖ lam K (fun i => x' i ^ p ^ h) r = ϖ * rowS p ϖ lam (K - 1) (K + 1) x' r := by
  unfold rowT rowS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [term_pow p ϖ hϖ]
  rw [← Finset.mul_sum]
  congr 1
  have hI : Finset.Icc (-((K - 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ)
      = (Finset.Icc (-(K : ℤ)) (K : ℤ)).map (addRightEmbedding 1) := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> push_cast [hK] <;> ring
  rw [hI, Finset.sum_map]
  rfl

end WinInner

theorem win_inner : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F),
    ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F,
      Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} =
        Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  intro F _ p _ _ _ h K ϖ hϖ hK lam π
  let e : (Fin h → F) ≃ (Fin h → F) := Equiv.piCongrRight fun _ => frobPerm (F := F) p ^ h
  have he : ∀ x' : Fin h → F, e x' = fun i => x' i ^ p ^ h := by
    intro x'; funext i; simp [e, frobPerm_pow_apply]
  symm
  refine Nat.card_congr (e.subtypeEquiv fun x' => ?_)
  rw [he]
  have hq : p ^ h ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (h1 j) _
    · rw [rowT_pow p ϖ hϖ lam x' K hK, h2 r, mul_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun r => ?_⟩
    · have := h1 j
      rw [norm_pow] at this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hq).1 this
    · have := h2 r
      rw [rowT_pow p ϖ hϖ lam x' K hK] at this
      exact (mul_eq_zero.1 this).resolve_left hϖ

end GlobalTheory.PMonE

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuterStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F), ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F, Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} = Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  first | exact @GlobalTheory.PMonE.win_inner | exact GlobalTheory.PMonE.win_inner | (intros; apply GlobalTheory.PMonE.win_inner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystem
open GlobalTheory.PMonE

namespace GlobalTheory.PMonE

theorem winPt_card (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F)
    (lam π : Fin h → F) (hπ : ∀ j, π j ≠ 0) (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F)
    (hM : ∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) :
    Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} =
      Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  set φ := iterateFrobeniusEquiv F p (h * (L - 1)) with hφ
  have hpow : ∀ y : F, φ y = y ^ (p ^ h) ^ (L - 1) := fun y => by
    rw [hφ, iterateFrobeniusEquiv_def, pow_mul]
  have hN : (p ^ h) ^ (L - 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hwin : ∀ z : Fin h → F, ∀ j, winPt p π L z j = π j * φ (z j) := fun z j => by
    simp only [winPt, hpow]
  symm
  refine Nat.card_congr
    { toFun := fun z => ⟨winPt p π L z.1, fun j => ?_, (hM z.1).1 z.2.2⟩
      invFun := fun x => ⟨fun j => φ.symm (x.1 j / π j), fun j => ?_, ?_⟩
      left_inv := fun z => ?_
      right_inv := fun x => ?_ }
  · rw [hwin, norm_mul, hpow, norm_pow]
    have h0 : 0 ≤ ‖z.1 j‖ := norm_nonneg _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ h0 (z.2.1 j))
  · have hx : ‖φ (φ.symm (x.1 j / π j))‖ ≤ 1 := by
      rw [RingEquiv.apply_symm_apply, norm_div, div_le_one (norm_pos_iff.2 (hπ j))]
      exact x.2.1 j
    rw [hpow, norm_pow] at hx
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN).1 hx
  · rw [hM]
    have : winPt p π L (fun j => φ.symm (x.1 j / π j)) = x.1 := by
      funext j
      rw [hwin, RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]
    rw [this]; exact x.2.2
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [mul_div_cancel_left₀ _ (hπ j), RingEquiv.symm_apply_apply]
  · apply Subtype.ext
    funext j
    simp only [hwin]
    rw [RingEquiv.apply_symm_apply, mul_div_cancel₀ _ (hπ j)]

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystemStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F), (∀ j, π j ≠ 0) → ∀ (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F), (∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) → Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} = Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  first | exact @GlobalTheory.PMonE.winPt_card | exact GlobalTheory.PMonE.winPt_card | (intros; apply GlobalTheory.PMonE.winPt_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAdditive
namespace GlobalTheory.PMonE

theorem window_additive (q : ℝ) (hq : 2 ≤ q) (r : ℤ) (α f : ℤ → ℝ) (hα : Antitone α)
    (hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * (q ^ (r - J) - 1)) :
    (∀ J, J ≤ r → f J + α J ≤ f r + α r) ∧
    (∀ J, r + 1 ≤ J → f J - α J / 2 ≤ f r - α (r + 1) / 2) := by
  have hd : ∀ J, 0 ≤ α J - α (J + 1) := fun J => sub_nonneg.2 (hα (by omega))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  constructor
  · intro J hJ
    induction J, hJ using Int.leInductionDown with
    | base => exact le_rfl
    | pred n hn ih =>
      have h1 := hf (n - 1)
      have h2 := hd (n - 1)
      rw [sub_add_cancel] at h1 h2
      have h3 : q ^ (1 : ℤ) ≤ q ^ (r - (n - 1)) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_one] at h3
      nlinarith [mul_nonneg h2 (show 0 ≤ q ^ (r - (n - 1)) - 2 by linarith)]
  · intro J hJ
    induction J, hJ using Int.leInduction with
    | base =>
      have h1 := hf r
      rw [sub_self, zpow_zero, sub_self, mul_zero] at h1
      linarith
    | succ n hn ih =>
      have h1 := hf n
      have h2 := hd n
      have h3 : q ^ (r - n) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_neg_one] at h3
      have h4 : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
      nlinarith [mul_nonneg h2 (show 0 ≤ 2⁻¹ - q ^ (r - n) by linarith)]

theorem window_ineq : ∀ (p h : ℕ), 1 < p → 0 < h → ∀ a ρ : ℤ → ℝ, (∀ J, 0 < a J) → (∀ J, 0 < ρ J) → Antitone a → a 0 < p * a ((h : ℤ) - 1) → (∀ J, a (J + h) = a J / p) → (∀ J, ρ (J + h) = ρ J ^ ((p : ℝ) ^ h)⁻¹) → (∀ J, a (J + 1) * ρ (J + 1) ^ ((p : ℝ) ^ J) = a J * ρ J ^ ((p : ℝ) ^ J)) → ∀ r : ℕ, r < h → ∀ J : ℤ, a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) ∧ (J < 0 → a J * ρ J ^ ((p : ℝ) ^ r) < a r * ρ r ^ ((p : ℝ) ^ r)) ∧ (J ≤ -(h : ℤ) → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) ∧ (3 * (h : ℤ) ≤ J → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) := by
  intro p h hp hh a ρ ha hρ hanti hlt hper _ hrel r hr J
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set α : ℤ → ℝ := fun J => Real.log (a J) with hαdef
  set f : ℤ → ℝ := fun J => Real.log (a J * ρ J ^ ((p : ℝ) ^ r)) with hfdef
  have hα : Antitone α := fun i j hij => Real.log_le_log (ha j) (hanti hij)
  have hpos : ∀ J, 0 < a J * ρ J ^ ((p : ℝ) ^ r) := fun J =>
    mul_pos (ha J) (Real.rpow_pos_of_pos (hρ J) _)
  have hlog : ∀ (J : ℤ) (e : ℝ), Real.log (a J * ρ J ^ e) = α J + e * Real.log (ρ J) := by
    intro J e
    rw [Real.log_mul (ha J).ne' (Real.rpow_pos_of_pos (hρ J) _).ne', Real.log_rpow (hρ J)]
  have hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * ((p : ℝ) ^ ((r : ℤ) - J) - 1) := by
    intro J
    have h1 := congrArg Real.log (hrel J)
    rw [hlog, hlog] at h1
    have h2 : (p : ℝ) ^ r = (p : ℝ) ^ ((r : ℤ) - J) * (p : ℝ) ^ J := by
      rw [← zpow_add₀ hp0.ne', sub_add_cancel, zpow_natCast]
    simp only [hfdef, hlog]
    rw [h2]
    linear_combination (p : ℝ) ^ ((r : ℤ) - J) * h1
  obtain ⟨hL, hR⟩ := window_additive p hp2 r α f hα hf
  have hαper : ∀ J, α (J + h) = α J - Real.log p := by
    intro J
    simp only [hαdef]
    rw [hper, Real.log_div (ha J).ne' hp0.ne']
  have hdiv : f J ≤ f r - Real.log p →
      a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p := by
    intro H
    rw [← Real.log_le_log_iff (hpos J) (div_pos (hpos r) hp0),
      Real.log_div (hpos r).ne' hp0.ne']
    exact H
  have hr0 : α r ≤ α 0 := hα (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (hpos J) (hpos r)]
    change f J ≤ f r
    rcases le_or_gt J r with hJ | hJ
    · have := hL J hJ
      have := hα hJ
      linarith
    · have := hR J hJ
      have := hα (show (r : ℤ) + 1 ≤ J from hJ)
      linarith
  · intro hJ
    rw [← Real.log_lt_log_iff (hpos J) (hpos r)]
    change f J < f r
    have h1 := hL J (by omega)
    have h2 : α (-1) ≤ α J := hα (by omega)
    have h3 : α 0 < α (-1) := by
      apply Real.log_lt_log (ha 0)
      have h4 := hlt
      have h5 := hper (-1)
      rw [show (-1 : ℤ) + h = (h : ℤ) - 1 by ring] at h5
      rw [h5, mul_div_cancel₀ _ hp0.ne'] at h4
      exact h4
    linarith
  · intro hJ
    apply hdiv
    have h1 := hL J (by omega)
    have h2 : α (-h) ≤ α J := hα hJ
    have h3 := hαper (-h)
    rw [neg_add_cancel] at h3
    linarith
  · intro hJ
    apply hdiv
    have h1 := hR J (by omega)
    have h2 : α J ≤ α (h + h + h) := hα (by omega)
    have h3 := hαper (h + h)
    have h4 := hαper h
    have h5 : α h ≤ α (r + 1) := hα (by omega)
    linarith

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBound
noncomputable section

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem pow_iter_frobeniusEquiv_symm {F : Type} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (x : F) (m : ℕ) : (((frobeniusEquiv F p).symm)^[m] x) ^ p ^ m = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul]
    have h := frobenius_apply_frobeniusEquiv_symm F p (((frobeniusEquiv F p).symm)^[m] x)
    rw [frobenius_def] at h
    rw [h, ih]

variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem norm_pw (k : ℤ) (x : F) : ‖pw p k x‖ = ‖x‖ ^ ((p : ℝ) ^ k) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold pw
  split_ifs with hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [norm_pow, Int.toNat_natCast, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hm
    rw [neg_neg, Int.toNat_natCast]
    have hy := pow_iter_frobeniusEquiv_symm p x m
    conv_rhs => rw [← hy]
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_pow, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (by positivity), Real.rpow_one]

theorem norm_term (k : ℕ) (ϖ : F) (hϖ : ‖ϖ‖ = (p : ℝ)⁻¹) (lam π : Fin (k + 1) → F) (r j : Fin (k + 1)) (n : ℤ) :
    ‖term p ϖ lam π r j n‖ = ‖lam j‖ * (p : ℝ) ^ n * ‖π j‖ ^ ((p : ℝ) ^ (((r : ℕ) : ℤ) + n * ((k : ℤ) + 1))) := by
  unfold term
  rw [norm_mul, norm_mul, norm_zpow, hϖ, norm_pw, inv_zpow', neg_neg]
  push_cast
  rfl

def idx (k : ℕ) (J : ℤ) : Fin (k + 1) :=
  ⟨(J % ((k : ℤ) + 1)).toNat, by
    have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos J (show (0 : ℤ) < (k : ℤ) + 1 by omega)
    omega⟩

theorem idx_spec (k : ℕ) (j : Fin (k + 1)) (m : ℤ) :
    idx k (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = j ∧ (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) / ((k : ℤ) + 1) = m := by
  have hj := j.isLt
  have h0 : ((j : ℕ) : ℤ) / ((k : ℤ) + 1) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have h1 : ((j : ℕ) : ℤ) % ((k : ℤ) + 1) = j := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · ext
    simp [idx, Int.add_mul_emod_self_left, h1]
  · rw [Int.add_mul_ediv_left _ _ (by omega), h0, zero_add]

theorem decomp (k : ℕ) (J : ℤ) : ∃ j : Fin (k + 1), ∃ m : ℤ, J = ((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
  refine ⟨idx k J, J / ((k : ℤ) + 1), ?_⟩
  have h1 := Int.emod_nonneg J (show ((k : ℤ) + 1) ≠ 0 by omega)
  have h2 : J % ((k : ℤ) + 1) = J - ((k : ℤ) + 1) * (J / ((k : ℤ) + 1)) := Int.emod_def _ _
  show J = (((J % ((k : ℤ) + 1)).toNat : ℕ) : ℤ) + _
  rw [Int.toNat_of_nonneg h1]
  linarith

def aW (k : ℕ) (lam : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖lam (idx k J)‖ * (p : ℝ) ^ (-(J / ((k : ℤ) + 1)))

def rW (k : ℕ) (π : Fin (k + 1) → F) (J : ℤ) : ℝ :=
  ‖π (idx k J)‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * (J / ((k : ℤ) + 1)))))

theorem aW_at (k : ℕ) (lam : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    aW p k lam (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖lam j‖ * (p : ℝ) ^ (-m) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [aW, h1, h2]

theorem rW_at (k : ℕ) (π : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    rW p k π (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * m))) := by
  obtain ⟨h1, h2⟩ := idx_spec k j m
  simp only [rW, h1, h2]

end GlobalTheory.PMonE.WinBounds

namespace GlobalTheory.PMonE.WinBounds

open GlobalTheory.PMonE

theorem term_le_bound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  intro F _ p _ _ _ k ϖ hϖ lam π hlam hanti hratio hπ hrel1 hrel2 r j n
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have ha : ∀ J, 0 < aW p k lam J := by
    intro J; unfold aW; exact mul_pos (norm_pos_iff.2 (hlam _)) (zpow_pos hp0 _)
  have hρ : ∀ J, 0 < rW p k π J := by
    intro J; unfold rW; exact Real.rpow_pos_of_pos (norm_pos_iff.2 (hπ _).1) _
  have hrp : ∀ (x : ℝ), 0 ≤ x → ∀ c d : ℤ, (x ^ ((p : ℝ) ^ c)) ^ ((p : ℝ) ^ d) = x ^ ((p : ℝ) ^ (c + d)) := by
    intro x hx c d; rw [← Real.rpow_mul hx, zpow_add₀ hpne]
  have hnat : ∀ (x : ℝ) (e : ℕ), x ^ ((p : ℝ) ^ (e : ℤ)) = x ^ (p ^ e) := by
    intro x e; rw [zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
  have hstep : ∀ J, aW p k lam (J + 1) ≤ aW p k lam J := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
      have h1 := hratio 0 (Fin.last k)
      have hz := zpow_pos hp0 (-m)
      calc ‖lam 0‖ * ((p : ℝ) ^ (-m) * (p : ℝ)⁻¹) = (‖lam 0‖ / p) * (p : ℝ) ^ (-m) := by ring
        _ ≤ ‖lam (Fin.last k)‖ * (p : ℝ) ^ (-m) := by
          gcongr
          rw [div_le_iff₀ hp0]; linarith
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at]
      have h1 : ‖lam i.succ‖ ≤ ‖lam (Fin.castSucc i)‖ := hanti (Fin.castSucc_lt_succ (i := i)).le
      have hz := zpow_pos hp0 (-m)
      gcongr
  have hA : Antitone (aW p k lam) := antitone_int_of_succ_le hstep
  have hA0 : aW p k lam 0 < (p : ℝ) * aW p k lam (((k + 1 : ℕ) : ℤ) - 1) := by
    have h1 : aW p k lam 0 = ‖lam 0‖ := by simpa using aW_at p k lam 0 0
    have h2 : aW p k lam (k : ℤ) = ‖lam (Fin.last k)‖ := by simpa using aW_at p k lam (Fin.last k) 0
    rw [h1, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, h2]
    exact hratio 0 (Fin.last k)
  have hperA : ∀ J, aW p k lam (J + ((k + 1 : ℕ) : ℤ)) = aW p k lam J / p := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, aW_at, aW_at, neg_add, zpow_add₀ hpne, zpow_neg_one]
    ring
  have hperR : ∀ J, rW p k π (J + ((k + 1 : ℕ) : ℤ)) = rW p k π J ^ (((p : ℝ) ^ (k + 1))⁻¹) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    rw [show ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * m + ((k + 1 : ℕ) : ℤ) = ((i : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) by
      push_cast; ring, rW_at, rW_at]
    have e3 : ((p : ℝ) ^ (k + 1))⁻¹ = (p : ℝ) ^ (-((k : ℤ) + 1)) := by
      rw [zpow_neg]; norm_cast
    rw [e3, hrp _ (norm_nonneg _), show -(((k : ℤ) + 1) * (m + 1)) = -(((k : ℤ) + 1) * m) + -((k : ℤ) + 1) by ring]
  have hrelW : ∀ J, aW p k lam (J + 1) * rW p k π (J + 1) ^ ((p : ℝ) ^ J)
      = aW p k lam J * rW p k π J ^ ((p : ℝ) ^ J) := by
    intro J
    obtain ⟨i, m, rfl⟩ := decomp k J
    induction i using Fin.lastCases with
    | last =>
      have e1 : (((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1
          = (((0 : Fin (k + 1)) : ℕ) : ℤ) + ((k : ℤ) + 1) * (m + 1) := by
        push_cast [Fin.val_last, Fin.val_zero]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * (m + 1)) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = -1 := by
        push_cast [Fin.val_last]; ring
      have e3 : -(((k : ℤ) + 1) * m) + ((((Fin.last k : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((k : ℕ) : ℤ) := by
        push_cast [Fin.val_last]; ring
      rw [e2, e3, hnat, zpow_neg_one]
      have hXY : ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) = ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by
        have hx : 0 ≤ ‖lam 0‖ / p * ‖π 0‖ ^ ((p : ℝ)⁻¹) := by positivity
        have hy : 0 ≤ ‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k := by positivity
        refine (pow_left_inj₀ hx hy (Fact.out : p.Prime).ne_zero).1 ?_
        rw [mul_pow, ← hrel2, ← Real.rpow_natCast (‖π 0‖ ^ ((p : ℝ)⁻¹)) p, ← Real.rpow_mul (norm_nonneg _),
          inv_mul_cancel₀ hpne, Real.rpow_one]
      rw [neg_add, zpow_add₀ hpne, zpow_neg_one]
      linear_combination (p : ℝ) ^ (-m) * hXY
    | cast i =>
      have e1 : (((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m + 1 = ((i.succ : ℕ) : ℤ) + ((k : ℤ) + 1) * m := by
        push_cast [Fin.coe_castSucc, Fin.val_succ]; ring
      rw [e1, aW_at, aW_at, rW_at, rW_at, hrp _ (norm_nonneg _), hrp _ (norm_nonneg _)]
      have e2 : -(((k : ℤ) + 1) * m) + ((((Fin.castSucc i : ℕ)) : ℤ) + ((k : ℤ) + 1) * m) = ((i : ℕ) : ℤ) := by
        push_cast [Fin.coe_castSucc]; ring
      rw [e2, hnat, hnat]
      have h := hrel1 i
      linear_combination (p : ℝ) ^ (-m) * h
  have hJ := window_ineq p (k + 1) (by exact_mod_cast (Fact.out : p.Prime).one_lt) (Nat.succ_pos k) (aW p k lam)
    (rW p k π) ha hρ hA hA0 hperA hperR hrelW (r : ℕ) r.isLt (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * (-n))
  rw [aW_at p k lam j (-n), rW_at p k π j (-n)] at hJ
  have hR1 : aW p k lam ((r : ℕ) : ℤ) = ‖lam r‖ := by simpa using aW_at p k lam r 0
  have hR2 : rW p k π ((r : ℕ) : ℤ) = ‖π r‖ := by simpa using rW_at p k π r 0
  rw [hR1, hR2] at hJ
  have hT : ‖term p ϖ lam π r j n‖
      = ‖lam j‖ * (p : ℝ) ^ (-(-n)) * (‖π j‖ ^ ((p : ℝ) ^ (-(((k : ℤ) + 1) * -n)))) ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_term p k ϖ hϖ, ← zpow_natCast (p : ℝ) (r : ℕ), hrp _ (norm_nonneg _), neg_neg,
      show -(((k : ℤ) + 1) * -n) + ((r : ℕ) : ℤ) = ((r : ℕ) : ℤ) + n * ((k : ℤ) + 1) by ring]
  have hRt : ‖lam r * π r ^ p ^ (r : ℕ)‖ = ‖lam r‖ * ‖π r‖ ^ ((p : ℝ) ^ (r : ℕ)) := by
    rw [norm_mul, norm_pow, ← Real.rpow_natCast ‖π r‖ (p ^ (r : ℕ)), Nat.cast_pow]
  rw [hT, hRt]
  obtain ⟨W1, W2, W3, W4⟩ := hJ
  have hj1 : ((j : ℕ) : ℤ) < (k : ℤ) + 1 := by exact_mod_cast j.isLt
  have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
  refine ⟨W1, fun hn => W2 (by nlinarith), fun hn => ?_⟩
  rcases lt_abs.1 hn with hn | hn
  · exact W3 (by push_cast; nlinarith)
  · exact W4 (by push_cast; nlinarith)

end GlobalTheory.PMonE.WinBounds
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBoundStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  first | exact @GlobalTheory.PMonE.WinBounds.term_le_bound | exact GlobalTheory.PMonE.WinBounds.term_le_bound | (intros; apply GlobalTheory.PMonE.WinBounds.term_le_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWindowRadii
namespace GlobalTheory.PMonE


open Finset in
theorem _root_.GlobalTheory.PMonE.exists_window_radii : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by
  intro F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hl : ∀ j, 0 < ‖lam j‖ := fun j => norm_pos_iff.mpr (hlam j)
  have hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)
  choose ρ hρ using hρ
  have hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖ := fun j => by
    rw [← norm_pow, hρ, norm_div]
  have hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖ := fun j => by
    rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn,
      one_le_div (hl _)]
    exact hanti (Fin.castSucc_le_succ j)
  set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'
  have hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖ := fun n => by
    simp only [hρ']; split_ifs with h
    · exact hρ1 _
    · simp
  have hρ'ne : ∀ n, ρ' n ≠ 0 := fun n h0 => by
    have := hρ'1 n; rw [h0, norm_zero] at this; linarith
  set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP
  have hPne : ∀ j, P j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n
  have hPsucc : ∀ j, P (j + 1) = P j * ρ' j := fun j => prod_range_succ _ _
  have hPmono : Monotone fun j => ‖P j‖ := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [hPsucc, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)
  have hP0 : P 0 = 1 := by simp [hP]
  have hc1 : 1 ≤ ‖P k‖ := by
    have := hPmono (Nat.zero_le k); simpa [hP0] using this
  set c := ‖P k‖ with hc
  have hcpos : 0 < c := by linarith
  set N := p ^ (k + 1) - 1 with hN
  have hpk : 2 ≤ p ^ (k + 1) := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hNpos : 0 < N := by omega
  have hN1 : p ^ (k + 1) = N + 1 := by omega
  set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw
  have hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1)) := by
    rw [hw]
    simp only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]
    ring
  have hwne : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by
      intro h0; rw [h0, norm_zero] at hϖ; exact (inv_pos.mpr hpR).ne' hϖ.symm)))
      (mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))
  obtain ⟨π0, hπ0⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hπ0ne : π0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hNpos.ne'] at hπ0; exact hwne hπ0.symm
  set s := ‖π0‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hπ0ne
  have hsN : s ^ N = ‖w‖ := by rw [hs, ← norm_pow, hπ0]
  have hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖ := by
    rw [div_lt_iff₀ hpR, mul_comm]; exact hclose 0 (Fin.last k)
  have hsc : s * c < 1 := by
    have key : (s * c) ^ N < 1 := by
      have hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c) := by
        rw [hwn, pow_succ]
        field_simp
      rw [mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]
      calc (‖lam 0‖ / p) ^ p < ‖lam (Fin.last k)‖ ^ p :=
            pow_lt_pow_left₀ hl0 (by positivity) (by omega)
        _ ≤ ‖lam (Fin.last k)‖ ^ p * c :=
            le_mul_of_one_le_right (by have := hl (Fin.last k); positivity) hc1
    exact (pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key
  refine ⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩
  · rw [norm_mul, ← hs]
    calc s * ‖P j‖ ≤ s * c := mul_le_mul_of_nonneg_left (hPmono (Nat.lt_succ_iff.mp j.isLt)) hspos.le
      _ < 1 := hsc
  · simp only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]
    have : ρ' j = ρ j := by simp [hρ', j.isLt]
    rw [this, hρn]
    have := hl j.succ
    field_simp
  · simp only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]
    rw [← pow_succ, hN1, pow_succ s N, hsN, hwn]
    have := hl (Fin.last k)
    field_simp

end GlobalTheory.PMonE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero
noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

theorem coefB_norm {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] {h : ℕ}
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    (∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1) ∧ (∀ m, L < m → ∀ r j, ‖coefB p ϖ lam π L U m r j‖ < 1) := by
  have key : ∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1 ∧ (L < m → ‖coefB p ϖ lam π L U m r j‖ < 1) := by
    intro m r j
    simp only [coefB, Matrix.of_apply]
    split_ifs with hm
    · rw [norm_pow, norm_div]
      obtain ⟨h1, h2⟩ := hb r j ((m : ℤ) - L)
      have hpos : p ^ (h - (r : ℕ)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
      rcases eq_or_lt_of_le (norm_nonneg (lam r * π r ^ p ^ (r : ℕ))) with hc | hc
      · rw [← hc, div_zero, zero_pow hpos]
        exact ⟨zero_le_one, fun _ => zero_lt_one⟩
      · refine ⟨pow_le_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_le_one hc).2 h1), fun hLm => ?_⟩
        exact pow_lt_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_lt_one hc).2 (h2 (by omega))) hpos
    · simp
  exact ⟨fun m r j => (key m r j).1, fun m hm r j => (key m r j).2 hm⟩

theorem gsum_mul_left {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (A : Matrix m m F)
    (B : ℕ → Matrix m m F) (z : m → F) :
    gsum q D (fun n => A * B n) z = A *ᵥ gsum q D B z := by
  simp only [gsum, Matrix.mulVec_sum, Matrix.mulVec_mulVec]

theorem normalize {F : Type} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hlam : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hanti : Antitone (fun j => ‖lam j‖)) (horth : Orth p lam) (L U : ℕ) (hL : 1 ≤ L)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    ∃ M : ℕ → Matrix (Fin h) (Fin h) F, Normal L M ∧ (M 0).det ≠ 0 ∧
      ∃ Φ : (Fin h → F) → (Fin h → F), (∀ b, (∀ r, ‖b r‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖) → Integral (Φ b)) ∧
        Φ 0 = 0 ∧ ∀ z b, gsum (p ^ h) (L + U) M z = Φ b ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = b r := by
  set B := coefB p ϖ lam π L U with hBdef
  obtain ⟨hB1, hB2⟩ := coefB_norm p ϖ lam π L U hb
  obtain ⟨hdet, hdet0⟩ := GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm F p h ϖ hϖ lam π hlam hπ hanti horth L U
  obtain ⟨hN, hinv⟩ := GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one F (Fin h) L B hB1 hB2 hdet
  have hdne : (B L).det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  have hdu : IsUnit (B L).det := isUnit_iff_ne_zero.2 hdne
  have hc : ∀ r, lam r * π r ^ p ^ (r : ℕ) ≠ 0 := fun r => mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r))
  let nb : (Fin h → F) → (Fin h → F) := fun b r => (b r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))
  refine ⟨fun n => (B L)⁻¹ * B n, hN, ?_, fun b => (B L)⁻¹ *ᵥ nb b, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det (B L) hdu).ne_zero hdet0
  · intro b hbb i
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_mul]
    have h1 : ‖nb b j‖ ≤ 1 := by
      simp only [nb]
      rw [norm_pow, norm_div]
      exact pow_le_one₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
        ((div_le_one (norm_pos_iff.2 (hc j))).2 (hbb j))
    exact mul_le_one₀ (hinv i j) (norm_nonneg _) h1
  · have : nb 0 = 0 := by
      funext r
      simp only [nb, Pi.zero_apply, zero_div]
      exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    simp only [this, Matrix.mulVec_zero]
  · intro z b
    rw [gsum_mul_left]
    constructor
    · intro H r
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        have := congrArg (fun v => B L *ᵥ v) H
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdu, Matrix.one_mulVec] using this
      have H3 := congrFun H2 r
      rw [← GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum F p h ϖ lam π L U hL z r] at H3
      have H4 := (iterateFrobenius_inj F p (h - (r : ℕ))).eq_iff.1 (by simpa [iterateFrobenius_def] using H3)
      exact (div_left_inj' (hc r)).1 H4
    · intro H
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        funext r
        rw [← GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum F p h ϖ lam π L U hL z r, H r]
      rw [H2]

theorem winThm : WinThm := by
  intro F _ _ _ _ p _ _ _ h ϖ hh hϖ lam hlam hanti horth hlt
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  obtain ⟨π, hπ, hrel1, hrel2⟩ := exists_window_radii F p k ϖ hϖ lam hlam hanti hlt
  have hp := (Fact.out : p.Prime)
  have hϖ0 : ϖ ≠ 0 := by
    have : (0 : ℝ) < ‖ϖ‖ := by
      rw [hϖ]
      exact inv_pos.2 (by exact_mod_cast hp.pos)
    exact norm_pos_iff.1 this
  have hbd := GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound F p k ϖ hϖ lam π hlam hanti hlt hπ hrel1 hrel2
  have hb : ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) :=
    fun r j n => ⟨(hbd r j n).1, (hbd r j n).2.1⟩
  have hπ0 : ∀ j, π j ≠ 0 := fun j => (hπ j).1
  have hGL := GlobalTheory.T.additiveSystem_generalLemma_all_orders
  refine ⟨fun j => ‖π j‖, fun r => ‖lam r * π r ^ p ^ (r : ℕ)‖, 2,
    fun j => ⟨norm_pos_iff.2 (hπ j).1, (hπ j).2⟩,
    fun r => norm_pos_iff.2 (mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r).1)), ?_, ?_, ?_⟩
  · intro x hx r j n
    have hm := GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono F p (k + 1) ϖ lam π x hx r j n
    exact ⟨hm.trans (hbd r j n).1, fun hn => hm.trans ((hbd r j n).2.2 (by exact_mod_cast hn))⟩
  · intro b hbnd
    obtain ⟨M, hM, _, Φ, hΦ, _, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨z, hz, hzb⟩ := (hGL 2).1 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM (Φ b)
      (hΦ b hbnd)
    refine ⟨winPt p π 2 z, ?_, fun r => ?_⟩
    · intro j
      simp only [winPt]
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz j))
    · rw [rowT_eq_rowS]
      exact (hiff z b).1 hzb r
  · obtain ⟨M, hM, hM0, Φ, _, hΦ0, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨M', hM', hM0', Φ', _, hΦ0', hiff'⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth (2 - 1) (2 + 1) (by norm_num) hb
    have c1 := (hGL 2).2 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM hM0
    have c2 := (hGL (2 - 1)).2 F p (Fin (k + 1)) (k + 1) ((2 - 1) + (2 + 1)) (by omega) (by omega) M' hM' hM0'
    have d1 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 2 2 M (fun z => by simpa [hΦ0] using hiff z 0)
    have d2 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 (2 - 1) (2 + 1) M' (fun z => by simpa [hΦ0'] using hiff' z 0)
    have e1 := GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer F p (k + 1) 2 ϖ hϖ0 (by norm_num) lam π
    have hq1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (by omega) hp.one_lt
    have cS : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =
        (p ^ (k + 1)) ^ ((k + 1) * 2) := by
      rw [d1, c1, Fintype.card_fin]
    have cI : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} = (p ^ (k + 1)) ^ ((k + 1) * (2 - 1)) := by
      rw [e1, d2, c2, Fintype.card_fin]
    by_contra hcon
    have hsub : ∀ x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0},
        ∀ j, ‖x.1 j‖ ≤ ‖π j‖ ^ p ^ (k + 1) := by
      intro x
      by_contra hx
      push_neg at hx
      exact hcon ⟨x.1, x.2.1, hx, x.2.2⟩
    haveI : Finite {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} := Nat.finite_of_card_ne_zero (by rw [cI]; positivity)
    have hle := Nat.card_le_card_of_injective
      (fun x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =>
        (⟨x.1, hsub x, x.2.2⟩ : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
          ∀ r, rowT p ϖ lam 2 x r = 0}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [cS, cI] at hle
    exact absurd hle (not_le.2 (Nat.pow_lt_pow_right hq1 (by omega)))

end GlobalTheory.PMonE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZeroStatement
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
end
