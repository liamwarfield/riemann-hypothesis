module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
open Formalism.REAL Finset

namespace GlobalTheory

theorem capelli_left_comatrix :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
      ∀ (u : ℂ) (j l : Fin (m + 1)),
        ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
            (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
          if l = j then qdet E u else 0 := by
  intro A _ _ m E hE u j l
  set b : Fin (m + 1) → Fin (m + 1) := Fin.cons l (Fin.succAbove j) with hb
  have hexp := PI.QmColExpWork.expFirst E id b u
  have hbc : b ∘ Fin.succ = Fin.succAbove j := by
    funext k; simp [hb]
  have hb0 : b 0 = l := by simp [hb]
  rw [hbc, hb0] at hexp
  have hcast : ∀ (k : ℕ) (x : A), (((-1 : ℤ) ^ k : ℤ) : A) * x = ((-1 : ℂ) ^ k) • x := by
    intro k x
    rw [Algebra.smul_def]
    push_cast
    simp
  have hL : ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
      ((-1 : ℂ) ^ (j : ℕ)) • qminor E id b u := by
    rw [hexp, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcast, smul_smul, ← pow_add, add_comm (j : ℕ) (a : ℕ)]
    rfl
  rw [hL]
  by_cases hlj : l = j
  · subst hlj
    have hbcyc : b = id ∘ PI.QmColExpWork.cyc0 m l := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [hb, PI.QmColExpWork.cycle_perm_zero]
      · simp [hb, PI.QmColExpWork.cycle_perm_succ]
    rw [if_pos rfl, hbcyc, qSkewCol A (m + 1) (m + 1) E hE id id _ u, PI.QmColExpWork.sign_cycle_perm,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hcast, smul_smul, ← mul_pow]
    simp [qdet]
  · rw [if_neg hlj]
    obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hlj
    have hfix : b ∘ Equiv.swap (0 : Fin (m + 1)) k0.succ = b := by
      funext k
      have h0 : b 0 = b k0.succ := by simp [hb, hk0]
      simp only [Function.comp, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, h0]
      · rw [h2, h0]
      · rfl
    have hs := qSkewCol A (m + 1) (m + 1) E hE id b (Equiv.swap 0 k0.succ) u
    rw [hfix, Equiv.Perm.sign_swap (Fin.succ_ne_zero k0).symm] at hs
    have h2 : (2 : ℂ) • qminor E id b u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hs]
      simp
    have hz : qminor E id b u = 0 := by
      have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
      simpa [smul_smul] using h3
    rw [hz, smul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrixStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_left_comatrix_qminor_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (j l : Fin (m + 1)), ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) = if l = j then qdet E u else 0 := by
  first | exact @GlobalTheory.capelli_left_comatrix | exact GlobalTheory.capelli_left_comatrix | (intros; apply GlobalTheory.capelli_left_comatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormFormalGroupHeightOneTorsionTower
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormFormalGroupHeightOneTorsionTower
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.TowerNorm

theorem norm_natCast_eq_one {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) (h : ‖(p : K)‖ < 1) {j : ℕ} (hj : ¬ p ∣ j) : ‖(j : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K j) ?_
  by_contra hlt
  push_neg at hlt
  have hc : IsCoprime (p : ℤ) (j : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hj)
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (u : K) * (p : K) + (v : K) * (j : K) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) huv
  have h2 := IsUltrametricDist.norm_add_le_max ((u : K) * (p : K)) ((v : K) * (j : K))
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have hu := IsUltrametricDist.norm_intCast_le_one K u
  have hv := IsUltrametricDist.norm_intCast_le_one K v
  have a1 : ‖(u : K)‖ * ‖(p : K)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hu (norm_nonneg _) h
  have a2 : ‖(v : K)‖ * ‖(j : K)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hv (norm_nonneg _) hlt
  exact absurd h2 (not_le.2 (max_lt a1 a2))

theorem prod_range_mul (g : ℕ → ℝ) (N b : ℕ) :
    ∏ j ∈ Finset.range (N * b), g j =
      ∏ a ∈ Finset.range N, ∏ c ∈ Finset.range b, g (a + N * c) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_range_succ, add_comm (N * b) a]

theorem prod_range_ite (f : ℕ → ℝ) (c : ℝ) {M : ℕ} (hM : 0 < M) :
    ∏ j ∈ Finset.range M, (if j = 0 then c else f j) = c * ∏ j ∈ Finset.Ico 1 M, f j := by
  rw [Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hM]
  simp only [if_true, zero_add]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have := (Finset.mem_Ico.1 hj).1
  rw [if_neg (by omega)]

section

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem prod_fibre (f : PowerSeries K) (p : ℕ) (hp : 0 < p) (hf : Intg f)
    (h0 : PowerSeries.constantCoeff f = 0)
    (h1 : ‖PowerSeries.coeff p f‖ = 1) (hl : ∀ k < p, ‖PowerSeries.coeff k f‖ < 1)
    (c : K) (hc : ‖c‖ < 1) (x : ℕ → K) (T : Finset ℕ) (hT : T.card = p)
    (hinj : Set.InjOn x T) (hx : ∀ b ∈ T, ‖x b‖ < 1 ∧ ev1 f (x b) = c) :
    ∏ b ∈ T, ‖x b‖ = ‖c‖ := by
  classical
  obtain ⟨A1, A2, A3, A4, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hC : Intg (PowerSeries.C c : PowerSeries K) := (A4 c).2.1 hc.le
  have hI : Intg (f - PowerSeries.C c) := (A1 _ _ hf hC).2.1
  have hcard : (T.image x).card = p := by rw [Finset.card_image_of_injOn hinj, hT]
  have key := (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K (f - PowerSeries.C c) (T.image x) hI (by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨(hx b hb).1, ?_⟩
    obtain ⟨-, B2, B3, -⟩ := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K (x b) (hx b hb).1
    rw [(B2 _ _ ((A3 f 0).2.2 hf) ((A3 _ 0).2.2 hC)).2.1, B3, (hx b hb).2, sub_self])).2
  rw [hcard, Finset.prod_image hinj] at key
  have hz : PowerSeries.coeff 0 (f - PowerSeries.C c) = -c := by
    simp [h0]
  have hn : ∀ k, k ≠ 0 → PowerSeries.coeff k (f - PowerSeries.C c) = PowerSeries.coeff k f := by
    intro k hk
    simp [PowerSeries.coeff_C, hk]
  rw [key, hz, norm_neg]
  · rw [hn p hp.ne', h1]
  · intro k hk
    by_cases hk0 : k = 0
    · rw [hk0, hz, norm_neg]; exact hc
    · rw [hn k hk0]; exact hl k hk

theorem prod_zero_fibre (f : PowerSeries K) (p : ℕ) (hp : 0 < p) (hf : Intg f)
    (h0 : PowerSeries.constantCoeff f = 0)
    (h1 : ‖PowerSeries.coeff p f‖ = 1) (hl : ∀ k < p, ‖PowerSeries.coeff k f‖ < 1)
    (x : ℕ → K) (T : Finset ℕ) (hT : T.card = p - 1)
    (hinj : Set.InjOn x T) (hx : ∀ b ∈ T, ‖x b‖ < 1 ∧ ev1 f (x b) = 0 ∧ x b ≠ 0) :
    ∏ b ∈ T, ‖x b‖ = ‖PowerSeries.coeff 1 f‖ := by
  classical
  obtain ⟨A1, A2, A3, A4, A5, -, -, -, -, A10⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  set h : PowerSeries K := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f with hh
  have hco : ∀ k, PowerSeries.coeff k h = PowerSeries.coeff (k + 1) f := by
    intro k; simp [hh]
  have hI : Intg h := ((A10 h).1).2 fun n => by rw [hco]; exact ((A10 f).1).1 hf _
  have hX : Intg (PowerSeries.X : PowerSeries K) := (A5 ()).1
  have hfe : f = PowerSeries.X * h := by
    have := PowerSeries.eq_X_mul_shift_add_const f
    rw [h0, map_zero, add_zero] at this
    exact this
  have hcard : (T.image x).card = p - 1 := by rw [Finset.card_image_of_injOn hinj, hT]
  have key := (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K h (T.image x) hI (by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨(hx b hb).1, ?_⟩
    obtain ⟨-, B2, -, B4, -⟩ := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K (x b) (hx b hb).1
    have e := (B2 _ _ ((A3 _ 0).2.2 hX) ((A3 _ 0).2.2 hI)).2.2
    rw [← hfe, B4, (hx b hb).2.1] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hx b hb).2.2)).2
  rw [hcard, Finset.prod_image hinj] at key
  rw [key, hco]
  · rw [hco, Nat.sub_add_cancel hp, h1]
  · intro k hk
    rw [hco]; exact hl _ (by omega)

end

theorem tower_norm : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ‖t 1‖ ^ (p - 1) = ‖(p : K)‖ ∧ ‖(p : K)‖ < 1 ∧ (∀ n j, ¬ p ^ n ∣ j → ‖t 1‖ ≤ ‖ev1 (nMul F j) (t n)‖) ∧ ∀ n, ∏ j ∈ Finset.Ico 1 (p ^ n), ‖ev1 (nMul F j) (t n)‖ = ‖(p : K)‖ ^ n := by
  intro K _ _ _ _ _ p hpf F hF h1 hl t ht ht0 ht1 htt
  have hp : p.Prime := hpf.out
  obtain ⟨M1, -⟩ := GlobalTheory.T.formalGroupNatMulSeries_properties K F
  obtain ⟨P0, P⟩ := GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF
  obtain ⟨O1, O2, O3⟩ := GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht ht0 ht1 htt
  have hpn : ‖(p : K)‖ < 1 := by
    have := hl 1 hp.one_lt
    rwa [(M1 p).2] at this
  have hlt : ∀ n j, ‖ev1 (nMul F j) (t n)‖ < 1 := fun n j =>
    lt_of_le_of_lt ((P _ (ht n)).2.2.1 j).1 (ht n)
  have hunit : ∀ n j, ¬ p ∣ j → ‖ev1 (nMul F j) (t n)‖ = ‖t n‖ := fun n j hj =>
    ((P _ (ht n)).2.2.1 j).2 (norm_natCast_eq_one hp hpn hj)
  have hdown : ∀ n j, ev1 (nMul F p) (ev1 (nMul F j) (t (n + 1))) = ev1 (nMul F j) (t n) :=
    fun n j => by rw [(P _ (ht (n + 1))).2.2.2.2.1, O1]
  have hbot : ∀ n j, ev1 (nMul F (p ^ n * j)) (t (n + 1)) = ev1 (nMul F j) (t 1) :=
    fun n j => by rw [add_comm n 1, O2]
  have hnd : ∀ b ∈ Finset.Ico 1 p, ¬ p ∣ b := fun b hb =>
    Nat.not_dvd_of_pos_of_lt (Finset.mem_Ico.1 hb).1 (Finset.mem_Ico.1 hb).2
  have hB : ∏ b ∈ Finset.Ico 1 p, ‖ev1 (nMul F b) (t 1)‖ = ‖(p : K)‖ := by
    rw [← (M1 p).2]
    refine prod_zero_fibre (nMul F p) p hp.pos (P0 p) (M1 p).1 h1 hl
      (fun b => ev1 (nMul F b) (t 1)) _ (by simp) ?_ ?_
    · intro b hb b' hb' e
      have := (O3 1 b b').1 e
      rw [pow_one] at this
      exact Nat.ModEq.eq_of_lt_of_lt this (Finset.mem_Ico.1 hb).2 (Finset.mem_Ico.1 hb').2
    · intro b hb
      refine ⟨hlt _ _, ?_, ?_⟩
      · have := hdown 0 b
        rw [zero_add] at this
        rw [this, ht0]
        have e := ((P 0 (by simp)).2.2.1 b).1
        rw [norm_zero] at e
        exact norm_le_zero_iff.1 e
      · rw [← norm_ne_zero_iff, hunit 1 b (hnd b hb), norm_ne_zero_iff]
        exact ht1
  have hA : ∀ n a, ∏ b ∈ Finset.range p, ‖ev1 (nMul F (a + p ^ n * b)) (t (n + 1))‖ =
      ‖ev1 (nMul F a) (t n)‖ := by
    intro n a
    refine prod_fibre (nMul F p) p hp.pos (P0 p) (M1 p).1 h1 hl _ (hlt n a)
      (fun b => ev1 (nMul F (a + p ^ n * b)) (t (n + 1))) _ (by simp) ?_ ?_
    · intro b hb b' hb' e
      have := (O3 (n + 1) _ _).1 e
      have h2 := Nat.ModEq.add_left_cancel' a this
      rw [pow_succ] at h2
      have h3 := Nat.ModEq.mul_left_cancel' (pow_pos hp.pos n).ne' h2
      exact Nat.ModEq.eq_of_lt_of_lt h3 (Finset.mem_range.1 hb) (Finset.mem_range.1 hb')
    · intro b hb
      refine ⟨hlt _ _, ?_⟩
      rw [hdown, O3]
      simp [Nat.ModEq]
  refine ⟨?_, hpn, ?_, ?_⟩
  · rw [← hB, Finset.prod_congr rfl fun b hb => hunit 1 b (hnd b hb)]
    simp
  · intro n
    induction n with
    | zero => intro j hj; simp at hj
    | succ n ih =>
      intro j hj
      by_cases hd : p ^ n ∣ j
      · obtain ⟨j', rfl⟩ := hd
        rw [hbot, hunit 1 j']
        intro h
        exact hj (by rw [pow_succ]; exact Nat.mul_dvd_mul_left _ h)
      · refine (ih j hd).trans ?_
        rw [← hdown]
        exact ((P _ (hlt _ _)).2.2.1 p).1
  · intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hN : 0 < p ^ n := pow_pos hp.pos n
      have e1 := prod_range_ite (fun j => ‖ev1 (nMul F j) (t (n + 1))‖) 1 (pow_pos hp.pos (n + 1))
      rw [one_mul] at e1
      rw [← e1, pow_succ p n, prod_range_mul, pow_succ', ← ih, ← prod_range_ite _ _ hN]
      refine Finset.prod_congr rfl fun a _ => ?_
      by_cases ha : a = 0
      · subst ha
        rw [if_pos rfl, ← hB, ← one_mul (∏ b ∈ Finset.Ico 1 p, _), ← prod_range_ite _ _ hp.pos]
        refine Finset.prod_congr rfl fun b _ => ?_
        by_cases hb : b = 0
        · simp [hb]
        · rw [if_neg hb, zero_add, if_neg (Nat.mul_ne_zero hN.ne' hb), hbot]
      · rw [if_neg ha, ← hA n a]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [if_neg (by omega)]

end GlobalTheory.ConvSer.TowerNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormFormalGroupHeightOneTorsionTowerStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ‖t 1‖ ^ (p - 1) = ‖(p : K)‖ ∧ ‖(p : K)‖ < 1 ∧ (∀ n j, ¬ p ^ n ∣ j → ‖t 1‖ ≤ ‖ev1 (nMul F j) (t n)‖) ∧ ∀ n, ∏ j ∈ Finset.Ico 1 (p ^ n), ‖ev1 (nMul F j) (t n)‖ = ‖(p : K)‖ ^ n := by
  first | exact @GlobalTheory.ConvSer.TowerNorm.tower_norm | exact GlobalTheory.ConvSer.TowerNorm.tower_norm | (intros; apply GlobalTheory.ConvSer.TowerNorm.tower_norm <;> assumption)
end
end
