module

public import Mathlib

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def LB (m : ℤ) (f : ℤ → V) : Prop := ∀ k < m, f k = 0

def smulS (g : PowerSeries LL) (f : ℤ → V) : ℤ → V :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem smulS_eq_sum {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : smulS g f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (k - j) := by
  show ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j) = _
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hjN
  apply hj
  rw [hf (k - j) (by omega), smul_zero]

theorem LB_mono {m m' : ℤ} {f : ℤ → V} (hf : LB m f) (h : m' ≤ m) : LB m' f := by
  intro k hk
  exact hf k (lt_of_lt_of_le hk h)

theorem LB_smulS {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) : LB m (smulS g f) := by
  intro k hk
  rw [smulS_eq_sum hf g k 0 (by omega)]
  simp

theorem LB_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f + f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f - f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) : LB m (c • f) := by
  intro k hk
  simp [hf k hk]

private theorem exists_nat_gt_int_sub (k m : ℤ) : ∃ N : ℕ, k - m < N := by
  exact exists_nat_gt (k - m)

theorem smulS_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f + f') = smulS g f + smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.add_apply, smulS_eq_sum (LB_add hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, smul_add]

theorem smulS_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f - f') = smulS g f - smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.sub_apply, smulS_eq_sum (LB_sub hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, smul_sub]

theorem smulS_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (c : LL) :
    smulS g (c • f) = c • smulS g f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [Pi.smul_apply, smulS_eq_sum (LB_smul hf c) g k N hN,
    smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

private theorem smulS_C_eq_smul_of_LB {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf _ k (N + 1) (by omega), Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [PowerSeries.coeff_C, hj]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h0

theorem smulS_one {m : ℤ} {f : ℤ → V} (hf : LB m f) : smulS (1 : PowerSeries LL) f = f := by
  simpa using smulS_C_eq_smul_of_LB hf (1 : LL)

theorem smulS_C {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  exact smulS_C_eq_smul_of_LB hf c

theorem smulS_X_pow {m : ℤ} {f : ℤ → V} (hf : LB m f) (K : ℕ) :
    smulS ((PowerSeries.X : PowerSeries LL) ^ K) f = fun k => f (k - K) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf _ k (N + K + 1) (by omega), Finset.sum_eq_single K]
  · simp [PowerSeries.coeff_X_pow]
  · intro j _ hj
    simp [PowerSeries.coeff_X_pow, hj]
  · intro hK
    exact absurd (Finset.mem_range.mpr (by omega)) hK

theorem smulS_mul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g h : PowerSeries LL) :
    smulS (g * h) f = smulS g (smulS h f) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  have hR : ∀ i : ℕ, smulS h f (k - i) =
      ∑ j ∈ Finset.range N, PowerSeries.coeff j h • f (k - i - j) :=
    fun i => smulS_eq_sum hf h (k - i) N (by omega)
  have hzero : ∀ i j : ℕ, N ≤ i + j → f (k - i - j) = 0 := fun i j hij => hf _ (by omega)
  calc smulS (g * h) f k
      = ∑ n ∈ Finset.range N, PowerSeries.coeff n (g * h) • f (k - n) :=
        smulS_eq_sum hf _ k N hN
    _ = ∑ n ∈ Finset.range N, ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i g * PowerSeries.coeff (n - i) h) • f (k - i - (n - i : ℕ)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [PowerSeries.coeff_mul, Finset.sum_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := by
          simp only [Finset.mem_range, Nat.succ_eq_add_one] at hi
          omega
        have e : k - (n : ℤ) = k - i - ((n - i : ℕ) : ℤ) := by omega
        rw [e]
        try rfl
    _ = ∑ i ∈ Finset.range N, ∑ n ∈ Finset.Ico i N,
          (PowerSeries.coeff i g * PowerSeries.coeff (n - i) h) • f (k - i - (n - i : ℕ)) :=
        Finset.sum_comm' fun n i => by
          simp only [Finset.mem_range, Finset.mem_Ico]
          constructor <;> intro hh <;> omega
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i),
          (PowerSeries.coeff i g * PowerSeries.coeff j h) • f (k - i - j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Nat.add_sub_cancel_left]
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (PowerSeries.coeff i g * PowerSeries.coeff j h) • f (k - i - j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        apply Finset.sum_subset
        · intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
        · intro j hj hj'
          simp only [Finset.mem_range, not_lt] at hj hj'
          simp only [hzero i j (by omega), smul_zero]
    _ = smulS g (smulS h f) k := by
        rw [smulS_eq_sum (LB_smulS hf h) g k N hN]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hR, Finset.smul_sum, smul_smul]

theorem smulS_inv {m : ℤ} {f : ℤ → V} (hf : LB m f) (u : PowerSeries LL)
    (hu : PowerSeries.constantCoeff u ≠ 0) : smulS u⁻¹ (smulS u f) = f := by
  have h1 : u⁻¹ * u = 1 := by
    exact PowerSeries.inv_mul_cancel u hu
  rw [← smulS_mul hf, h1, smulS_one hf]

def Dg (Fil : ℤ → Submodule LL V) (s : ℤ) (f : ℤ → V) : Prop := ∀ k, f k ∈ Fil (s - k)

theorem Dg_smulS {Fil : ℤ → Submodule LL V} (hF : Antitone Fil) {m s : ℤ} {f : ℤ → V}
    (hf : LB m f) (hD : Dg Fil s f) (g : PowerSeries LL) : Dg Fil s (smulS g f) := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum hf g k N hN]
  refine sum_mem fun j _ => Submodule.smul_mem _ _ ?_
  exact hF (by omega : s - k ≤ s - (k - (j : ℤ))) (hD (k - j))

def resc (χ : LL) (f : ℤ → V) : ℤ → V := fun k => (χ ^ k) • f k

theorem LB_resc {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) : LB m (resc χ f) := by
  intro k hk
  show (χ ^ k) • f k = 0
  rw [hf k hk, smul_zero]

theorem smulS_rescale {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) (hχ : χ ≠ 0)
    (g : PowerSeries LL) : smulS (PowerSeries.rescale χ g) (resc χ f) = resc χ (smulS g f) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt_int_sub k m
  rw [smulS_eq_sum (LB_resc hf χ) _ k N hN]
  show _ = χ ^ k • smulS g f k
  rw [smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : χ ^ j * χ ^ (k - (j : ℤ)) = χ ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hχ]
    congr 1
    omega
  show PowerSeries.coeff j (PowerSeries.rescale χ g) • (χ ^ (k - (j : ℤ)) • f (k - j)) =
    χ ^ k • (PowerSeries.coeff j g • f (k - j))
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul, mul_right_comm, e]

end Formalism.MainNotions.N.Pv.LocalLengthBound.Ser
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ZpowNeOneOfClose
noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Val

variable {LL : Type} [Field LL] (v : AddValuation LL (WithTop ℚ))

theorem v_natCast_nonneg (m : ℕ) : 0 ≤ v (m : LL) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_le_add ih v.map_one.symm.le

private theorem withTop_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  exact WithTop.coe_lt_coe.2 zero_lt_one

private theorem withTop_rat_not_one_add_one_le_one : ¬ ((1 : WithTop ℚ) + 1 ≤ 1) := by
  rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]; norm_num

private theorem le_v_sum_range_of_forall (f : ℕ → LL) (g : WithTop ℚ) (hf : ∀ i, g ≤ v (f i)) (m : ℕ) :
    g ≤ v (∑ i ∈ Finset.range m, f i) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact v.map_le_add ih (hf n)

theorem v_intCast_nonneg (z : ℤ) : 0 ≤ v (z : LL) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.cast_natCast]; exact v_natCast_nonneg v n
  · rw [Int.cast_neg, Int.cast_natCast, v.map_neg]; exact v_natCast_nonneg v n

variable {p : ℕ} (hp : p.Prime) (hv : v (p : LL) = 1)
include hp hv

theorem v_natCast_eq_zero (m : ℕ) (hm : ¬ p ∣ m) : v (m : LL) = 0 := by
  have h0 := v_natCast_nonneg v m
  refine le_antisymm (not_lt.mp fun hlt => ?_) h0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hb
  have hL : (p : LL) * (Nat.gcdA p m : LL) + (m : LL) * (Nat.gcdB p m : LL) = 1 := by
    have h := congrArg (fun z : ℤ => (z : LL)) hb; push_cast at h; exact h.symm
  have h1 : 0 < v ((p : LL) * (Nat.gcdA p m : LL)) := by
    rw [v.map_mul, hv]
    exact lt_of_lt_of_le withTop_zero_lt_one (le_add_of_nonneg_right (v_intCast_nonneg v _))
  have h2 : 0 < v ((m : LL) * (Nat.gcdB p m : LL)) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (v_intCast_nonneg v _))
  have h3 : min (v ((p : LL) * (Nat.gcdA p m : LL))) (v ((m : LL) * (Nat.gcdB p m : LL))) ≤
      v ((p : LL) * (Nat.gcdA p m : LL) + (m : LL) * (Nat.gcdB p m : LL)) :=
    v.map_le_add (min_le_left _ _) (min_le_right _ _)
  rw [hL, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

omit hp hv in
theorem v_eq_zero_of_close {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) : v ξ = 0 := by
  have hpos : 0 < v (ξ - 1) := lt_of_lt_of_le withTop_zero_lt_one h1
  have h0 : (0 : WithTop ℚ) ≤ v ((ξ - 1) + 1) := v.map_le_add hpos.le v.map_one.symm.le
  rw [sub_add_cancel] at h0
  refine le_antisymm (not_lt.mp fun hlt => ?_) h0
  have h3 : min (v ξ) (v (ξ - 1)) ≤ v (ξ + -(ξ - 1)) :=
    v.map_le_add (min_le_left _ _) (by rw [v.map_neg]; exact min_le_right _ _)
  have e : ξ + -(ξ - 1) = 1 := by ring
  rw [e, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min hlt hpos))

omit hp hv in
theorem v_geom_nonneg {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    0 ≤ v (∑ i ∈ Finset.range m, ξ ^ i) := by
  have hξ := v_eq_zero_of_close v h1
  exact le_v_sum_range_of_forall v (fun i => ξ ^ i) 0
    (fun i => by
      show (0 : WithTop ℚ) ≤ v (ξ ^ i)
      exact le_of_eq (by rw [v.map_pow, hξ, smul_zero])) m

omit hp hv in
theorem v_pow_sub_one {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    v (ξ - 1) ≤ v (ξ ^ m - 1) := by
  rw [← geom_sum_mul ξ m, v.map_mul]
  exact le_add_of_nonneg_left (v_geom_nonneg v h1 m)


omit hp hv in
theorem v_geom_sub {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    v (ξ - 1) ≤ v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : LL)) := by
  have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : LL) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  exact le_v_sum_range_of_forall v (fun i => ξ ^ i - 1) _ (fun i => v_pow_sub_one v h1 i) m

theorem pow_p_ne_one {ξ : LL} (hp3 : 3 ≤ p) (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (hne : ξ ≠ 1) :
    ξ ^ p ≠ 1 := by
  intro hpow
  have hS : (∑ i ∈ Finset.range p, ξ ^ i) = 0 := by
    have h := geom_sum_mul ξ p
    rw [hpow, sub_self] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hne
  have eSp : (∑ i ∈ Finset.range p, ξ ^ i) - (p : LL) =
      (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) * (ξ - 1) := by
    rw [Finset.sum_mul]
    simp only [geom_sum_mul]
    rw [Finset.sum_sub_distrib]; simp
  have hT : 1 ≤ v (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) := by
    have e2 : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) =
        (∑ i ∈ Finset.range p, ((∑ j ∈ Finset.range i, ξ ^ j) - (i : LL))) +
          (((∑ i ∈ Finset.range p, i : ℕ)) : LL) := by
      rw [Finset.sum_sub_distrib, Nat.cast_sum]; ring
    rw [e2]
    apply v.map_le_add
    · exact le_v_sum_range_of_forall v _ _ (fun i => le_trans h1 (v_geom_sub v h1 i)) p
    · obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := hp.eq_two_or_odd'.resolve_left (by omega)
      have hs : (∑ i ∈ Finset.range p, i) = p * k := by
        apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
        rw [Finset.sum_range_id_mul_two, hk, Nat.add_sub_cancel]
        ring
      rw [hs, Nat.cast_mul, v.map_mul, hv]
      exact le_add_of_nonneg_right (v_natCast_nonneg v k)
  have hvS : 1 + 1 ≤ v ((∑ i ∈ Finset.range p, ξ ^ i) - (p : LL)) := by
    rw [eSp, v.map_mul]
    exact add_le_add hT h1
  rw [hS, zero_sub, v.map_neg, hv] at hvS
  exact withTop_rat_not_one_add_one_le_one hvS

theorem pow_ne_one_of_close (hp3 : 3 ≤ p) :
    ∀ (m : ℕ) (ξ : LL), 0 < m → (1 : WithTop ℚ) ≤ v (ξ - 1) → ξ ≠ 1 → ξ ^ m ≠ 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ξ hm h1 hne
    by_cases hpm : p ∣ m
    · obtain ⟨k, rfl⟩ := hpm
      have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hlt : k < p * k := by
        have : 1 < p := hp.one_lt
        nlinarith
      rw [pow_mul]
      exact ih k hlt (ξ ^ p) hk (le_trans h1 (v_pow_sub_one v h1 p))
        (pow_p_ne_one v hp hv hp3 h1 hne)
    · intro hpow
      have hS : (∑ i ∈ Finset.range m, ξ ^ i) = 0 := by
        have h := geom_sum_mul ξ m
        rw [hpow, sub_self] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd (sub_eq_zero.mp h') hne
      have h2 := v_geom_sub v h1 m
      rw [hS, zero_sub, v.map_neg, v_natCast_eq_zero v hp hv m hpm] at h2
      exact absurd (le_trans h1 h2) (not_le.mpr withTop_zero_lt_one)

theorem zpow_ne_one_of_close (hp3 : 3 ≤ p) (ξ : LL) (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1))
    (hne : ξ ≠ 1) (k : ℤ) (hk : k ≠ 0) : ξ ^ k ≠ 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hn : 0 < n := by omega
    rw [zpow_natCast]
    exact pow_ne_one_of_close v hp hv hp3 n ξ hn h1 hne
  · have hn : 0 < n := by omega
    rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]
    exact pow_ne_one_of_close v hp hv hp3 n ξ hn h1 hne

end Formalism.MainNotions.N.Pv.LocalLengthBound.Val
end
end
