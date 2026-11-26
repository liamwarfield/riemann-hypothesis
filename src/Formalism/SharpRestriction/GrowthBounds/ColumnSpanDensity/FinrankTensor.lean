module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DensityNumericalFacts

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

private theorem choose_add_succ_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + (m + 1)).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * ((A : ℚ) + m + 1) / ((m : ℚ) + 1) := by
  have h : (A + m + 1) * (A + m).choose m = (A + m + 1).choose (m + 1) * (m + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq (A + m) m
    | exact Nat.succ_mul_choose_eq (A + m) m
  rw [eq_div_iff (by positivity), show A + (m + 1) = A + m + 1 by omega]
  have h' : (((A + m + 1) * (A + m).choose m : ℕ) : ℚ) = (((A + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linear_combination -h'

private theorem choose_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + m).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * (A : ℚ) / ((m : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (A + m) m
  rw [Nat.add_sub_cancel] at h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast h

theorem prodA (m A : ℕ) :
    ∏ j : Fin m, (((A : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = ((A + m).choose m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, choose_add_succ_succ_eq_choose_mul_div]
    ring

theorem prodB (m B : ℕ) :
    ∏ j : Fin m, (((B : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) = ((B + m).choose m : ℚ) := by
  rw [← prodA m B, ← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.isLt
  have hr : (((Fin.revPerm j : Fin m) : ℕ) : ℚ) = (m : ℚ) - ((j : ℕ) : ℚ) - 1 := by
    rw [Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hr]
  congr 1 <;> ring

theorem weylDim_const (m : ℕ) (d : ℤ) : weylDim m (fun _ => d) = 1 := by
  unfold weylDim
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · have hij : (i : ℕ) < (j : ℕ) := h
    have hq : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
    simp only [sub_self, Int.cast_zero, zero_add]
    exact div_self (sub_pos.mpr hq).ne'
  · rfl

private theorem weylDim_cons_eq_prod_mul (n : ℕ) (a : ℤ) (lam : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons a lam) =
      (∏ j : Fin n, (((a - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n lam := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [lt_self_iff_false, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [if_pos (Fin.succ_pos j)]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    push_cast
    congr 1 <;> ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.not_lt_zero, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.cons_succ, Fin.val_succ, Fin.succ_lt_succ_iff]
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

private theorem weylDim_snoc_eq_mul_prod (n : ℕ) (lam : Fin n → ℤ) (b : ℤ) :
    weylDim (n + 1) (Fin.snoc lam b) =
      weylDim n lam * ∏ i : Fin n, (((lam i - b : ℤ) : ℚ) + (n : ℚ) - ((i : ℕ) : ℚ)) / ((n : ℚ) - ((i : ℕ) : ℚ)) := by
  unfold weylDim
  have h1 : ∀ g : Fin (n + 1) → ℚ, (∏ j : Fin (n + 1), if Fin.last n < j then g j else 1) = 1 :=
    fun g => Finset.prod_eq_one fun j _ => if_neg (not_lt.mpr (Fin.le_last j))
  rw [Fin.prod_univ_castSucc, h1, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc, if_pos (Fin.castSucc_lt_last i)]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc, Fin.castSucc_lt_castSucc_iff]
  · simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]

theorem weylDim_hwt_eq (m A B : ℕ) : weylDim (m + 2) (hwt m A B) = (dimHar (m + 1) A B : ℚ) := by
  unfold hwt
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_zero, zero_sub, neg_neg, sub_neg_eq_add, zero_add]
  rw [prodA m A, prodB m B]
  unfold dimHar dimPol
  have hle : (if A = 0 ∨ B = 0 then 0 else (A - 1 + (m + 1)).choose (m + 1) * (B - 1 + (m + 1)).choose (m + 1)) ≤
      (A + (m + 1)).choose (m + 1) * (B + (m + 1)).choose (m + 1) := by
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
  rw [Nat.cast_sub hle, Nat.cast_mul, choose_add_succ_succ_eq_choose_mul_div A m, choose_add_succ_succ_eq_choose_mul_div B m]
  split_ifs with h
  · rcases h with rfl | rfl <;> push_cast <;> field_simp <;> ring
  · push_neg at h
    rw [Nat.cast_mul, show A - 1 + (m + 1) = A + m by omega, show B - 1 + (m + 1) = B + m by omega,
      choose_succ_eq_choose_mul_div A m, choose_succ_eq_choose_mul_div B m]
    field_simp
    ring

theorem weylDim_vec (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  have hz : (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0 : Fin (m + 1) → ℤ) = fun _ => 0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  rw [hz, weylDim_cons_eq_prod_mul, weylDim_const, mul_one]
  push_cast
  try simp only [sub_zero]
  rw [prodA (m + 1) d]

theorem weylDim_cov (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (d : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_self, zero_add, sub_zero]
  have h1 : (∏ j : Fin m, (((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = 1 :=
    Finset.prod_eq_one fun j _ => div_self (by positivity)
  rw [prodB m d, h1, one_mul, choose_add_succ_succ_eq_choose_mul_div d m]
  ring

theorem finrank_tensor (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) := by
  classical
  haveI : IsFractionRing Kf Kf := by
    first
    | infer_instance
    | exact IsLocalization.atUnits Kf (nonZeroDivisors Kf)
        (fun x hx => (IsUnit.mem_submonoid_iff _).mpr (Ne.isUnit (nonZeroDivisors.ne_zero hx)))
  let M : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf) := fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)
  let B : ∀ s, Module.Basis (Module.Basis.ofVectorSpaceIndex Kf (M s)) Kf (M s) :=
    fun s => Module.Basis.ofVectorSpace Kf (M s)
  let b : ∀ s, Module.Basis.ofVectorSpaceIndex Kf (M s) → MvPolynomial (Fin k × Fin n) Kf :=
    fun s i => ((B s i : M s) : MvPolynomial (Fin k × Fin n) Kf)
  have hli : ∀ s, LinearIndependent Kf (b s) := fun s =>
    (B s).linearIndependent.map' (M s).subtype (Submodule.ker_subtype _)
  have hsp : ∀ s, Submodule.span Kf (Set.range (b s)) = M s := by
    intro s
    have h1 : Set.range (b s) = (M s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, (B s).span_eq, Submodule.map_subtype_top]
  obtain ⟨hT, hTs⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf S k n (fun s => Module.Basis.ofVectorSpaceIndex Kf (M s)) M b hli hsp
  show Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf M) = _
  rw [← hTs, Module.finrank_eq_nat_card_basis (Module.Basis.span hT), Nat.card_pi]
  exact Finset.prod_congr rfl fun s _ => (Module.finrank_eq_nat_card_basis (B s)).symm

theorem RS.charZeroO {p n' : ℕ} (R : RS p n') : CharZero R.O := by
  obtain ⟨c, hc⟩ := CharP.exists R.O
  rcases CharP.char_is_prime_or_zero R.O c with h | h
  · exfalso
    have hc0 : (c : R.O) = 0 := CharP.cast_eq_zero R.O c
    by_cases hcp : c = p
    · exact R.p_ne (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h R.std.1.prime).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : R.O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact R.p_not_unit (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero R.O

theorem RS.charZero {p n' : ℕ} (R : RS p n') : CharZero R.Kf := by
  have := R.charZeroO
  have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective R.O R.Kf)

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoHundredLeRadius
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def Cst.TM (K : Cst) : ℝ := max K.TLP (max (4 * K.CH + 1) (2 * K.Cm + 24))

theorem TM_pos (K : Cst) : 0 < K.TM :=
  lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _)))
    (le_max_left _ _)

theorem two_hundred_le_radius {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : (200 : ℝ) ≤ X.ar := by
  have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
  linarith [B.hpa]

theorem log_round {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    Real.log X.ar ≤ Real.log X.a ∧ Real.log X.a ≤ Real.log X.ar + 1 / 200 := by
  have h200 := two_hundred_le_radius B
  have har : 0 < X.ar := by linarith
  have ha : (0 : ℝ) < X.a := by linarith [B.haa]
  refine ⟨Real.log_le_log har B.haa, ?_⟩
  have h1 : Real.log ((X.a : ℝ) / X.ar) = Real.log X.a - Real.log X.ar := Real.log_div ha.ne' har.ne'
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha har)
  have h3 : (X.a : ℝ) / X.ar - 1 ≤ 1 / 200 := by
    have : (X.a : ℝ) / X.ar ≤ 1 + 1 / 200 := by
      rw [div_le_iff₀ har]
      linarith [B.haa1]
    linarith
  linarith

theorem La_round {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) :
    LaI K.C₀ X.N₁ X.ar ≤ LaI K.C₀ X.N₁ X.a ∧ LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar ∧
      LaI K.C₀ X.N₁ X.a * Real.log X.a ≤ 2 * (LaI K.C₀ X.N₁ X.ar * Real.log X.ar) := by
  obtain ⟨h1, h2⟩ := log_round B
  have hl := B.hlog1
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  unfold LaI
  refine ⟨mul_le_mul_of_nonneg_left h1 hcn, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (by linarith : Real.log X.a ≤ 2 * Real.log X.ar) hcn
    linarith
  · have hsq : Real.log X.a * Real.log X.a ≤ 2 * (Real.log X.ar * Real.log X.ar) := by
      have a1 : Real.log X.a ≤ (1 + 1 / 200) * Real.log X.ar := by linarith
      have a0 : 0 ≤ Real.log X.a := by linarith
      have a2 := mul_le_mul a1 a1 a0 (by linarith)
      have a3 : 0 ≤ Real.log X.ar * Real.log X.ar := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hsq hcn
    calc K.C₀ * (X.N₁ : ℝ) ^ 2 * Real.log X.a * Real.log X.a
        = K.C₀ * (X.N₁ : ℝ) ^ 2 * (Real.log X.a * Real.log X.a) := by ring
      _ ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 * (2 * (Real.log X.ar * Real.log X.ar)) := this
      _ = _ := by ring

theorem r12 (Yb N La La' b' k w : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 ≤ b') (hk : 0 < k) (h2 : La' ≤ 2 * La)
    (h : Yb * N * La * b' / k ≤ w) : Yb / 2 * N * La' * b' / k ≤ w := by
  have hc : 0 ≤ Yb * N * b' / k := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : La' / 2 ≤ La) hc
  calc Yb / 2 * N * La' * b' / k = Yb * N * b' / k * (La' / 2) := by ring
    _ ≤ Yb * N * b' / k * La := this
    _ = Yb * N * La * b' / k := by ring
    _ ≤ w := h

theorem r15 (Yb N La La' k : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (h2 : La' ≤ 2 * La) (h : 2 * Yb * N * La < k) :
    2 * (Yb / 2) * N * La' < k := by
  have hc : 0 ≤ Yb * N := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc 2 * (Yb / 2) * N * La' = Yb * N * La' := by ring
    _ ≤ Yb * N * (2 * La) := this
    _ = 2 * Yb * N * La := by ring
    _ < k := h

theorem r16 (k Y Yb N La La' l l' ar a' b' : ℝ) (hk : 0 ≤ k) (hY : 0 ≤ Y) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 < b')
    (ha : ar ≤ a') (h2 : La' * l' ≤ 2 * (La * l)) (h : k * Y ^ 2 * Yb * N * La * l ≤ ar / b') :
    k * Y ^ 2 * (Yb / 2) * N * La' * l' ≤ a' / b' := by
  have hc : 0 ≤ k * Y ^ 2 * Yb * N / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc k * Y ^ 2 * (Yb / 2) * N * La' * l' = k * Y ^ 2 * Yb * N / 2 * (La' * l') := by ring
    _ ≤ k * Y ^ 2 * Yb * N / 2 * (2 * (La * l)) := this
    _ = k * Y ^ 2 * Yb * N * La * l := by ring
    _ ≤ ar / b' := h
    _ ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le

theorem rde (CH CH1 N1 La La' k r : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 + 1 ≤ CH) (hN1 : 1 ≤ N1) (hLa : 1 ≤ La)
    (h2 : La' ≤ 2 * La) (hk : 0 < k) : CH1 * N1 * La' / k + r + 1 / k ≤ CH * N1 * La / k + r := by
  have h1 : CH1 * N1 * La' + 1 ≤ CH * N1 * La := by
    have a1 : CH1 * N1 * La' ≤ CH1 * N1 * (2 * La) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have a2 : 1 ≤ N1 * La := one_le_mul_of_one_le_of_one_le hN1 hLa
    have a3 : (2 * CH1 + 1) * (N1 * La) ≤ CH * (N1 * La) := mul_le_mul_of_nonneg_right hCH (by linarith)
    nlinarith
  have := div_le_div_of_nonneg_right h1 hk.le
  have e : (CH1 * N1 * La' + 1) / k = CH1 * N1 * La' / k + 1 / k := add_div _ _ _
  linarith

theorem rband (ar a' b' de de' k x : ℝ) (hb : 0 < b') (hk : 0 < k) (hka : k ≤ ar) (ha : ar ≤ a') (ha1 : a' ≤ ar + 1)
    (hde0 : 0 ≤ de') (hde6 : de' < 1 / 6) (hde : de' + 1 / k ≤ de)
    (h : a' / b' * (1 - 2 * de') ≤ x ∧ x ≤ a' / b' * (1 + 2 * de')) :
    ar / b' * (1 - 2 * de) ≤ x ∧ x ≤ ar / b' * (1 + 2 * de) := by
  have har : 0 < ar := lt_of_lt_of_le hk hka
  have hk1 : 0 < 1 / k := by positivity
  have hab : ar / b' ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le
  have hab0 : 0 ≤ ar / b' := by positivity
  constructor
  · refine le_trans ?_ h.1
    calc ar / b' * (1 - 2 * de) ≤ ar / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_left (by linarith) hab0
      _ ≤ a' / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_right hab (by linarith)
  · refine le_trans h.2 ?_
    have h1 : a' * (1 + 2 * de') ≤ ar * (1 + 2 * de) := by
      have a1 : a' * (1 + 2 * de') ≤ (ar + 1) * (1 + 2 * de') := mul_le_mul_of_nonneg_right ha1 (by linarith)
      have a2 : ar * (1 + 2 * de' + 2 * (1 / k)) ≤ ar * (1 + 2 * de) := mul_le_mul_of_nonneg_left (by linarith) har.le
      have a3 : 1 ≤ ar * (1 / k) := by
        rw [mul_one_div, le_div_iff₀ hk]
        linarith
      nlinarith
    calc a' / b' * (1 + 2 * de') = a' * (1 + 2 * de') / b' := by ring
      _ ≤ ar * (1 + 2 * de) / b' := div_le_div_of_nonneg_right h1 hb.le
      _ = _ := by ring

theorem r19 (CH CH1 N La La' k : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 4 * CH1 ≤ CH) (hN : 0 ≤ N) (hLa0 : 0 ≤ La')
    (h2 : La' ≤ 2 * La) (h : CH * N * La ^ 2 ≤ k) : CH1 * N * La' ^ 2 ≤ k := by
  have a1 : La' ^ 2 ≤ (2 * La) ^ 2 := pow_le_pow_left₀ hLa0 h2 2
  have a2 : CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := mul_le_mul_of_nonneg_left a1 (by positivity)
  have a3 : 4 * CH1 * (N * La ^ 2) ≤ CH * (N * La ^ 2) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := a2
    _ = 4 * CH1 * (N * La ^ 2) := by ring
    _ ≤ CH * (N * La ^ 2) := a3
    _ = CH * N * La ^ 2 := by ring
    _ ≤ k := h

theorem r22 (CH CH1 G L L' Dp : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 ≤ CH) (hG : 0 ≤ G) (hL : 0 ≤ L) (h2 : L' ≤ 2 * L)
    (h : CH * G * L ≤ Dp) : CH1 * G * L' ≤ Dp := by
  have a1 : CH1 * G * L' ≤ CH1 * G * (2 * L) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have a2 : 2 * CH1 * (G * L) ≤ CH * (G * L) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * G * L' ≤ CH1 * G * (2 * L) := a1
    _ = 2 * CH1 * (G * L) := by ring
    _ ≤ CH * (G * L) := a2
    _ = CH * G * L := by ring
    _ ≤ Dp := h

theorem hyp_round {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar := by
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  obtain ⟨l1, l2, l3⟩ := La_round hK B
  obtain ⟨-, -, g3, g4⟩ := logs_of B
  have hCH1 : 0 < K.CH := hK.2.1
  have hCH4 : 4 * K.CH + 1 ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCH
  have h108 : (108 : ℝ) ≤ CH :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCH
  have hYb0 : 0 ≤ X.Yb := by linarith
  have hN0 : (0 : ℝ) ≤ (X.TT.card : ℝ) := by positivity
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk0 : (0 : ℝ) < (X.m : ℝ) + 1 := by linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by linarith
  have hN1r : (1 : ℝ) ≤ (X.N₁ : ℝ) := B.hN1
  have hY0 : 0 ≤ X.Y := by linarith
  have hdd : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu + 1 / ((X.m : ℝ) + 1) ≤
      deI CH K.C₀ X.m X.N₁ X.ar X.b' X.bl X.bu := by
    unfold deI
    exact rde CH K.CH X.N₁ _ _ _ _ hCH1.le (by linarith) hN1r hLa1 l2 hk0
  have hk1 : 0 < 1 / ((X.m : ℝ) + 1) := by positivity
  have hde0 : 0 ≤ deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu := by
    unfold deI
    have : 0 ≤ X.bu - X.bl := by linarith
    positivity
  have hde6 : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu < 1 / 6 := by linarith
  have hka : (X.m : ℝ) + 1 ≤ X.ar := by
    have h1 : (X.m : ℝ) + 1 ≤ X.p := B.hkp
    have h2 := le_mul_of_one_le_right (by linarith [B.hp25] : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')
    linarith [B.hpa]
  refine ⟨hY, hp, hev, hseg2, hgap, hN1, hm, by linarith, hb, hbl, hbu, ?_, hIb2, by linarith, ?_, ?_, hde6, ?_, ?_,
    ?_, ?_, ?_, hcs, ?_⟩
  · exact r12 _ _ _ _ _ _ _ hYb0 hN0 hb.le hk0 l2 hIb1
  · exact r15 _ _ _ _ _ hYb0 hN0 l2 hk2
  · exact r16 _ _ _ _ _ _ _ _ _ _ _ hk0.le hY0 hYb0 hN0 hb B.haa l3 hab
  · exact lt_of_lt_of_le hpab (div_le_div_of_nonneg_right B.haa hb.le)
  · exact r19 CH _ _ _ _ _ hCH1.le (by linarith) hN0 hLa'0 l2 hkLa
  · intro d hd hc
    exact hband d hd (rband _ _ _ _ _ _ _ hb hk0 hka B.haa B.haa1.le hde0 hde6 hdd hc)
  · have : LaI K.C₀ X.N₁ X.ar * X.b' / ((X.m : ℝ) + 1) ≤ LaI K.C₀ X.N₁ X.a * X.b' / ((X.m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l1 hb.le) hk0.le
    linarith
  · have hG : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) := by positivity
    have := r22 CH K.CH _ _ _ _ hCH1.le (by linarith) hG (by linarith [B.hL1]) g4
      (by calc CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.ar
            = CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.ar := by ring
          _ ≤ (X.Dp : ℝ) := hD)
    calc K.CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.a
        = K.CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.a := by ring
      _ ≤ (X.Dp : ℝ) := this
  · have hG : (0 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
        ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : K.CH ≤ CH) hG
    calc K.CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y
        = K.CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := by ring
      _ ≤ CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := this
      _ = CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by ring
      _ ≤ X.b' := hsize

end Formalism.MainNotions.flipOneThree.Pf

end
end
