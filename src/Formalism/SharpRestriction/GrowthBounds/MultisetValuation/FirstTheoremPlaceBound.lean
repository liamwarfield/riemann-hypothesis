module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaApplyDScale
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.BiadditiveSecondVariable

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmRestNormOfPlace
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmPinvOfPlace
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NmNEqZero
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RationalLowerBounds
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

structure nm_Hyp {K : Type*} [Field K] (R : Subring K) (p : ℕ) : Prop where
  one_lt : 1 < p
  val : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R
  rk : ∀ x : K, x ≠ 0 → (∃ n : ℕ, (p : K) ^ n / x ∈ R) ∧ (x⁻¹ ∉ R → ∃ n : ℕ, x ^ n / (p : K) ∈ R)
  pinv : (p : K)⁻¹ ∉ R

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}

theorem nm_p_ne (h : nm_Hyp R p) : (p : K) ≠ 0 := by
  intro h0
  apply h.pinv
  rw [h0, inv_zero]
  exact R.zero_mem

theorem nm_root (h : nm_Hyp R p) {y : K} {k : ℕ} (hk : 0 < k) (hy : y ^ k ∈ R) : y ∈ R := by
  by_contra hyR
  have hy0 : y ≠ 0 := fun h0 => hyR (h0 ▸ R.zero_mem)
  have hinv : y⁻¹ ∈ R := (h.val y).resolve_left hyR
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : y ^ (m + 1) * y⁻¹ ^ m = y := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hy0, one_pow, mul_one]
  exact hyR (e ▸ R.mul_mem hy (R.pow_mem hinv _))

theorem nm_zpow_mem_iff (h : nm_Hyp R p) (k : ℤ) : (p : K) ^ k ∈ R ↔ 0 ≤ k := by
  constructor
  · intro hk
    by_contra hneg
    push_neg at hneg
    apply h.pinv
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hn
    have e : (p : K) ^ (-((n : ℤ) + 1)) = ((p : K)⁻¹) ^ (n + 1) := by
      rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, inv_pow]
    exact nm_root h (Nat.succ_pos n) (e ▸ hk)
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact R.pow_mem (natCast_mem R p) k

variable (R p)

def nm_P (x : K) (a : ℤ) (b : ℕ) : Prop := x ^ b * (p : K) ^ (-a) ∈ R

def rationalLowerBounds (x : K) : Set ℝ := {q | ∃ (a : ℤ) (b : ℕ), 0 < b ∧ q = (a : ℝ) / b ∧ nm_P R p x a b}

def nm_v (x : K) : ℝ := sSup (rationalLowerBounds R p x)

variable {R p}

theorem nm_T_nonempty (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : (rationalLowerBounds R p x).Nonempty := by
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).1
  refine ⟨_, -(n : ℤ), 1, one_pos, rfl, ?_⟩
  unfold nm_P
  rw [pow_one, neg_neg, zpow_natCast, mul_comm]
  rwa [div_inv_eq_mul] at hn

theorem nm_T_bdd (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : BddAbove (rationalLowerBounds R p x) := by
  have hp0 := nm_p_ne h
  obtain ⟨n, hn⟩ := (h.rk x hx).1
  refine ⟨n, ?_⟩
  rintro q ⟨a, b, hb, rfl, hP⟩
  have hxb : x ^ b ≠ 0 := pow_ne_zero _ hx
  have e : (p : K) ^ ((n : ℤ) * b - a) = ((p : K) ^ n / x) ^ b * (x ^ b * (p : K) ^ (-a)) := by
    rw [sub_eq_add_neg, zpow_add₀ hp0, ← Nat.cast_mul, zpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv,
      mul_assoc, inv_mul_cancel_left₀ hxb]
  have hmem : (p : K) ^ ((n : ℤ) * b - a) ∈ R := e ▸ R.mul_mem (R.pow_mem hn b) hP
  have h0 := (nm_zpow_mem_iff h _).1 hmem
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  have : (a : ℤ) ≤ (n : ℤ) * b := by linarith
  exact_mod_cast this

theorem nm_le_v (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) {a : ℤ} {b : ℕ} (hb : 0 < b) (hP : nm_P R p x a b) :
    (a : ℝ) / b ≤ nm_v R p x := by
  unfold nm_v
  exact le_csSup (nm_T_bdd h hx) ⟨a, b, hb, rfl, hP⟩

theorem nm_dich (h : nm_Hyp R p) (x : K) (a : ℤ) (b : ℕ) : nm_P R p x a b ∨ nm_P R p x⁻¹ (-a) b := by
  rcases h.val (x ^ b * (p : K) ^ (-a)) with h1 | h1
  · exact Or.inl h1
  · right
    unfold nm_P
    convert h1 using 1
    rw [mul_inv, inv_pow, neg_neg, zpow_neg, inv_inv]

theorem nm_P_mul (h : nm_Hyp R p) {x y : K} {a a' : ℤ} {b b' : ℕ} (hx : nm_P R p x a b) (hy : nm_P R p y a' b') :
    nm_P R p (x * y) (a * b' + a' * b) (b * b') := by
  unfold nm_P at *
  have e : (x * y) ^ (b * b') * (p : K) ^ (-(a * b' + a' * b)) =
      (x ^ b * (p : K) ^ (-a)) ^ b' * (y ^ b' * (p : K) ^ (-a')) ^ b := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← zpow_natCast ((p : K) ^ (-a)) b',
      ← zpow_natCast ((p : K) ^ (-a')) b, ← zpow_mul, ← zpow_mul, mul_comm b' b]
    have : (p : K) ^ (-(a * b' + a' * b)) = (p : K) ^ (-a * b') * (p : K) ^ (-a' * b) := by
      rw [← zpow_add₀ (nm_p_ne h)]; congr 1; ring
    rw [this]
    ring
  rw [e]
  exact R.mul_mem (R.pow_mem hx _) (R.pow_mem hy _)

theorem nm_v_mul_ge (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p x + nm_v R p y ≤ nm_v R p (x * y) := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have h1 : ∀ q' ∈ rationalLowerBounds R p y, nm_v R p x ≤ nm_v R p (x * y) - q' := by
    rintro q' ⟨a', b', hb', rfl, hP'⟩
    apply csSup_le (nm_T_nonempty h hx)
    rintro q ⟨a, b, hb, rfl, hP⟩
    have h2 := nm_le_v h hxy (Nat.mul_pos hb hb') (nm_P_mul h hP hP')
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hbR' : (b' : ℝ) ≠ 0 := by exact_mod_cast hb'.ne'
    have e : (((a * b' + a' * b : ℤ) : ℝ)) / ((b * b' : ℕ) : ℝ) = (a : ℝ) / b + (a' : ℝ) / b' := by
      push_cast
      field_simp
    rw [e] at h2
    linarith
  have h3 : nm_v R p y ≤ nm_v R p (x * y) - nm_v R p x := by
    apply csSup_le (nm_T_nonempty h hy)
    intro q' hq'
    have := h1 q' hq'
    linarith
  linarith

theorem nm_v_one (h : nm_Hyp R p) : nm_v R p (1 : K) = 0 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h one_ne_zero)
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [one_pow, one_mul] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have ha : (a : ℝ) ≤ 0 := by
      have : a ≤ 0 := by linarith
      exact_mod_cast this
    exact div_nonpos_of_nonpos_of_nonneg ha (Nat.cast_nonneg _)
  · have := nm_le_v h (one_ne_zero (α := K)) (a := 0) (b := 1) Nat.one_pos (by
      unfold nm_P
      simp only [pow_one, neg_zero, zpow_zero, mul_one]
      exact R.one_mem)
    simpa using this

theorem nm_v_inv (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : nm_v R p x⁻¹ = -nm_v R p x := by
  have hx' := inv_ne_zero hx
  have h1 : nm_v R p x + nm_v R p x⁻¹ ≤ 0 := by
    have := nm_v_mul_ge h hx hx'
    rwa [mul_inv_cancel₀ hx, nm_v_one h] at this
  have h2 : 0 ≤ nm_v R p x + nm_v R p x⁻¹ := by
    by_contra hneg
    have hlt : nm_v R p x < -nm_v R p x⁻¹ := by linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rcases nm_dich h x q.num q.den with h3 | h3
    · have := nm_le_v h hx q.den_pos h3
      rw [← hq] at this
      linarith
    · have := nm_le_v h hx' q.den_pos h3
      have e : (((-q.num : ℤ)) : ℝ) / (q.den : ℝ) = -(q : ℝ) := by
        rw [hq]; push_cast; ring
      rw [e] at this
      linarith
  linarith

theorem nm_v_mul (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nm_v R p (x * y) = nm_v R p x + nm_v R p y := by
  apply le_antisymm _ (nm_v_mul_ge h hx hy)
  have h1 := nm_v_mul_ge h (mul_ne_zero hx hy) (inv_ne_zero hy)
  rw [mul_assoc, mul_inv_cancel₀ hy, mul_one, nm_v_inv h hy] at h1
  linarith

theorem nm_v_nonneg (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) (hxR : x ∈ R) : 0 ≤ nm_v R p x := by
  have := nm_le_v h hx (a := 0) (b := 1) Nat.one_pos (by
    unfold nm_P
    simp only [pow_one, neg_zero, zpow_zero, mul_one]
    exact hxR)
  simpa using this

theorem nm_v_neg (h : nm_Hyp R p) {x : K} (hxR : x ∉ R) : nm_v R p x < 0 := by
  have hx : x ≠ 0 := fun h0 => hxR (h0 ▸ R.zero_mem)
  obtain ⟨n, hn⟩ := (h.rk x⁻¹ (inv_ne_zero hx)).2 (by rwa [inv_inv])
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero, one_div] at hn
      exact h.pinv hn
    · exact h0
  have h1 := nm_le_v h (inv_ne_zero hx) (a := 1) (b := n) hn0 (by
    unfold nm_P
    rw [zpow_neg_one, ← div_eq_mul_inv]
    exact hn)
  rw [nm_v_inv h hx] at h1
  have : (0 : ℝ) < ((1 : ℤ) : ℝ) / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  linarith

theorem nm_v_nonneg_iff (h : nm_Hyp R p) {x : K} (hx : x ≠ 0) : 0 ≤ nm_v R p x ↔ x ∈ R :=
  ⟨fun h0 => by
    by_contra hxR
    exact absurd (nm_v_neg h hxR) (not_lt.2 h0), nm_v_nonneg h hx⟩

theorem nm_v_p (h : nm_Hyp R p) : nm_v R p (p : K) = 1 := by
  apply le_antisymm
  · apply csSup_le (nm_T_nonempty h (nm_p_ne h))
    rintro q ⟨a, b, hb, rfl, hP⟩
    unfold nm_P at hP
    rw [← zpow_natCast, ← zpow_add₀ (nm_p_ne h)] at hP
    have := (nm_zpow_mem_iff h _).1 hP
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [div_le_one hb']
    have : a ≤ b := by linarith
    exact_mod_cast this
  · have := nm_le_v h (nm_p_ne h) (a := 1) (b := 1) Nat.one_pos (by
      unfold nm_P
      rw [pow_one, zpow_neg_one, mul_inv_cancel₀ (nm_p_ne h)]
      exact R.one_mem)
    simpa using this

theorem nm_v_add (h : nm_Hyp R p) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (nm_v R p x) (nm_v R p y) ≤ nm_v R p (x + y) := by
  have key : ∀ {x y : K}, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → x / y ∈ R → nm_v R p y ≤ nm_v R p (x + y) := by
    intro x y _ hy hxy hR
    have e : x + y = y * (1 + x / y) := by field_simp; ring
    have h1 : 1 + x / y ≠ 0 := by
      intro h0
      apply hxy
      rw [e, h0, mul_zero]
    rw [e, nm_v_mul h hy h1]
    have := nm_v_nonneg h h1 (R.add_mem R.one_mem hR)
    linarith
  rcases h.val (x / y) with h1 | h1
  · exact le_trans (min_le_right _ _) (key hx hy hxy h1)
  · rw [inv_div] at h1
    rw [add_comm] at hxy ⊢
    exact le_trans (min_le_left _ _) (key hy hx hxy h1)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open scoped Classical

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}


variable (R p) in
def nm_N (x : K) : ℝ := if x = 0 then 0 else (p : ℝ) ^ (-nm_v R p x)

theorem nm_N_zero : nm_N R p (0 : K) = 0 := by
  simp [nm_N]

theorem nm_N_of_ne {x : K} (hx : x ≠ 0) : nm_N R p x = (p : ℝ) ^ (-nm_v R p x) := by
  simp [nm_N, hx]

theorem nm_pR (h : nm_Hyp R p) : (1 : ℝ) < p := by
  exact_mod_cast h.one_lt

theorem nm_N_nonneg (h : nm_Hyp R p) (x : K) : 0 ≤ nm_N R p x := by
  unfold nm_N
  split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).le

theorem nm_N_mul (h : nm_Hyp R p) (x y : K) : nm_N R p (x * y) = nm_N R p x * nm_N R p y := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  by_cases hy : y = 0
  · simp [nm_N, hy]
  rw [nm_N_of_ne (mul_ne_zero hx hy), nm_N_of_ne hx, nm_N_of_ne hy, nm_v_mul h hx hy, neg_add,
    Real.rpow_add (zero_lt_one.trans (nm_pR h))]

theorem nm_N_eq_zero (h : nm_Hyp R p) (x : K) : nm_N R p x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  · rw [nm_N_of_ne hx]
    simp only [hx, iff_false]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).ne'

theorem nm_N_add (h : nm_Hyp R p) (x y : K) : nm_N R p (x + y) ≤ max (nm_N R p x) (nm_N R p y) := by
  by_cases hx : x = 0
  · simp only [hx, zero_add, nm_N_zero]
    exact le_max_right _ _
  by_cases hy : y = 0
  · simp only [hy, add_zero, nm_N_zero]
    exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, nm_N_zero]
    exact le_max_of_le_left (nm_N_nonneg h x)
  rw [nm_N_of_ne hxy, nm_N_of_ne hx, nm_N_of_ne hy]
  have hp1 : (1 : ℝ) ≤ p := (nm_pR h).le
  have hm := nm_v_add h hx hy hxy
  rcases le_total (nm_v R p x) (nm_v R p y) with hle | hle
  · rw [min_eq_left hle] at hm
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  · rw [min_eq_right hle] at hm
    exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))

theorem nm_N_p (h : nm_Hyp R p) : nm_N R p (p : K) = (p : ℝ)⁻¹ := by
  rw [nm_N_of_ne (nm_p_ne h), nm_v_p h, Real.rpow_neg_one]

theorem nm_N_le_one (h : nm_Hyp R p) (x : K) : nm_N R p x ≤ 1 ↔ x ∈ R := by
  by_cases hx : x = 0
  · subst hx
    simp only [nm_N_zero, zero_le_one, true_iff]
    exact R.zero_mem
  rw [nm_N_of_ne hx, ← nm_v_nonneg_iff h hx]
  have e : (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
  rw [e, Real.rpow_le_rpow_left_iff (nm_pR h), neg_nonpos]

def nm_abs (h : nm_Hyp R p) : AbsoluteValue K ℝ where
  toFun := nm_N R p
  map_mul' := nm_N_mul h
  nonneg' := nm_N_nonneg h
  eq_zero' := nm_N_eq_zero h
  add_le' x y := le_trans (nm_N_add h x y) (max_le_add_of_nonneg (nm_N_nonneg h x) (nm_N_nonneg h y))

theorem nm_extG {K : Type} [Field K] (N : AbsoluteValue K ℝ) (hna : ∀ x y, N (x + y) ≤ max (N x) (N y)) (c : K)
    (hc : 1 < N c) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra K K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ∀ x, ‖algebraMap K K' x‖ = N x := by
  let nK : NormedField K := N.toNormedField
  have hnorm : ∀ x : K, ‖x‖ = N x := fun _ => rfl
  have hnatK : ∀ n : ℕ, N (n : K) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact le_trans (hna _ _) (max_le ih (by simp))
  have hcast : ∀ n : ℕ, ((n : K) : UniformSpace.Completion K) = (n : UniformSpace.Completion K) := fun n =>
    map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n
  have hnatC : ∀ n : ℕ, ‖(n : UniformSpace.Completion K)‖ ≤ 1 := by
    intro n
    rw [← hcast, UniformSpace.Completion.norm_coe]
    exact hnatK n
  have uC : IsUltrametricDist (UniformSpace.Completion K) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnatC
  let nnC : NontriviallyNormedField (UniformSpace.Completion K) :=
    { (inferInstance : NormedField (UniformSpace.Completion K)) with
      non_trivial := ⟨(c : UniformSpace.Completion K), by rw [UniformSpace.Completion.norm_coe]; exact hc⟩ }
  let nL : NormedField (AlgebraicClosure (UniformSpace.Completion K)) :=
    spectralNorm.normedField (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
  have hext : ∀ z : UniformSpace.Completion K,
      ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) z‖ = ‖z‖ :=
    fun z => spectralNorm_extends z
  let aL : Algebra K (AlgebraicClosure (UniformSpace.Completion K)) :=
    ((algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))).comp
      (UniformSpace.Completion.coeRingHom (α := K))).toAlgebra
  refine ⟨AlgebraicClosure (UniformSpace.Completion K), nL, aL, ?_, inferInstance, ?_⟩
  · apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
    intro n
    have := hext (n : UniformSpace.Completion K)
    rw [map_natCast] at this
    rw [this]
    exact hnatC n
  · intro x
    show ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
      (x : UniformSpace.Completion K)‖ = N x
    rw [hext, UniformSpace.Completion.norm_coe]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_pinv_of_eO (Y : Pend X) (he : 0 < X.eO) : (p : Y.Kc)⁻¹ ∉ Y.Oc := by
  intro hmem
  have hinj := algebraMap_inj Y he
  have hpO : (p : X.G.O) ≠ 0 := fun h0 =>
    pow_ne_zero _ X.unif.ne_zero (X.eO_spec.eq_zero_iff.mp h0)
  have hpK : (p : X.G.Kf) ≠ 0 := by
    have := (map_ne_zero_iff _ hinj).mpr hpO
    rwa [map_natCast] at this
  have h1 : algebraMap X.G.Kf Y.Kc ((p : X.G.Kf)⁻¹) ∈ Y.Oc := by
    rwa [map_inv₀, map_natCast]
  obtain ⟨a, ha⟩ := (mem_intK (X := X)).mp ((Y.Oc_K _).mp h1)

  have h1eq : (p : X.G.O) * a = 1 := hinj (by
    rw [map_mul, ha, map_natCast, mul_inv_cancel₀ hpK, map_one])
  have hpu : IsUnit (p : X.G.O) := IsUnit.of_mul_eq_one _ h1eq
  exact X.unif.not_isUnit
    ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp he)).mp (X.eO_spec.isUnit_iff.mp hpu))

theorem nm_pinv_of_place (Y : Pend X) (v : X.Pl) : (p : Y.Kc)⁻¹ ∉ Y.Oc :=
  nm_pinv_of_eO Y (eO_pos X v)

theorem nm_hyp (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : nm_Hyp Y.Oc p :=
  ⟨hp.out.one_lt, Y.Oc_val, Y.Oc_rank1, h⟩

theorem nm_ext (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra Y.Kc K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ‖(p : K')‖ = (p : ℝ)⁻¹ ∧ (∀ x : Y.Kc, ‖algebraMap Y.Kc K' x‖ ≤ 1 ↔ x ∈ Y.Oc) ∧
      ∃ vp : K', vp ^ (p ^ 2 - 1) = (p : K') := by
  have hH := nm_hyp Y h
  have hc : 1 < nm_abs hH ((p : Y.Kc)⁻¹) := by
    rw [map_inv₀]
    show 1 < (nm_N Y.Oc p (p : Y.Kc))⁻¹
    rw [nm_N_p hH, inv_inv]
    exact nm_pR hH
  obtain ⟨K', i1, i2, hu, hac, hn⟩ :=
    nm_extG (nm_abs hH) (fun x y => nm_N_add hH x y) ((p : Y.Kc)⁻¹) hc
  refine ⟨K', i1, i2, hu, hac, ?_, ?_, ?_⟩
  · have := hn (p : Y.Kc)
    rw [map_natCast] at this
    exact this.trans (nm_N_p hH)
  · intro x
    rw [hn x]
    exact nm_N_le_one hH x
  · have h2 : 2 ≤ p := hp.out.two_le
    have hpos : 0 < p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    exact IsAlgClosed.exists_pow_nat_eq (p : K') hpos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_restNorm (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : ea_RestNorm Y := by
  obtain ⟨K', nf, ac, um, -, hpn, hball, vp, hvp⟩ := nm_ext Y h
  letI : Algebra (K0 p) K' := ((algebraMap Y.Kc K').comp (algebraMap (K0 p) Y.Kc)).toAlgebra
  haveI : IsScalarTower (K0 p) Y.Kc K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨ea_NormExt.mk K' vp hvp hpn hball⟩

theorem nm_restNorm_of_place (Y : Pend X) (v : X.Pl) : ea_RestNorm Y := nm_restNorm Y (nm_pinv_of_place Y v)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem ea_restSU (hG : RestGc p) : ea_RestSU X Y :=
  ea_restSU_of X Y (ea_restSExpV_of X (restBeta p) (th_restGcV_of X hG))

theorem first_theorem_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : EntryBoundOfHypotheses X Y D :=
  fun hA v j hj =>
    ea_A1U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem second_lemma_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : PlacewiseLowerBoundEvenShift X Y D :=
  fun hA v j hj =>
    ea_A2U D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brClass X) (ea_brNum X) hA v j hj

theorem hecke_place_bound (D : Formalism.BasicNotions.D7) (hG : RestGc p) (hJ : ea_BrJet X) : RestBU X Y D :=
  fun hA v j hj i hi =>
    ea_BU D Y (nm_restNorm_of_place Y v) (ea_restSU X Y hG) hJ (ea_brScale X) (ea_brClass X) (ea_brNum X) hA v j hj i hi

end Formalism.MainNotions.FormalGroupSystem.Pf
