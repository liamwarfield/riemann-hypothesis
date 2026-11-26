module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.RaChar

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RaCpaf
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RaTlog
open scoped Matrix TensorProduct
open Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

open Polynomial

def logPoly {O : Type} [CommRing O] (p : ℕ) (c : ℕ → O) : O[X] :=
  ∑ k ∈ Finset.Ico 1 p, C ((-1) ^ (k - 1) * c k) * X ^ k

lemma logPoly_deriv {O : Type} [CommRing O] (p : ℕ) (hp : 1 ≤ p) (c : ℕ → O)
    (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) :
    (1 + X) * derivative (logPoly p c) = 1 - (-X) ^ (p - 1) := by
  have h1 : derivative (logPoly p c) = ∑ i ∈ Finset.range (p - 1), (-X : O[X]) ^ i := by
    rw [logPoly, derivative_sum, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [derivative_C_mul_X_pow, mul_assoc, hc _ (by omega) (by omega), mul_one,
      show 1 + i - 1 = i by omega, neg_pow (X : O[X])]
    simp
  rw [h1, ← mul_neg_geom_sum, sub_neg_eq_add]

lemma logPoly_dvd {O : Type} [CommRing O] [IsDomain O] [CharZero O] (p : ℕ) (hp : 1 ≤ p)
    (c : ℕ → O) (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) (a : ℕ) :
    X ^ p ∣ (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c := by
  set P := (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c with hP
  set s : O[X] := (1 + X) ^ a - 1 with hs
  have hXs : X ∣ s := by
    have := sub_dvd_pow_sub_pow (1 + X : O[X]) 1 a
    simpa using this
  have hd := logPoly_deriv p hp c hc
  have hd2 : (1 + s) * (derivative (logPoly p c)).comp s = 1 - (-s) ^ (p - 1) := by
    have := congrArg (fun q => q.comp s) hd
    simpa using this
  have hds : (1 + X) * derivative s = C (a : O) * (1 + s) := by
    rw [hs]
    rcases a with _ | a
    · simp
    · simp only [derivative_sub, derivative_one, sub_zero, derivative_pow_succ, derivative_add,
        derivative_X, zero_add, mul_one, add_sub_cancel]
      push_cast
      ring
  have hP' : (1 + X) * derivative P = C (a : O) * ((-X) ^ (p - 1) - (-s) ^ (p - 1)) := by
    rw [hP, derivative_sub, derivative_comp, derivative_C_mul]
    linear_combination ((derivative (logPoly p c)).comp s) * hds + C (a : O) * hd2 - C (a : O) * hd
  have hdv : X ^ (p - 1) ∣ (1 + X) * derivative P := by
    rw [hP']
    exact Dvd.dvd.mul_left (dvd_sub (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) _)
      (pow_dvd_pow_of_dvd (dvd_neg.2 hXs) _)) _
  have hcop : IsCoprime (X ^ (p - 1) : O[X]) (1 + X) :=
    IsCoprime.pow_left ⟨-1, 1, by ring⟩
  have hdv2 := X_pow_dvd_iff.1 (hcop.dvd_of_dvd_mul_left hdv)
  refine X_pow_dvd_iff.2 fun d hdp => ?_
  rcases d with _ | d
  · have hL : X ∣ logPoly p c := by
      refine Finset.dvd_sum fun k hk => Dvd.dvd.mul_left (dvd_pow_self _ ?_) _
      have := (Finset.mem_Ico.1 hk).1
      omega
    refine X_dvd_iff.1 (dvd_sub ?_ (hL.mul_left _))
    obtain ⟨q, hq⟩ := hL
    rw [hq, mul_comp, X_comp]
    exact hXs.mul_right _
  · have := hdv2 d (by omega)
    rw [coeff_derivative] at this
    exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast Nat.succ_ne_zero d)

section Val

variable {K : Type} [Field K] (v : Valuation K NNReal)

lemma val_nat_le (k : ℕ) : v (k : K) ≤ 1 := (natCast_mem v.integer k : (k : K) ∈ v.integer)

lemma val_nat_eq (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) (k : ℕ) (h1 : 1 ≤ k) (h2 : k < p) :
    v (k : K) = 1 := by
  by_contra hne
  have hlt : v (k : K) < 1 := lt_of_le_of_ne (val_nat_le v k) hne
  have hc : Nat.Coprime p k := (Nat.coprime_of_lt_prime (by omega) h2 Fact.out)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have hab' : (a : K) * p + b * k = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have ha : v (a : K) ≤ 1 := (intCast_mem v.integer a : (a : K) ∈ v.integer)
  have hb : v (b : K) ≤ 1 := (intCast_mem v.integer b : (b : K) ∈ v.integer)
  have : v ((a : K) * p + b * k) < 1 := by
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ha zero_le hp
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hb zero_le hlt
  rw [hab', map_one] at this
  exact lt_irrefl _ this

lemma val_root (p : ℕ) (hp : p ≠ 0) {x : K} (hx : x ^ p = 1) : v x = 1 := by
  have : v x ^ p = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hp).1 this

lemma val_pow_sub_one {x : K} (hx : v x = 1) (k : ℕ) : v (x ^ k - 1) ≤ v (x - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ (k + 1) - 1 = x * (x ^ k - 1) + (x - 1) := by ring
    rw [this]
    refine v.map_add_le ?_ le_rfl
    rw [map_mul, hx, one_mul]; exact ih

lemma val_prim (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := congrArg v hζ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  push_cast
  rw [← h, Finset.prod_congr rfl (g := fun _ => v (ζ - 1))]
  · simp
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have hc : Nat.Coprime (k + 1) (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
  have h2 := hζ.pow_of_coprime _ hc
  rw [v.map_sub_swap]
  refine le_antisymm (val_pow_sub_one v (val_root v _ hp.ne_zero hζ.pow_eq_one) _) ?_
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one hζ.pow_eq_one
  conv_lhs => rw [← hi]
  exact val_pow_sub_one v (val_root v _ hp.ne_zero h2.pow_eq_one) _

def tl (p : ℕ) (x : K) : K := ∑ k ∈ Finset.Ico 1 p, (-1) ^ (k - 1) * (x - 1) ^ k / (k : K)

lemma tl_one (p : ℕ) : tl p (1 : K) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have := (Finset.mem_Ico.1 hk).1
  rw [sub_self, zero_pow (by omega)]; simp

lemma val_tl_pow [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x : K} (hx : v x = 1)
    (a : ℕ) : v (tl p (x ^ a) - tl p x * a) ≤ v (x - 1) ^ p := by
  classical
  let c : ℕ → v.integer := fun k => if h : v (k : K) = 1 then ⟨(k : K)⁻¹, by
    rw [Valuation.mem_integer_iff, map_inv₀, h, inv_one]⟩ else 0
  have hc' : ∀ k, 1 ≤ k → k < p → (c k : K) = (k : K)⁻¹ := by
    intro k h1 h2
    simp only [c, dif_pos (val_nat_eq v p hp k h1 h2)]
  have hc : ∀ k, 1 ≤ k → k < p → c k * k = 1 := by
    intro k h1 h2
    ext
    have : (k : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast
    rw [hc' k h1 h2, inv_mul_cancel₀ this]
  have hev : ∀ t : v.integer, (((logPoly p c).eval t : v.integer) : K) = tl p (1 + (t : K)) := by
    intro t
    rw [logPoly, eval_finsetSum, tl]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    rw [hc' k h1 h2, add_sub_cancel_left]; ring
  obtain ⟨q, hq⟩ := logPoly_dvd p (Fact.out : p.Prime).one_le c hc a
  have hx1 : x - 1 ∈ v.integer := by
    apply sub_mem _ (one_mem _)
    rw [Valuation.mem_integer_iff, hx]
  let t : v.integer := ⟨x - 1, hx1⟩
  have h := congrArg (fun r : v.integer[X] => ((r.eval t : v.integer) : K)) hq
  simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h
  push_cast at h
  rw [hev, hev] at h
  push_cast at h
  have ht : (t : K) = x - 1 := rfl
  rw [ht, add_sub_cancel, add_sub_cancel, mul_comm (a : K)] at h
  rw [h, map_mul, map_pow]
  exact mul_le_of_le_one_right zero_le (q.eval t).2

lemma val_prim_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) < 1 := by
  by_contra h
  have := one_le_pow₀ (n := p - 1) (not_lt.1 h)
  rw [val_prim v p hζ] at this
  exact absurd hp (not_lt.2 this)

lemma val_prim_pos (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : 0 < v (ζ - 1) :=
  (v.pos_iff).2 (sub_ne_zero.2 (hζ.ne_one (Fact.out : p.Prime).one_lt))

lemma val_prim_pow_le (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ p ≤ v (p : K) := by
  rw [← val_prim v p hζ]
  exact pow_le_pow_of_le_one zero_le (val_prim_lt v p hp hζ).le (Nat.sub_le _ _)

lemma val_prim_pow_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (hk : 1 < k) : v (ζ - 1) ^ k < v (ζ - 1) :=
  pow_lt_self_of_lt_one₀ (val_prim_pos v p hζ) (val_prim_lt v p hp hζ) hk

lemma val_tl_prim (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (tl p ζ) = v (ζ - 1) := by
  rw [tl, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : p.Prime).one_lt]
  simp only [Nat.sub_self, pow_zero, pow_one, one_mul, Nat.cast_one, div_one]
  refine v.map_add_eq_of_lt_left (v.map_sum_lt (val_prim_pos v p hζ).ne' fun k hk => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  rw [map_div₀, val_nat_eq v p hp k (by omega) h2, div_one, map_mul, map_pow, map_pow,
    Valuation.map_neg, map_one, one_pow, one_mul]
  exact val_prim_pow_lt v p hp hζ k (by omega)

lemma val_tl_add [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x y : K}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : v (tl p (x * y) - tl p x - tl p y) ≤ v (p : K) := by
  have hpp : p.Prime := Fact.out
  by_cases h1 : x = 1
  · simp [h1, tl_one]
  have hζ : IsPrimitiveRoot x p := by
    have := orderOf_eq_prime hx h1
    rw [← this]; exact IsPrimitiveRoot.orderOf x
  have : NeZero p := ⟨hpp.ne_zero⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  have hv := val_root v p hpp.ne_zero hx
  have : tl p (x * x ^ b) - tl p x - tl p (x ^ b) =
      (tl p (x ^ (b + 1)) - tl p x * (b + 1 : ℕ)) - (tl p (x ^ b) - tl p x * b) := by
    rw [pow_succ']; push_cast; ring
  rw [this]
  exact (v.map_sub_le (val_tl_pow v p hp hv _) (val_tl_pow v p hp hv _)).trans
    (val_prim_pow_le v p hp hζ)

end Val

end PositivityTheory.HtPt.Ra
end
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma mem_pInt_iff [CharZero C] (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (z : C) :
    z ∈ pInt (C := C) R p ↔ v z ≤ v (p : C) := by
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
  · intro h
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := z / p)
      (by rw [map_div₀]; exact div_le_one_of_le₀ h zero_le)
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ hp0]⟩

lemma pow_mem_order {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) (k : ℕ) :
    f ^ k ∈ A.carrier := by
  induction k with
  | zero => simpa using A.one_mem
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hf

lemma tl_mem_order (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (hp : v (p : C) < 1)
    {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) :
    (fun x => tl p (f x)) ∈ A.carrier := by
  have : (fun x => tl p (f x)) =
      ∑ k ∈ Finset.Ico 1 p, fun x => (-1) ^ (k - 1) * (f x - 1) ^ k / (k : C) := by
    funext x; rw [Finset.sum_apply]; rfl
  rw [this]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := (-1) ^ (k - 1) / (k : C)) (by
    rw [map_div₀, val_nat_eq v p hp k h1 h2, map_pow, Valuation.map_neg, map_one, one_pow, div_one])
  have h3 := A.carrier.smul_mem r (pow_mem_order A (A.carrier.sub_mem hf A.one_mem) k)
  convert h3 using 1
  funext x
  simp only [Pi.smul_apply, Algebra.smul_def, Pi.pow_apply, Pi.sub_apply, Pi.one_apply, hr]
  ring

end

theorem cpaf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ μ : N →+ ZMod p, ∃ g ∈ afFun p AA.carrier, ∃ ε : R, v (algebraMap R C ε) ^ (p - 1) = v (p : C) ∧ g 0 = 0 ∧ ∀ x, g x - algebraMap R C ε * ((μ x).val : C) ∈ pInt (C := C) R p ∧ v (g x - algebraMap R C ε * ((μ x).val : C)) < v (algebraMap R C ε) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ AA μ
  have hpp : p.Prime := Fact.out
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hpp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  let ψ : AddChar N C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom μ
  have hψ : ∀ x, ψ x = ζ ^ (μ x).val := fun x => rfl
  have hψp : ∀ x, ψ x ^ p = 1 := fun x => by
    rw [hψ, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζ1 := val_root v p hpp.ne_zero hζ.pow_eq_one
  have hε := val_tl_prim v p hp hζ
  obtain ⟨ε, hεe⟩ := hv.exists_of_le_one (r := tl p ζ) (hε.le.trans (val_prim_lt v p hp hζ).le)
  refine ⟨fun x => tl p (ψ x), ⟨tl_mem_order hv p hp AA (charmem p C v R hv hp N AA ψ), ?_⟩,
    ε, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · intro x y
    rw [mem_pInt_iff hv]
    simp only [AddChar.map_add_eq_mul]
    exact val_tl_add v p hp (hψp x) (hψp y)
  · rw [hεe, hε, val_prim v p hζ]
  · simp only [AddChar.map_zero_eq_one, tl_one]
  · rw [mem_pInt_iff hv, hεe]
    exact (val_tl_pow v p hp hζ1 _).trans (val_prim_pow_le v p hp hζ)
  · rw [hεe, hε]
    exact (val_tl_pow v p hp hζ1 _).trans_lt (val_prim_pow_lt v p hp hζ p hpp.one_lt)

lemma form_add {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] (p : ℕ) [Fact p.Prime]
    {ι : Type} [Fintype ι] (l : ι → R) (x y : ι → ZMod p) :
    algebraMap R C (∑ i, l i * (((x + y) i).val : R)) - algebraMap R C (∑ i, l i * ((x i).val : R))
      - algebraMap R C (∑ i, l i * ((y i).val : R)) ∈ pInt (C := C) R p := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h := Nat.mod_add_div ((x i).val + (y i).val) p
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → C) h
  rw [pInt, Submodule.mem_span_singleton]
  refine ⟨-(l i * ((((x i).val + (y i).val) / p : ℕ) : R)), ?_⟩
  simp only [Algebra.smul_def, map_neg, map_mul, map_natCast, Pi.add_apply]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h'
  linear_combination (-algebraMap R C (l i)) * h'

theorem lifts : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ (l : ι → R) (ε : R), ε • l ∈ afLat p AA.carrier → v (p : C) ≤ v (algebraMap R C ε) ^ (p - 1) → ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧ (∀ x, v (u x) ≤ 1) ∧ ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA l ε hl hε
  have hpp : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
  have hp0 : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
  have hε0 : v (algebraMap R C ε) ≠ 0 := by
    intro h
    rw [h, zero_pow hp1] at hε
    exact hp0 (le_antisymm hε zero_le)
  have hε0' : algebraMap R C ε ≠ 0 := (Valuation.ne_zero_iff v).1 hε0
  suffices h : ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧
      ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 by
    obtain ⟨u, h1, h2⟩ := h
    refine ⟨u, h1, fun x => ?_, h2⟩
    rw [← sub_add_cancel (u x) (algebraMap R C (∑ i, l i * ((x i).val : R)))]
    exact v.map_add_le (h2 x).le (hv.map_le_one _)
  rcases lt_or_ge (v (p : C)) (v (algebraMap R C ε)) with hlt | hge
  · obtain ⟨g, hg, h⟩ := hl
    refine ⟨fun x => g x / algebraMap R C ε, ?_, fun x => ?_⟩
    · simp only [mul_div_cancel₀ _ hε0']
      refine ⟨hg, fun x y => ?_⟩
      have := Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (h (x + y)) (h x)) (h y))
        (form_add (C := C) p (ε • l) x y)
      convert this using 1
      ring
    · have h1 := (mem_pInt_iff hv p _).1 (h x)
      have h2 : g x / algebraMap R C ε - algebraMap R C (∑ i, l i * ((x i).val : R)) =
          (g x - algebraMap R C (∑ i, (ε • l) i * ((x i).val : R))) / algebraMap R C ε := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, map_mul]
        field_simp
      rw [h2, map_div₀, div_lt_one₀ (pos_iff_ne_zero.2 hε0)]
      exact h1.trans_lt hlt
  · have hc := fun i => cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    choose g hg e he _ hge' using hc
    have hee : ∀ i, v (algebraMap R C ε) ≤ v (algebraMap R C (e i)) := by
      intro i
      refine hge.trans ?_
      rw [← he i]
      exact pow_le_of_le_one zero_le (hv.map_le_one _) hp1
    have he0 : ∀ i, v (algebraMap R C (e i)) ≠ 0 := fun i h =>
      hε0 (le_antisymm (h ▸ hee i) zero_le)
    have he0' : ∀ i, algebraMap R C (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff v).1 (he0 i)
    choose r hr using fun i => hv.dvd_of_le (hee i)
    refine ⟨fun x => ∑ i, algebraMap R C (l i) * (g i x / algebraMap R C (e i)), ?_, fun x => ?_⟩
    · have := Submodule.sum_mem (afFun p AA.carrier) (t := Finset.univ)
        fun i _ => Submodule.smul_mem _ (l i * r i) (hg i)
      convert this using 1
      funext x
      rw [Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h0 := he0' i
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      conv_lhs => rw [hr i, map_mul]
      field_simp
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine v.map_sum_lt one_ne_zero fun i _ => ?_
      have h0 := he0' i
      have h2 : algebraMap R C (l i) * (g i x / algebraMap R C (e i)) -
          algebraMap R C (l i * ((x i).val : R)) = algebraMap R C (l i) *
          ((g i x - algebraMap R C (e i) * ((x i).val : C)) / algebraMap R C (e i)) := by
        rw [map_mul, map_natCast]
        field_simp
      rw [h2, map_mul, map_div₀]
      refine mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le ?_
      rw [div_lt_one₀ (pos_iff_ne_zero.2 (he0 i))]
      exact (hge' i x).2

end PositivityTheory.HtPt.Ra
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RaSmith
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section lattice

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem exists_smith_basis (hv : v.Integers R) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : Submodule R (ι → R)) (hL : L.FG) :
    ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧
      L = Submodule.span R (Set.range fun j => ε j • Λ j) := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A : Matrix (Fin (Fintype.card ι)) (Fin m) R := Matrix.of fun i k => g k (e.symm i)
  obtain ⟨P, Q, a, hP, hQ, hD⟩ :=
    ReciprocityTheory.PGsh.Up.Smith.smith_mat (v := v) hv (Fintype.card ι) m A
  have hPv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hP
  have hQv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hAQ : A * Q = P⁻¹ * (P * A * Q) := by
    simp only [← Matrix.mul_assoc, hPv, Matrix.one_mul]
  have hA : A = P⁻¹ * (P * A * Q) * Q⁻¹ := by
    rw [← hAQ, Matrix.mul_assoc, hQv, Matrix.mul_one]
  let Λ : Matrix ι ι R := Matrix.of fun j i => P⁻¹ (e i) (e j)
  let ε : ι → R := fun j => if (e j : ℕ) < m then a (e j) else 0
  have hΛ : Λ = ((P⁻¹).submatrix e e)ᵀ := by
    ext j i; rfl
  have hdet : IsUnit Λ.det := by
    rw [hΛ, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 hP
  refine ⟨Λ, ε, hdet, le_antisymm ?_ ?_⟩
  · rw [← hg, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have hgl : g l = ∑ k : Fin m, ∑ j : Fin (Fintype.card ι),
        (Q⁻¹ k l * (P * A * Q) j k) • Λ (e.symm j) := by
      ext i
      have h1 : A (e i) l = (P⁻¹ * (P * A * Q) * Q⁻¹) (e i) l := by rw [← hA]
      have h2 : A (e i) l = g l i := by simp [A]
      rw [← h2, h1, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply (M := P⁻¹)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Λ, Matrix.of_apply, Equiv.apply_symm_apply]
      ring
    rw [SetLike.mem_coe, hgl]
    refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => ?_
    rw [hD j k]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : ((e (e.symm j)) : ℕ) < m := by
        rw [Equiv.apply_symm_apply, ← hkj]; exact k.2
      have hε : ε (e.symm j) = a j := by
        simp only [ε, if_pos hj, Equiv.apply_symm_apply]
      rw [if_pos hkj, mul_smul, ← hε]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.symm j, rfl⟩)
    · rw [if_neg hkj, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ε j • Λ j ∈ L
    by_cases hj : (e j : ℕ) < m
    · have hsum : ε j • Λ j = ∑ l : Fin m, Q l ⟨e j, hj⟩ • g l := by
        ext i
        have h1 : (A * Q) (e i) ⟨e j, hj⟩ = (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ := by rw [← hAQ]
        have h2 : (A * Q) (e i) ⟨e j, hj⟩ = ∑ l, Q l ⟨e j, hj⟩ * g l i := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [A, mul_comm]
        have h3 : (P⁻¹ * (P * A * Q)) (e i) ⟨e j, hj⟩ = a (e j) * P⁻¹ (e i) (e j) := by
          rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
          · rw [hD]; simp [mul_comm]
          · intro b _ hb
            rw [hD, if_neg, mul_zero]
            intro h
            exact hb (Fin.ext h.symm)
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← h2, h1, h3]
        simp only [ε, if_pos hj, Λ, Matrix.of_apply]
      rw [hsum, ← hg]
      exact Submodule.sum_mem _ fun l _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · have : ε j = 0 := if_neg hj
      rw [this, zero_smul]
      exact Submodule.zero_mem _

noncomputable def rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (h : IsUnit Λ.det) :
    (ι → R) ≃ₗ[R] (ι → R) :=
  LinearEquiv.ofLinear (Matrix.vecMulLinear Λ) (Matrix.vecMulLinear Λ⁻¹)
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ h])
    (LinearMap.ext fun x => by
      simp [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ h])

theorem rowEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (x : ι → R) : rowEquiv Λ h x = ∑ j, x j • Λ j := by
  show x ᵥ* Λ = _
  rw [Matrix.vecMul_eq_sum]

theorem map_rowEquiv {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) :
    (Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)).map
        (rowEquiv Λ h : (ι → R) →ₗ[R] (ι → R)) =
      Submodule.span R (Set.range fun j => ε j • Λ j) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    rw [Submodule.mem_comap]
    show rowEquiv Λ h x ∈ _
    rw [rowEquiv_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hx j (Set.mem_univ j))
    rw [← hr, mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j (ε j), ?_, ?_⟩
    · intro k _
      by_cases hk : k = j
      · subst hk
        simpa using Ideal.mem_span_singleton_self (ε k)
      · simp [Pi.single_eq_of_ne hk]
    · show rowEquiv Λ h _ = _
      rw [rowEquiv_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ _) hj

theorem dvd_of_smul_row_mem {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) (c : R) (j : ι)
    (hc : c • Λ j ∈ Submodule.span R (Set.range fun j => ε j • Λ j)) : ε j ∣ c := by
  rw [← map_rowEquiv Λ h ε] at hc
  obtain ⟨x, hx, hxe⟩ := hc
  have hx' : x = Pi.single j c := by
    apply (rowEquiv Λ h).injective
    have : rowEquiv Λ h x = c • Λ j := hxe
    rw [this, rowEquiv_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ _) hj
  have := hx j (Set.mem_univ j)
  rw [hx', Pi.single_eq_same] at this
  exact Ideal.mem_span_singleton.1 this

theorem hasLen_quot_rows {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R)
    (h : IsUnit Λ.det) (ε : ι → R) {M : Type} [AddCommGroup M] [Module R M]
    (E : M ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j))) :
    HasLen v R M (∏ j, v (algebraMap R C (ε j))) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let T : Submodule R (ι → R) := Submodule.pi Set.univ fun j => (Ideal.span {ε j} : Submodule R R)
  have E1 : ((ι → R) ⧸ T) ≃ₗ[R] ((ι → R) ⧸ Submodule.span R (Set.range fun j => ε j • Λ j)) :=
    Submodule.Quotient.equiv T _ (rowEquiv Λ h) (map_rowEquiv Λ h ε)
  have E2 : ((ι → R) ⧸ T) ≃ₗ[R] ((j : ι) → R ⧸ Ideal.span {ε j}) :=
    Submodule.quotientPi fun j => (Ideal.span {ε j} : Submodule R R)
  have E3 := LinearEquiv.piCongrLeft R (fun j : ι => R ⧸ Ideal.span {ε j}) e.symm
  refine ⟨Fintype.card ι, fun i => ε (e.symm i), ⟨((E.trans E1.symm).trans E2).trans E3.symm⟩, ?_⟩
  exact Equiv.prod_comp e.symm fun j => v (algebraMap R C (ε j))

end lattice

theorem smith_of (hfg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), (afLat p AA.carrier).FG)
    (hquot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA
  have hp1 : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le
    omega
  obtain ⟨-, -, cp, hcp, -, -⟩ := cpaf p C v R hv hp (ι → ZMod p) AA 0
  have hcoord : ∀ i, (Pi.single i cp : ι → R) ∈ afLat p AA.carrier := by
    intro i
    obtain ⟨g, hg, c, hc, -, h⟩ :=
      cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    have hvc : v (algebraMap R C cp) = v (algebraMap R C c) :=
      (pow_left_inj₀ zero_le zero_le hp1).1 (hcp.trans hc.symm)
    obtain ⟨u, hu⟩ : c ∣ cp := hv.dvd_of_le hvc.le
    have hmem : (Pi.single i c : ι → R) ∈ afLat p AA.carrier := by
      refine ⟨g, (Submodule.mem_inf.1 hg).1, fun x => ?_⟩
      have hs : ∑ k, (Pi.single i c : ι → R) k * ((x k).val : R) = c * ((x i).val : R) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro hi; exact absurd (Finset.mem_univ _) hi
      rw [hs, map_mul, map_natCast]
      exact (h x).1
    have : (Pi.single i cp : ι → R) = u • (Pi.single i c : ι → R) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp [hu, mul_comm]
      · simp [Pi.single_eq_of_ne hk]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  have hscale : ∀ l : ι → R, cp • l ∈ afLat p AA.carrier := by
    intro l
    have : cp • l = ∑ i, l i • (Pi.single i cp : ι → R) := by
      ext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hcoord i)
  obtain ⟨Λ, ε, hdet, hL⟩ := exists_smith_basis hv _ (hfg p C v R hv hp ι AA)
  refine ⟨Λ, ε, hdet, hL, fun j => ?_, ?_⟩
  · have hd : ε j ∣ cp := dvd_of_smul_row_mem Λ hdet ε cp j (hL ▸ hscale (Λ j))
    obtain ⟨t, ht⟩ := hd
    have hle : v (algebraMap R C cp) ≤ v (algebraMap R C (ε j)) := by
      rw [ht, map_mul, map_mul]
      exact mul_le_of_le_one_right' (hv.map_le_one t)
    rw [← hcp]
    exact pow_le_pow_left₀ zero_le hle _
  · obtain ⟨E⟩ := hquot p C v R hv hp ι AA
    exact hasLen_quot_rows Λ hdet ε (E.trans (Submodule.quotEquivOfEq _ _ hL))

end PositivityTheory.HtPt.Ra
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RaCoord
noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section Count

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma monomialCount_col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R)
    (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have h : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

lemma monomialCount_exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨fun i α => c α i, ?_⟩
  ext x α
  have := congrFun (hc α) x
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  rw [← this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma monomialCount_prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

end Count

lemma monomialCount_exponent (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → NNReal) :
    (∏ j, a j) ^ (Fintype.card (ι → ZMod p) * (p - 1)) =
      (∏ j, a j ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) :=
    Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (Fintype.card ι - 1) * p = p ^ Fintype.card ι := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  have hcard : Fintype.card (ι → ZMod p) = p ^ Fintype.card ι := by
    simp [ZMod.card]
  rw [Finset.prod_pow, ← pow_mul, hcard]
  congr 1
  calc p ^ Fintype.card ι * (p - 1) = p ^ (Fintype.card ι - 1) * p * (p - 1) := by rw [h3]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1)) := by ring
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2 * 2) := by rw [h2]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) * 2 := by ring

theorem cnt_coord_of (hsmith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j)))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) := by
  intro p _ C _ _ _ v R _ _ hv hp1 ι _ _ AA cA cN hA hN
  obtain ⟨Λ, ε, hΛ, hspan, hε, hlen⟩ := hsmith p C v R hv hp1 ι AA
  have hcA : cA = ∏ j, v (algebraMap R C (ε j)) := hasLen_unique hv hA hlen
  have hl := fun j => lifts p C v R hv hp1 ι AA (Λ j) (ε j)
    (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)
  choose u hu_mem hu_int hu_cong using hl

  let B' : Matrix (ι → ZMod p) (ι → ZMod p) C := Matrix.of fun (x α : ι → ZMod p) =>
    ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^
      (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 ι Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)
  have hsq : cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = v B'.det ^ 2 := by
    rw [hcA, hB'v]
    exact monomialCount_exponent p _

  have hp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0 := by
    intro j h0
    have hpp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    have := hε j
    rw [h0, zero_pow hpp] at this
    exact hp0 (le_antisymm this zero_le)
  have hB'0 : v B'.det ≠ 0 := by
    rw [hB'v]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)

  have hmem : ∀ α : ι → ZMod p, (fun x => B' x α) ∈ AA.carrier := by
    intro α
    exact monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y)
      (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)
  obtain ⟨B, hAA, hBc⟩ := hN
  obtain ⟨W, hW⟩ := monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = cN * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]; rfl
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hle : v B'.det ≤ cN := by
    rw [hdet]; exact mul_le_of_le_one_right zero_le hw1
  refine ⟨by rw [hsq]; exact pow_le_pow_left₀ zero_le hle 2, fun heq => ?_⟩
  have hBeq : v B'.det = cN := by
    rw [hsq] at heq
    exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq
  have hcN0 : cN ≠ 0 := hBeq ▸ hB'0
  have hw : v (algebraMap R C W.det) = 1 := by
    have h : cN * v (algebraMap R C W.det) = cN * 1 := by rw [← hdet, hBeq, mul_one]
    exact mul_left_cancel₀ hcN0 h
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq' : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine ⟨fun j y => algebraMap R C (ε j) * u j y, hu_mem, ?_⟩
  have hspan' : Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) =>
      ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan']
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := monomialCount_col_mem_span (R := R) B' (W⁻¹) j
    rwa [hBeq'] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end PositivityTheory.HtPt.Ra
end
end

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem smith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) :=
  smith_of PositivityTheory.HtPt.Rh.aflat_fg PositivityTheory.HtPt.Rh.afquot

theorem cnt_coord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) :=
  cnt_coord_of smith

theorem cnt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) :=
  cnt_of cnt_coord

end PositivityTheory.HtPt.Ra
