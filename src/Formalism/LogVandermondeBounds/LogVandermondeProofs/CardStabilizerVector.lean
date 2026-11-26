module

public import Formalism.LogVandermondeBounds.MultinomialPowerBound

@[expose] public section

section -- merged from Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

lemma half_add_half (n : ℕ) : n * (n - 1) / 2 + n * (n + 1) / 2 = n * n := by
  rcases n with _ | k
  · simp
  · obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    have h1 : (k + 1) * k = m + m := by rw [mul_comm]; exact hm
    have h2 : (k + 1) * (k + 1 + 1) = m + m + 2 * (k + 1) := by rw [← h1]; ring
    have h3 : (k + 1) * (k + 1) = m + m + (k + 1) := by rw [← h1]; ring
    rw [Nat.add_sub_cancel, h1, h2, h3]
    omega

lemma factor_eq (q : ℝ) (hq : q ≠ 0) (n i : ℕ) (hi : i ≤ n) :
    q ^ n - q ^ i = q ^ n * (1 - q⁻¹ ^ (n - i)) := by
  have h : q ^ n * q⁻¹ ^ (n - i) = q ^ i := by
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hq), ← pow_add, Nat.add_sub_of_le hi]
  rw [mul_sub, mul_one, h]

theorem cardGeneralLinear : CardGeneralLinear := by
  intro F _ _ _ n
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnat : Fintype.card (GL (Fin n) F) =
      ∏ i ∈ range n, (Fintype.card F ^ n - Fintype.card F ^ i) := by
    rw [Finset.prod_range, Fintype.card_eq_nat_card (α := GL (Fin n) F)]
    exact Matrix.card_GL_field n
  have hreal : (Fintype.card (GL (Fin n) F) : ℝ) =
      ∏ i ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i) := by
    rw [hnat, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Nat.cast_sub (Nat.pow_le_pow_right hpos (mem_range.mp hi).le), Nat.cast_pow, Nat.cast_pow]
  rw [hreal, ← pow_add, half_add_half]
  have hpow : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i ∈ range n, (Fintype.card F : ℝ) ^ n := by
    rw [prod_const, card_range, ← pow_mul]
  have hrefl : ∏ j ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ (n - 1 - j)) =
      ∏ j ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ j) :=
    prod_range_reflect (fun i => (Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i) n
  rw [hpow, ← prod_mul_distrib, ← hrefl]
  refine prod_congr rfl (fun i hi => ?_)
  have hi' := mem_range.mp hi
  rw [factor_eq _ hq0 n (n - 1 - i) (by omega), show n - (n - 1 - i) = i + 1 by omega]

def upperEquiv (F : Type) [Field F] (n : ℕ) :
    {A : Matrix (Fin n) (Fin n) F // (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1} ≃
      ({p : Fin n × Fin n // p.1 < p.2} → F) where
  toFun A p := A.1 p.1.1 p.1.2
  invFun f := ⟨fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · simp [not_lt.mpr hji.le, hji.ne']
    · simp⟩
  left_inv A := by
    apply Subtype.ext
    funext i j
    simp only
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (A.2.2 i).symm
    · exact (A.2.1 i j (lt_of_le_of_ne (not_lt.mp h1) (fun h => h2 h.symm))).symm
  right_inv f := by
    funext p
    simp [p.2]

lemma card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have hs : (univ.filter (fun i : Fin n => i < j)) = Finset.Iio j := by ext i; simp
    rw [hs, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

theorem cardUnitriangular : CardUnitriangular := by
  intro F _ _ _ n
  rw [Nat.card_congr (upperEquiv F n)]
  rw [Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

def RowVec (F : Type) (n : ℕ) : Type := Fin n → F

instance rowAction (F : Type) [Field F] (n : ℕ) : MulAction (GL (Fin n) F) (RowVec F n) where
  smul g v := Matrix.vecMul (v : Fin n → F) ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  one_smul v := by
    show Matrix.vecMul (v : Fin n → F)
      (((1 : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v
    rw [inv_one, Units.val_one]
    exact Matrix.vecMul_one _
  mul_smul g h v := by
    show Matrix.vecMul (v : Fin n → F) (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.vecMul (Matrix.vecMul (v : Fin n → F) ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [mul_inv_rev, Units.val_mul]
    exact (Matrix.vecMul_vecMul (v : Fin n → F) _ _).symm

lemma vecMul_inv_eq_iff {F : Type} [Field F] {n : ℕ} (v : Fin n → F) (A : GL (Fin n) F) :
    Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v ↔
      Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v := by
  constructor
  · intro h
    calc Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F)
        = Matrix.vecMul (Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
            (A : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  · intro h
    calc Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = Matrix.vecMul (Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F))
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

private theorem vecMul_one_add_vecMulVec_single {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (c z : Fin n → F) :
    Matrix.vecMul z (1 + Matrix.vecMulVec (Pi.single k 1) c) = z + z k • c := by
  rw [Matrix.vecMul_add, Matrix.vecMul_one]
  congr 1
  funext j
  simp [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply]

private theorem single_one_vecMul_apply {F : Type} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    Matrix.vecMul (Pi.single i 1) M j = M i j := by
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

private theorem one_add_vecMulVec_single_mul_inverse_eq_one {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (x y : Fin n → F) (hx : x k ≠ 0) (hy : y k ≠ 0) :
    (1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) *
      (1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y))) = 1 := by
  have key : ∀ z : Fin n → F, Matrix.vecMul z
      ((1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) *
        (1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y)))) = z := by
    intro z
    rw [← Matrix.vecMul_vecMul, vecMul_one_add_vecMulVec_single,
      vecMul_one_add_vecMulVec_single]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  ext i j
  have h1 := congrFun (key (Pi.single i 1)) j
  rw [single_one_vecMul_apply] at h1
  rw [h1]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem exists_GL_vecMul_eq_of_ne_zero_at {F : Type} [Field F] {n : ℕ} (k : Fin n)
    (x y : Fin n → F) (hx : x k ≠ 0) (hy : y k ≠ 0) :
    ∃ A : GL (Fin n) F, Matrix.vecMul x (A : Matrix (Fin n) (Fin n) F) = y := by
  refine ⟨(⟨1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x)),
    1 + Matrix.vecMulVec (Pi.single k 1) ((y k)⁻¹ • (x - y)),
    one_add_vecMulVec_single_mul_inverse_eq_one k x y hx hy,
    one_add_vecMulVec_single_mul_inverse_eq_one k y x hy hx⟩ : (Matrix (Fin n) (Fin n) F)ˣ), ?_⟩
  show Matrix.vecMul x (1 + Matrix.vecMulVec (Pi.single k 1) ((x k)⁻¹ • (y - x))) = y
  rw [vecMul_one_add_vecMulVec_single]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [mul_inv_cancel_left₀ hx]
  ring

lemma exists_row {F : Type} [Field F] [Fintype F] {n : ℕ} (v w : Fin n → F) (hv : v ≠ 0)
    (hw : w ≠ 0) : ∃ A : GL (Fin n) F, Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = w := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    exact hv (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨l, hl⟩ : ∃ l, w l ≠ 0 := by
    by_contra h
    exact hw (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
  obtain ⟨A, hA⟩ := exists_GL_vecMul_eq_of_ne_zero_at k v (fun _ : Fin n => (1 : F)) hk one_ne_zero
  obtain ⟨B, hB⟩ := exists_GL_vecMul_eq_of_ne_zero_at l (fun _ : Fin n => (1 : F)) w one_ne_zero hl
  refine ⟨A * B, ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, hA, hB]

theorem cardStabilizerVector : CardStabilizerVector := by
  intro F _ _ _ n v hv
  have hcardne : Fintype.card {w : Fin n → F // w ≠ 0} = Fintype.card F ^ n - 1 := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : Fin n → F))
    rw [Fintype.card_option, Fintype.card_fun, Fintype.card_fin] at h
    omega
  have horbit : Nat.card (@MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v) =
      Fintype.card F ^ n - 1 := by
    have e : @MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v ≃ {w : Fin n → F // w ≠ 0} :=
      Equiv.subtypeEquivRight (fun w => by
        refine MulAction.mem_orbit_iff.trans ?_
        constructor
        · rintro ⟨g, rfl⟩ h0
          apply hv
          have h1 : Matrix.vecMul (Matrix.vecMul v ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
              (g : Matrix (Fin n) (Fin n) F) = v := by
            rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
          have h0' : Matrix.vecMul v ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0 := h0
          rw [← h1, h0', Matrix.zero_vecMul]
        · intro hw0
          obtain ⟨A, hA⟩ := exists_row v w hv hw0
          refine ⟨A⁻¹, ?_⟩
          show Matrix.vecMul v (((A⁻¹)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = w
          rw [inv_inv, hA])
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, hcardne]
  have hstab : Fintype.card {A : GL (Fin n) F // Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v} =
      Nat.card (@MulAction.stabilizer (GL (Fin n) F) (RowVec F n) _ _ v) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun A => by
      exact (vecMul_inv_eq_iff v A).symm))
  have hos : Nat.card (@MulAction.stabilizer (GL (Fin n) F) (RowVec F n) _ _ v) *
      Nat.card (@MulAction.orbit (GL (Fin n) F) (RowVec F n) _ v) = Nat.card (GL (Fin n) F) := by
    rw [mul_comm, ← Nat.card_prod]; exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ _)
  rw [hstab, ← horbit, hos, Nat.card_eq_fintype_card]

end Formalism.LogVandermondeBounds.StandardLattice
end

section -- merged from Formalism.LogVandermondeBounds.LogVandermondeProofs.BlockDimensionIdentities
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

theorem eulerProductBounds : EulerProductBounds := by
  intro q hq n
  set x := q⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr (by linarith)
  have hxq : x * q = 1 := inv_mul_cancel₀ (by linarith)
  have hx3 : x ≤ 1 / 3 := by nlinarith
  have hx1 : x ≤ 1 := by linarith
  have key : ∀ n : ℕ, 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc]
      set y := x ^ (n + 1) with hy
      have hy0 : 0 ≤ y := pow_nonneg hx0.le _
      have hyx : y ≤ x := pow_le_of_le_one hx0.le hx1 (by omega)
      have hc : 0 ≤ 1 - y := by have : y ≤ 1 := pow_le_one₀ hx0.le hx1; linarith
      have h1 := mul_le_mul_of_nonneg_right ih hc
      have h2 : y * y ≤ y * x := mul_le_mul_of_nonneg_left hyx hy0
      have e : x ^ (n + 1 + 1) = y * x := by rw [hy, pow_succ]
      rw [e]
      nlinarith
  have hfac : ∀ i ∈ range n, 0 ≤ 1 - x ^ (i + 1) ∧ 1 - x ^ (i + 1) ≤ 1 := by
    intro i _
    exact ⟨by have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1; linarith,
      by have : 0 ≤ x ^ (i + 1) := pow_nonneg hx0.le _; linarith⟩
  refine ⟨?_, Finset.prod_le_one₀ (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)⟩
  by_contra hlt
  push_neg at hlt
  have h1 : (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) < (1 - x) * (1 / 2) :=
    mul_lt_mul_of_pos_left hlt (by linarith)
  have := key n
  have := pow_pos hx0 (n + 1)
  linarith

end Formalism.LogVandermondeBounds.StandardLattice
end

section -- merged from Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Core

variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]

def eps (a h : H) : K := if h = a then 1 else if h = 1 then -1 else 0

def bas (a : ι → {c : H // c ≠ 1}) (h : ι → H) : K := ∏ w, (eps ((a w : H)) (h w) : K)

omit [Fintype H] in
lemma mulSingle_mul_apply_ne (v w : ι) (c : H) (h : ι → H) (hw : w ≠ v) :
    ((Pi.mulSingle v c : ι → H) * h) w = h w := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, _root_.one_mul]

omit [Fintype H] in
lemma mulSingle_mul_apply_self (v : ι) (c : H) (h : ι → H) :
    ((Pi.mulSingle v c : ι → H) * h) v = c * h v := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same]

lemma sum_eps (a t : H) (ha : a ≠ 1) : ∑ c : H, (eps a (c * t) : K) = 0 := by
  have key : ∀ h : H, (eps a h : K) = (if h = a then 1 else 0) + (if h = 1 then -1 else 0) := by
    intro h
    unfold eps
    by_cases h1 : h = a
    · subst h1
      simp [ha]
    · simp [h1]
  rw [show (∑ c : H, (eps a (c * t) : K)) = ∑ h : H, (eps a h : K) from
    Equiv.sum_comp (Equiv.mulRight t) (fun h => (eps a h : K))]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma sum_bas (a : ι → {c : H // c ≠ 1}) (v : ι) (h : ι → H) :
    ∑ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K) = 0 := by
  have hfac : ∀ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K)
      = (eps (a v : H) (c * h v) : K) * ∏ w ∈ univ.erase v, (eps (a w : H) (h w) : K) := by
    intro c
    unfold bas
    rw [← Finset.mul_prod_erase univ _ (mem_univ v)]
    simp only [mulSingle_mul_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mulSingle_mul_apply_ne v w c h (Finset.ne_of_mem_erase hw)]
  simp only [hfac, ← Finset.sum_mul, sum_eps (K := K) (a v : H) (h v) (a v).2, zero_mul]

lemma bas_avoid (a b : ι → {c : H // c ≠ 1}) :
    (bas a (fun w => (b w : H)) : K) = if a = b then 1 else 0 := by
  unfold bas
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold eps
    simp
  · rw [if_neg hab]
    have hw : ∃ w, a w ≠ b w := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hab (funext hcon)
    obtain ⟨w, hw⟩ := hw
    refine Finset.prod_eq_zero (mem_univ w) ?_
    have h1 : (b w : H) ≠ a w := fun h => hw (Subtype.ext h.symm)
    unfold eps
    simp [h1, (b w).2]

lemma inj_core (ψ : (ι → H) → K)
    (hψ : ∀ (v : ι) (h : ι → H), ∑ c : H, ψ ((Pi.mulSingle v c : ι → H) * h) = 0)
    (h0 : ∀ a : ι → {c : H // c ≠ 1}, ψ (fun w => (a w : H)) = 0) :
    ∀ h, ψ h = 0 := by
  classical
  suffices key : ∀ n, ∀ h : ι → H, (univ.filter (fun w => h w = 1)).card = n → ψ h = 0 from
    fun h => key _ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn
    by_cases hall : ∀ w, h w ≠ 1
    · exact h0 (fun w => ⟨h w, hall w⟩)
    · simp only [not_forall, not_not] at hall
      obtain ⟨v, hv⟩ := hall
      have hsum := hψ v h
      rw [Finset.sum_eq_single (1 : H)] at hsum
      · simpa using hsum
      · intro c _ hc
        apply ih _ _ _ rfl
        rw [← hn]
        have hset : univ.filter (fun w => ((Pi.mulSingle v c : ι → H) * h) w = 1)
            = (univ.filter (fun w => h w = 1)).erase v := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hwv : w = v
          · subst hwv
            rw [mulSingle_mul_apply_self, hv, mul_one]
            simp [hc]
          · rw [mulSingle_mul_apply_ne v w c h hwv]
            simp [hwv]
        rw [hset]
        exact Finset.card_erase_lt_of_mem (by simp [hv])
      · intro h1
        exact absurd (Finset.mem_univ _) h1

end Core

section Main

variable {ι H X K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H]
  [Fintype X] [MulAction (ι → H) X] [Field K]

def restr (Q : Type) (e : Q × (ι → H) ≃ X) :
    ramSub ι H X K →ₗ[K] (Q × (ι → {c : H // c ≠ 1}) → K) where
  toFun φ p := (φ : X → K) (e (p.1, fun w => (p.2 w : H)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_core (Q : Type) [Fintype Q] (e : Q × (ι → H) ≃ X)
    (he : ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g)) :
    Module.finrank K (ramSub ι H X K) = Fintype.card Q * (Fintype.card H - 1) ^ Fintype.card ι := by
  classical
  have hmem : ∀ φ : ramSub ι H X K, ∀ v x,
      ∑ c : H, (φ : X → K) ((Pi.mulSingle v c : ι → H) • x) = 0 := fun φ => φ.2
  have hinj : Function.Injective (restr (K := K) Q e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext x
    obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
    have hz := inj_core (K := K) (fun h => (φ : X → K) (e (ω, h)))
      (fun v h => by simpa only [he] using hmem φ v (e (ω, h)))
      (fun a => congrFun hφ (ω, a)) g
    simpa using hz
  have hsurj : Function.Surjective (restr (K := K) Q e) := by
    intro f
    let φ0 : X → K := fun x =>
      ∑ a : ι → {c : H // c ≠ 1}, f ((e.symm x).1, a) * bas a (e.symm x).2
    have hφ0 : φ0 ∈ ramSub ι H X K := by
      show ∀ (v : ι) (x : X), ∑ c : H, φ0 ((Pi.mulSingle v c : ι → H) • x) = 0
      intro v x
      obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
      have hx : ∀ c : H, e.symm ((Pi.mulSingle v c : ι → H) • e (ω, g))
          = (ω, (Pi.mulSingle v c : ι → H) * g) := by
        intro c
        rw [← he, Equiv.symm_apply_apply]
      simp only [φ0, hx]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.mul_sum, sum_bas, mul_zero]
    refine ⟨⟨φ0, hφ0⟩, ?_⟩
    funext p
    obtain ⟨ω, a'⟩ := p
    show φ0 (e (ω, fun w => (a' w : H))) = f (ω, a')
    simp only [φ0, Equiv.symm_apply_apply, bas_avoid]
    simp
  have hc : Fintype.card {c : H // c ≠ 1} = Fintype.card H - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [(LinearEquiv.ofBijective (restr (K := K) Q e) ⟨hinj, hsurj⟩).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fun, hc]

end Main

theorem exists_equiv (ι H X : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] (hfree : ∀ (g : ι → H) (x : X), g • x = x → g = 1) :
    ∃ (Q : Type) (_ : Fintype Q) (e : Q × (ι → H) ≃ X),
      ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g) := by
  classical
  let Q := MulAction.orbitRel.Quotient (ι → H) X
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → X := fun ω => Quotient.out ω
  have hrep : ∀ ω : Q, Quotient.mk (MulAction.orbitRel (ι → H) X) (rep ω) = ω :=
    fun ω => Quotient.out_eq ω
  let f : Q × (ι → H) → X := fun p => p.2 • rep p.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ω, g⟩ ⟨ω', g'⟩ h
      change g • rep ω = g' • rep ω' at h
      have hω : ω = ω' := by
        rw [← hrep ω, ← hrep ω']
        apply Quotient.sound
        show rep ω ∈ MulAction.orbit (ι → H) (rep ω')
        refine ⟨g⁻¹ * g', ?_⟩
        show (g⁻¹ * g') • rep ω' = rep ω
        rw [mul_smul, ← h, inv_smul_smul]
      subst hω
      have hfix : (g'⁻¹ * g) • rep ω = rep ω := by rw [mul_smul, h, inv_smul_smul]
      have hg := hfree _ _ hfix
      rw [inv_mul_eq_one] at hg
      rw [hg]
    · intro x
      have hx : rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) ∈ MulAction.orbit (ι → H) x :=
        Quotient.exact (hrep _)
      obtain ⟨g, hg⟩ := hx
      refine ⟨(Quotient.mk (MulAction.orbitRel (ι → H) X) x, g⁻¹), ?_⟩
      show g⁻¹ • rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) = x
      rw [← hg, inv_smul_smul]
  refine ⟨Q, inferInstance, Equiv.ofBijective f hf, ?_⟩
  intro m ω g
  show (m * g) • rep ω = m • (g • rep ω)
  rw [mul_smul]

theorem finrankFiberSumZero : FinrankFiberSumZero := by
  intro ι H X K _ _ _ _ _ _ _ hfree
  classical
  obtain ⟨Q, _, e, he⟩ := exists_equiv ι H X hfree
  rw [finrank_core (K := K) Q e he, ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  ring

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end
