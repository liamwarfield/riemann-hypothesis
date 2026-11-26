module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LowMinusUpExpand
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiPart
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem contDiff_lead_casimir_coefficients (j : ℕ) :
    ContDiff ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ => lead j w) := by
  by_cases h : j ≤ n
  · have e : (fun w : Matrix (Fin n) (Fin n) ℂ => lead j w) =
        fun w => (w.submatrix (Fin.castLE h) (Fin.castLE h)).det := funext fun w => dif_pos h
    rw [e]
    simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    refine contDiff_prod fun p _ => ?_
    exact contDiff_pi.1 (contDiff_pi.1 (contDiff_id (𝕜 := ℂ) (E := Matrix (Fin n) (Fin n) ℂ))
      (Fin.castLE h (σ p))) (Fin.castLE h p)
  · have e : (fun w : Matrix (Fin n) (Fin n) ℂ => lead j w) = fun _ => 0 := funext fun w => dif_neg h
    rw [e]
    exact contDiff_const

private theorem differentiableAt_PhiM_of_mem_OmegaSet (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0 := hz
  have key : ∀ i : Fin n, ContDiffAt ℂ 1
      (fun w : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) w ^ (-(μ i - muNext μ i))) z := by
    intro i
    have hd : ContDiffAt ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) w) z :=
      (contDiff_lead_casimir_coefficients ((i : ℕ) + 1)).contDiffAt
    have key' : ∀ k : ℤ,
        ContDiffAt ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) w ^ k) z := by
      intro k
      cases k with
      | ofNat p => simpa using hd.pow p
      | negSucc p =>
        simp only [zpow_negSucc]
        exact (hd.pow (p + 1)).inv (pow_ne_zero _ (hz' i))
    exact key' _
  have hc : ContDiffAt ℂ 1 (fun w : Matrix (Fin n) (Fin n) ℂ =>
      ∏ i : Fin n, lead ((i : ℕ) + 1) w ^ (-(μ i - muNext μ i))) z :=
    contDiffAt_prod fun i _ => key i
  exact hc.differentiableAt one_ne_zero

private theorem fderiv_PhiM_of_lead_curve (μ : Fin n → ℤ) {z V : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    (D : ℕ → ℂ) (hlead : ∀ (t : ℂ) (i : Fin n), lead ((i : ℕ) + 1) (z + t • V) =
      (∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * D a)) * lead ((i : ℕ) + 1) z) :
    fderiv ℂ (PhiM μ) z V = -(∑ a ∈ Finset.range n,
      (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) * D a) * PhiM μ z := by
  set m : ℕ → ℂ := fun k => if h : k < n then (μ ⟨k, h⟩ : ℂ) else 0 with hm
  have hc : HasDerivAt (fun t : ℂ => z + t • V) V 0 := by
    exact (((hasDerivAt_id (0 : ℂ)).smul_const V).const_add z).congr_deriv (one_smul ℂ V)
  have hΦ : HasFDerivAt (PhiM μ) (fderiv ℂ (PhiM μ) z) (z + (0 : ℂ) • V) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_PhiM_of_mem_OmegaSet μ hz).hasFDerivAt
  have h1 := hΦ.comp_hasDerivAt (0 : ℂ) hc
  set p : Fin n → ℂ → ℂ := fun i t => ∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * D a) with hp
  have hfun : (PhiM μ ∘ fun t : ℂ => z + t • V) =
      fun t => (∏ i : Fin n, p i t ^ (-(μ i - muNext μ i))) * PhiM μ z := by
    funext t
    simp only [Function.comp_apply, PhiM, hlead, mul_zpow, Finset.prod_mul_distrib, hp]
  have hpd : ∀ i : Fin n, HasDerivAt (p i) (∑ a ∈ Finset.range ((i : ℕ) + 1), D a) 0 := by
    intro i
    have h := HasDerivAt.finsetProd (u := Finset.range ((i : ℕ) + 1)) (x := (0 : ℂ))
      (f := fun a t => 1 + t * D a) (f' := fun a => D a)
      (fun a _ => by simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (D a)).const_add 1)
    refine (h.congr_deriv (by simp [Finset.prod_apply])).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [hp, Finset.prod_apply]
  have hp0 : ∀ i : Fin n, p i 0 = 1 := fun i => by simp [hp]
  have hfd : ∀ i : Fin n, HasDerivAt (fun t => p i t ^ (-(μ i - muNext μ i)))
      ((((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a) 0 := by
    intro i
    have h := (hasDerivAt_zpow (-(μ i - muNext μ i)) (p i 0)
      (Or.inl (by rw [hp0]; exact one_ne_zero))).comp (0 : ℂ) (hpd i)
    exact h.congr_deriv (by rw [hp0]; simp)
  have h2 : HasDerivAt (fun t => (∏ i : Fin n, p i t ^ (-(μ i - muNext μ i))) * PhiM μ z)
      ((∑ i : Fin n, (((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a) *
        PhiM μ z) 0 := by
    have h := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hfd i)).mul_const (PhiM μ z)
    refine (h.congr_deriv (by simp [hp0, Finset.prod_apply])).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have htel : ∀ N : ℕ, ∑ k ∈ Finset.range N, (m (k + 1) - m k) * ∑ a ∈ Finset.range (k + 1), D a =
      m N * ∑ a ∈ Finset.range N, D a - ∑ a ∈ Finset.range N, m a * D a := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ (fun k => (m (k + 1) - m k) * ∑ a ∈ Finset.range (k + 1), D a), ih,
        Finset.sum_range_succ (fun a => m a * D a), Finset.sum_range_succ D]
      ring
  have hmn : m n = 0 := by simp [hm]
  have hm0 : ∀ i : Fin n, m i = (μ i : ℂ) := fun i => by simp [hm, i.2]
  have hmN : ∀ i : Fin n, ((muNext μ i : ℤ) : ℂ) = m ((i : ℕ) + 1) := fun i => by
    simp only [muNext, hm]
    split_ifs <;> simp
  have hterm : ∀ i : Fin n, (((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a =
      (m ((i : ℕ) + 1) - m i) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a := fun i => by
    rw [hm0 i, ← hmN i]
    push_cast
    ring
  have hsumeq : ∑ i : Fin n, (((-(μ i - muNext μ i)) : ℤ) : ℂ) * ∑ a ∈ Finset.range ((i : ℕ) + 1), D a =
      -∑ a ∈ Finset.range n, m a * D a := by
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range (fun k => (m (k + 1) - m k) * ∑ a ∈ Finset.range (k + 1), D a) n,
      htel n, hmn]
    ring
  rw [hfun] at h1
  have hu := h1.unique h2
  rw [hsumeq] at hu
  exact hu

private theorem lead_add_smul_mul_of_isLowerTri {X z : Matrix (Fin n) (Fin n) ℂ} (hX : IsLowerTri X) (t : ℂ)
    (i : Fin n) : lead ((i : ℕ) + 1) (z + t • (X * z)) =
      (∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0))) *
        lead ((i : ℕ) + 1) z := by
  have hi : (i : ℕ) + 1 ≤ n := i.2
  set e : Fin ((i : ℕ) + 1) → Fin n := Fin.castLE hi with he
  set A : Matrix (Fin n) (Fin n) ℂ := 1 + t • X with hA
  have hAz : z + t • (X * z) = A * z := by
    rw [hA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hzero : ∀ a c : Fin n, a < c → A a c = 0 := fun a c hac => by
    rw [hA, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hac), Matrix.smul_apply, hX _ _ hac,
      smul_zero, zero_add]
  have hsub : (A * z).submatrix e e = A.submatrix e e * z.submatrix e e := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective hi) _ _ ?_ (fun r => rfl)
    intro c hc
    have hc' : (i : ℕ) + 1 ≤ c := by
      by_contra hlt
      push_neg at hlt
      exact hc ⟨⟨c, hlt⟩, Fin.ext rfl⟩
    have hlt : e p < c := by
      show (p : ℕ) < c
      exact lt_of_lt_of_le p.2 hc'
    show A (e p) c * z c (e q) = 0
    rw [hzero _ _ hlt, zero_mul]
  have htri : (A.submatrix e e).BlockTriangular OrderDual.toDual := by
    intro p q hpq
    have hpq' : p < q := OrderDual.toDual_lt_toDual.1 hpq
    have hlt : e p < e q := by
      show (p : ℕ) < q
      exact hpq'
    exact hzero _ _ hlt
  simp only [lead, dif_pos hi]
  rw [hAz, hsub, Matrix.det_mul, Matrix.det_of_lowerTriangular _ htri]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun a => 1 + t * (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : (p : ℕ) < n := lt_of_lt_of_le p.2 hi
  have hep : (⟨(p : ℕ), hp⟩ : Fin n) = e p := Fin.ext rfl
  simp only [dif_pos hp, hep, Matrix.submatrix_apply, hA, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul]

private theorem lead_add_smul_mul_of_isUpperTri {X z : Matrix (Fin n) (Fin n) ℂ} (hX : IsUpperTri X) (t : ℂ)
    (i : Fin n) : lead ((i : ℕ) + 1) (z + t • (z * X)) =
      (∏ a ∈ Finset.range ((i : ℕ) + 1), (1 + t * (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0))) *
        lead ((i : ℕ) + 1) z := by
  have hi : (i : ℕ) + 1 ≤ n := i.2
  set e : Fin ((i : ℕ) + 1) → Fin n := Fin.castLE hi with he
  set A : Matrix (Fin n) (Fin n) ℂ := 1 + t • X with hA
  have hAz : z + t • (z * X) = z * A := by
    rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hzero : ∀ a c : Fin n, c < a → A a c = 0 := fun a c hca => by
    rw [hA, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hca).symm, Matrix.smul_apply, hX _ _ hca,
      smul_zero, zero_add]
  have hsub : (z * A).submatrix e e = z.submatrix e e * A.submatrix e e := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective hi) _ _ ?_ (fun r => rfl)
    intro c hc
    have hc' : (i : ℕ) + 1 ≤ c := by
      by_contra hlt
      push_neg at hlt
      exact hc ⟨⟨c, hlt⟩, Fin.ext rfl⟩
    have hlt : e q < c := by
      show (q : ℕ) < c
      exact lt_of_lt_of_le q.2 hc'
    show z (e p) c * A c (e q) = 0
    rw [hzero _ _ hlt, mul_zero]
  have htri : (A.submatrix e e).BlockTriangular id := by
    intro p q hpq
    have hlt : e q < e p := by
      show (q : ℕ) < p
      exact hpq
    exact hzero _ _ hlt
  simp only [lead, dif_pos hi]
  rw [hAz, hsub, Matrix.det_mul, Matrix.det_of_upperTriangular htri, mul_comm]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun a => 1 + t * (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0))]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hp : (p : ℕ) < n := lt_of_lt_of_le p.2 hi
  have hep : (⟨(p : ℕ), hp⟩ : Fin n) = e p := Fin.ext rfl
  simp only [dif_pos hp, hep, Matrix.submatrix_apply, hA, Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul]

lemma fderiv_phiM_lower (μ : Fin n → ℤ) {z X : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    (hX : IsLowerTri X) :
    fderiv ℂ (PhiM μ) z (X * z) = -(∑ a, (μ a : ℂ) * X a a) * PhiM μ z := by
  have hs : ∑ a ∈ Finset.range n, (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) *
      (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0) = ∑ a, (μ a : ℂ) * X a a := by
    rw [← Fin.sum_univ_eq_sum_range (fun a => (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) *
      (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0)) n]
    simp
  rw [fderiv_PhiM_of_lead_curve μ hz _ (fun t i => lead_add_smul_mul_of_isLowerTri hX t i), hs]

lemma fderiv_phiM_upper (μ : Fin n → ℤ) {z X : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    (hX : IsUpperTri X) :
    fderiv ℂ (PhiM μ) z (z * X) = -(∑ a, (μ a : ℂ) * X a a) * PhiM μ z := by
  have hs : ∑ a ∈ Finset.range n, (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) *
      (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0) = ∑ a, (μ a : ℂ) * X a a := by
    rw [← Fin.sum_univ_eq_sum_range (fun a => (if h : a < n then (μ ⟨a, h⟩ : ℂ) else 0) *
      (if h : a < n then X ⟨a, h⟩ ⟨a, h⟩ else 0)) n]
    simp
  rw [fderiv_PhiM_of_lead_curve μ hz _ (fun t i => lead_add_smul_mul_of_isUpperTri hX t i), hs]

theorem phiM_part (μ : Fin n → ℤ) {z B : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    fderiv ℂ (PhiM μ) z (B * z + z * B) =
      fderiv ℂ (PhiM μ) z (z * lowMinusUp B - lowMinusUp B * z) -
        2 * (∑ a, (μ a : ℂ) * B a a) * PhiM μ z := by
  set X1 : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun a b => if b < a then 2 * B a b else if a = b then B a b else 0 with hX1
  set X2 : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun a b => if a < b then 2 * B a b else if a = b then B a b else 0 with hX2
  have e1 : B + lowMinusUp B = X1 := by
    ext a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [lowMinusUp, hX1, h, lt_asymm h, ne_of_lt h] <;> ring
    · simp [lowMinusUp, hX1]
    · simp [lowMinusUp, hX1, h, lt_asymm h, (ne_of_lt h).symm] <;> ring
  have e2 : B - lowMinusUp B = X2 := by
    ext a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [lowMinusUp, hX2, h, lt_asymm h, ne_of_lt h] <;> ring
    · simp [lowMinusUp, hX2]
    · simp [lowMinusUp, hX2, h, lt_asymm h, (ne_of_lt h).symm] <;> ring
  have hL : IsLowerTri X1 := fun a b hab => by simp [hX1, lt_asymm hab, ne_of_lt hab]
  have hU : IsUpperTri X2 := fun a b hab => by simp [hX2, lt_asymm hab, (ne_of_lt hab).symm]
  have hsplit : B * z + z * B = (z * lowMinusUp B - lowMinusUp B * z) + (X1 * z + z * X2) := by
    rw [← e1, ← e2, Matrix.add_mul, Matrix.mul_sub]
    abel
  have d1 : ∑ a, (μ a : ℂ) * X1 a a = ∑ a, (μ a : ℂ) * B a a := by simp [hX1]
  have d2 : ∑ a, (μ a : ℂ) * X2 a a = ∑ a, (μ a : ℂ) * B a a := by simp [hX2]
  rw [hsplit, map_add (f := _), map_add (f := _), fderiv_phiM_lower μ hz hL, fderiv_phiM_upper μ hz hU, d1, d2]
  ring

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TauPart
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def upPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a < b then B a b else 0

def lowPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b < a then B a b else 0

def diagPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => B a a

lemma decomp_up (B : Matrix (Fin n) (Fin n) ℂ) :
    B = lowMinusUp B + (2 : ℂ) • upPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, lowMinusUp, upPart, diagPart, Matrix.of_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_neg (lt_asymm h), if_neg h.ne']
    ring

lemma decomp_low (B : Matrix (Fin n) (Fin n) ℂ) :
    B = -lowMinusUp B + (2 : ℂ) • lowPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, lowMinusUp, lowPart, diagPart,
    Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_pos h, if_neg h.ne']
    ring

lemma single_eq_smul (a b : Fin n) (c : ℂ) :
    Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma dtau_upPart_w (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    T.dτ (upPart B) T.w = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.matrix_eq_sum_single (upPart B), map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
  simp only [upPart, Matrix.of_apply]
  split_ifs with h
  · by_cases he : ε a = ε b
    · rw [T.w_hw a b h he, smul_zero]
    · rw [hB a b he, zero_smul]
  · rw [zero_smul]

lemma dtau_diagPart_w (T : KType ε Λ) (B : Matrix (Fin n) (Fin n) ℂ) :
    T.dτ (diagPart B) T.w = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • T.w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.matrix_eq_sum_single (diagPart B), map_sum, _root_.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, _root_.sum_apply, Finset.sum_eq_single a]
  · rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply, T.w_wt, smul_smul]
    simp only [diagPart, Matrix.diagonal_apply_eq]
    rw [mul_comm]
  · intro b _ hb
    rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
    simp only [diagPart, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    rw [zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma isBlock_lowPart {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) : IsBlock ε (lowPart B) := by
  intro a b h
  simp only [lowPart, Matrix.of_apply]
  split_ifs
  · exact hB a b h
  · rfl

lemma isBlock_diagPart (B : Matrix (Fin n) (Fin n) ℂ) : IsBlock ε (diagPart B) := by
  intro a b h
  have hab : a ≠ b := by
    rintro rfl
    exact h rfl
  simp only [diagPart]
  exact Matrix.diagonal_apply_ne _ hab

lemma lowPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (lowPart B)ᴴ = upPart B := by
  ext a b
  simp only [Matrix.conjTranspose_apply, lowPart, upPart, Matrix.of_apply]
  split_ifs
  · have h := congrFun (congrFun hBh a) b
    rw [Matrix.conjTranspose_apply] at h
    exact h
  · exact star_zero _

lemma diagPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (diagPart B)ᴴ = diagPart B := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [diagPart]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have h' := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h'
    exact h'
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]

theorem tau_part {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : IsBlock ε B) (hBh : Bᴴ = B) :
    T.dτ B * projW T + projW T * T.dτ B =
      (T.dτ (lowMinusUp B) * projW T - projW T * T.dτ (lowMinusUp B)) +
        (2 * ∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
  have hP : ∀ v, projW T v = inner ℂ T.w v • T.w := fun v => by
    simp only [projW, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hBaa : ∀ a, (starRingEnd ℂ) (B a a) = B a a := fun a => by
    have h := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hc : (starRingEnd ℂ) (∑ a, ((Λ a : ℝ) : ℂ) * B a a) = ∑ a, ((Λ a : ℝ) : ℂ) * B a a := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_ofReal, hBaa]
  have h1 : T.dτ (upPart B) * projW T = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_upPart_w T hB, smul_zero,
      ContinuousLinearMap.zero_apply]
  have h2 : T.dτ (diagPart B) * projW T = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_diagPart_w, ContinuousLinearMap.smul_apply,
      hP, smul_comm]
  have h3 : projW T * T.dτ (lowPart B) = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_lowPart hB), lowPart_conjTranspose hBh, dtau_upPart_w T hB, inner_zero_left,
      zero_smul, ContinuousLinearMap.zero_apply]
  have h4 : projW T * T.dτ (diagPart B) = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_diagPart B), diagPart_conjTranspose hBh, dtau_diagPart_w, inner_smul_left, hc,
      ContinuousLinearMap.smul_apply, hP, mul_smul]
  have eB1 : T.dτ B = T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (upPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_up B]
    rw [map_add (f := _), map_add (f := _), map_smul]
  have eB2 : T.dτ B = -T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (lowPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_low B]
    rw [map_add (f := _), map_add (f := _), map_smul, map_neg]
  have hL : T.dτ B * projW T =
      T.dτ (lowMinusUp B) * projW T + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB1, add_mul, add_mul, smul_mul_assoc, h1, smul_zero, add_zero, h2]
  have hR : projW T * T.dτ B =
      -(projW T * T.dτ (lowMinusUp B)) + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB2, mul_add, mul_add, mul_smul_comm, h3, smul_zero, add_zero, h4, mul_neg]
  rw [hL, hR, two_mul, add_smul]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

namespace InfKH

variable {Λ : Fin n → ℝ}

lemma lowMinusUp_expand {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    lowMinusUp B = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ) := by
  ext i j
  have hsum : (∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
      ((if b < a then (1 : ℂ) else -1) * B a b) • Matrix.single a b (1 : ℂ)) i j =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
        if a = i ∧ b = j then (if b < a then (1 : ℂ) else -1) * B a b else 0 := by
    first
    | simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
    | (simp only [Matrix.sum_apply]
       refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
       by_cases h : a = i ∧ b = j
       · rw [if_pos h]
         obtain ⟨rfl, rfl⟩ := h
         simp
       · rw [if_neg h]
         simp [Matrix.single_apply, h])
  rw [hsum]
  rw [Finset.sum_eq_single i (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun h => ha h.1)
    (fun h => absurd (Finset.mem_univ i) h)]
  by_cases hj : ε j = ε i ∧ j ≠ i
  · rw [Finset.sum_eq_single j (fun b _ hb => if_neg fun h => hb h.2)
      (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)).elim)]
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [lowMinusUp, Matrix.of_apply]
    rcases lt_trichotomy j i with h | h | h
    · simp [h]
    · exact absurd h hj.2
    · simp [h, not_lt.2 h.le]
  · rw [Finset.sum_eq_zero fun b hb => if_neg fun h => hj (by
      obtain ⟨-, rfl⟩ := h
      exact (Finset.mem_filter.1 hb).2)]
    simp only [lowMinusUp, Matrix.of_apply]
    by_cases he : j = i
    · subst he
      simp
    · have hne : ε i ≠ ε j := fun h => hj ⟨h.symm, he⟩
      simp [hB i j hne]

lemma isBlock_single {a b : Fin n} (h : ε b = ε a) : IsBlock ε (Matrix.single a b (1 : ℂ)) := by
  intro a' b' hne
  by_cases h' : a = a' ∧ b = b'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h.symm hne
  · first
    | rw [Matrix.single_apply, if_neg h']
    | simp [Matrix.single_apply, h']
    | (simp only [Matrix.single_apply]
       exact if_neg h')

lemma scal (μ : Fin n → ℤ) (hμ : IsMu lam μ) (B : Matrix (Fin n) (Fin n) ℂ) :
    2 * ∑ a, (μ a : ℂ) * B a a =
      2 * ∑ a, ((lowK ε lam a : ℝ) : ℂ) * B a a + 4 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * B a a := by
  have key : ∀ a, ((μ a : ℤ) : ℂ) = ((lowK ε lam a : ℝ) : ℂ) + 2 * ((rhoC ε a : ℝ) : ℂ) := by
    intro a
    have hgt1 : (univ.filter (fun b => a < b ∧ ε b = ε a)).card +
        (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card = (univ.filter (fun b => a < b)).card := by
      first
      | (have h1 := Finset.filter_card_add_filter_neg_card_eq_card
            (s := univ.filter (fun b => a < b)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
      | (have h1 := Finset.card_filter_add_card_filter_not
            (s := univ.filter (fun b => a < b)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
    have hlt1 : (univ.filter (fun b => b < a ∧ ε b = ε a)).card +
        (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card = (univ.filter (fun b => b < a)).card := by
      first
      | (have h1 := Finset.filter_card_add_filter_neg_card_eq_card
            (s := univ.filter (fun b => b < a)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
      | (have h1 := Finset.card_filter_add_card_filter_not
            (s := univ.filter (fun b => b < a)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
    have hc1 : (univ.filter (fun b : Fin n => a < b)).card + (a : ℕ) + 1 = n := by
      have ha := a.isLt
      first
      | (rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
         omega)
      | (simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
         omega)
    have hc2 : (univ.filter (fun b : Fin n => b < a)).card = (a : ℕ) := by
      first
      | rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
      | simp [Finset.filter_gt_eq_Iio]
    have hr : ((μ a : ℤ) : ℝ) = lowK ε lam a + 2 * rhoC ε a := by
      rw [hμ a]
      delta lowK rhoC rhoN rho
      simp only [Pi.add_apply, Pi.sub_apply]
      have e1 : ((univ.filter (fun b => a < b ∧ ε b = ε a)).card : ℝ) +
          (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card + (a : ℕ) + 1 = n := by
        exact_mod_cast (hgt1.symm ▸ hc1 : _)
      have e2 : ((univ.filter (fun b => b < a ∧ ε b = ε a)).card : ℝ) +
          (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card = (a : ℕ) := by
        exact_mod_cast (hlt1.trans hc2)
      linarith
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hr
    push_cast at h2 ⊢
    linear_combination h2
  have e : ∑ a, (μ a : ℂ) * B a a = ∑ a, ((lowK ε lam a : ℝ) : ℂ) * B a a +
      2 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * B a a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a]
    ring
  rw [e]
  ring

def Ssum (T : KType ε Λ) (μ : Fin n → ℤ) (x A : Matrix (Fin n) (Fin n) ℂ) (k : KG ε) : T.V →L[ℂ] T.V :=
  ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a ∧ b ≠ a),
    (if b < a then (1 : ℂ) else -1) • InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k

lemma integral_Ssum [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (A : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (Ssum T μ x A) (muK ε) ∧ ∫ k, Ssum T μ x A k ∂(muK ε) = 0 := by
  have hI : ∀ a b : Fin n, Integrable (fun k => (if b < a then (1 : ℂ) else -1) •
      InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k) (muK ε) := fun a b =>
    InfKA.integrable_of_cont ((InfKA.continuous_Ek T μ hx (InfKA.entryCLM a b) A
      (Matrix.single a b 1)).const_smul (if b < a then (1 : ℂ) else -1))
  refine ⟨MeasureTheory.integrable_finsetSum _ fun a _ => MeasureTheory.integrable_finsetSum _ fun b _ => hI a b, ?_⟩
  unfold Ssum
  rw [MeasureTheory.integral_finsetSum _ fun a _ => MeasureTheory.integrable_finsetSum _ fun b _ => hI a b]
  refine sum_eq_zero fun a _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun b _ => hI a b]
  refine sum_eq_zero fun b hb => ?_
  rw [integral_smul (if b < a then (1 : ℂ) else -1)
    (fun k => InfKA.Ek T μ x (InfKA.entryCLM a b) A (Matrix.single a b 1) k), InfKA.integral_Ek_block T μ hx _ A (isBlock_single (mem_filter.mp hb).2.1), smul_zero]

lemma Ssum_eq (T : KType ε Λ) (μ : Fin n → ℤ) (x A : Matrix (Fin n) (Fin n) ℂ) (k : KG ε)
    (hB : IsBlock ε (toMK k⁻¹ * A * toMK k)) :
    Ssum T μ x A k = InfKA.DkL T μ x k (lowMinusUp (toMK k⁻¹ * A * toMK k)) +
      (-4 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * (toMK k⁻¹ * A * toMK k) a a) • Gint T μ x k := by
  have hφ : ∀ (a b : Fin n) (M : Matrix (Fin n) (Fin n) ℂ), InfKA.entryCLM a b M = M a b :=
    fun _ _ _ => rfl
  simp only [Ssum, InfKA.Ek, smul_add, Finset.sum_add_distrib, smul_smul, hφ]
  set A' := toMK k⁻¹ * A * toMK k with hA'
  have hl : ∀ a b, (A' * Matrix.single a b (1 : ℂ) - Matrix.single a b (1 : ℂ) * A') a b =
      A' a a - A' b b := by
    intro a b
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [lowMinusUp_expand hB, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul]
  · simp only [← Finset.sum_smul]
    congr 1
    simp only [hl, Finset.sum_filter]
    have hsplit : ∀ a b : Fin n,
        (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * (A' a a - A' b b) else 0) =
          (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) +
          (if ε a = ε b ∧ a ≠ b then (if a < b then (1 : ℂ) else -1) * A' b b else 0) := by
      intro a b
      by_cases h : ε b = ε a ∧ b ≠ a
      · have h' : ε a = ε b ∧ a ≠ b := ⟨h.1.symm, Ne.symm h.2⟩
        rw [if_pos h, if_pos h, if_pos h']
        rcases lt_or_gt_of_ne h.2 with hab | hab
        · simp only [if_pos hab, if_neg (not_lt.2 hab.le)]
          ring
        · simp only [if_pos hab, if_neg (not_lt.2 hab.le)]
          ring
      · have h' : ¬ (ε a = ε b ∧ a ≠ b) := fun h' => h ⟨h'.1.symm, Ne.symm h'.2⟩
        rw [if_neg h, if_neg h, if_neg h', add_zero]
    simp only [hsplit, Finset.sum_add_distrib]
    conv_lhs => arg 2; rw [Finset.sum_comm]
    rw [← two_mul]
    have hc : ∀ a, ∑ b, (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) =
        -2 * ((rhoC ε a : ℝ) : ℂ) * A' a a := by
      intro a
      have hp : ∀ b, (if ε b = ε a ∧ b ≠ a then (if b < a then (1 : ℂ) else -1) * A' a a else 0) =
          ((if b < a ∧ ε b = ε a then (1 : ℂ) else 0) - (if a < b ∧ ε b = ε a then (1 : ℂ) else 0)) *
            A' a a := by
        intro b
        rcases lt_trichotomy b a with h | rfl | h
        · by_cases he : ε b = ε a <;> simp [h, he, ne_of_lt h, not_lt.2 h.le]
        · simp
        · by_cases he : ε b = ε a <;> simp [h, he, ne_of_gt h, not_lt.2 h.le]
      simp only [hp]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
      delta rhoC
      push_cast
      ring
    simp only [hc]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

lemma pt (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsBlock ε A) (hAh : Aᴴ = A) (k : KG ε) :
    fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k) (toMK k⁻¹ * (A * x + x * A) * toMK k) •
        (T.op k * projW T * T.op k⁻¹) =
      Ssum T μ x A k - (T.dτ A * Gint T μ x k + Gint T μ x k * T.dτ A) := by
  have hmk : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have hop : ∀ a b : KG ε, T.op (a * b) = T.op a * T.op b := fun a b => by simp [KType.op, map_mul]
  have hop1 : T.op 1 = 1 := by simp [KType.op]
  have hkk : toMK k * toMK k⁻¹ = 1 := by rw [← hmk, mul_inv_cancel]; rfl
  have hok : T.op k * T.op k⁻¹ = 1 := by rw [← hop, mul_inv_cancel, hop1]
  have hok' : T.op k⁻¹ * T.op k = 1 := by rw [← hop, inv_mul_cancel, hop1]
  have hAJ : A * Jm ε = Jm ε * A := (kfa_comm_iff_block ε A).mpr hA
  have hk1 : toMK k * Jm ε = Jm ε * toMK k := (show toMK k ∈ Kset ε from k.2).2
  have hk2 : toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := (show toMK k⁻¹ ∈ Kset ε from (k⁻¹).2).2
  have hH : toMK k⁻¹ * (A * x + x * A) * toMK k =
      (toMK k⁻¹ * A * toMK k) * (toMK k⁻¹ * x * toMK k) + (toMK k⁻¹ * x * toMK k) * (toMK k⁻¹ * A * toMK k) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (toMK k) (toMK k⁻¹), hkk, Matrix.one_mul]
  have hBJ : (toMK k⁻¹ * A * toMK k) * Jm ε = Jm ε * (toMK k⁻¹ * A * toMK k) := by
    calc toMK k⁻¹ * A * toMK k * Jm ε = toMK k⁻¹ * (A * (toMK k * Jm ε)) := by simp only [Matrix.mul_assoc]
      _ = toMK k⁻¹ * (A * Jm ε) * toMK k := by rw [hk1]; simp only [Matrix.mul_assoc]
      _ = toMK k⁻¹ * Jm ε * (A * toMK k) := by rw [hAJ]; simp only [Matrix.mul_assoc]
      _ = Jm ε * (toMK k⁻¹ * A * toMK k) := by rw [hk2]; simp only [Matrix.mul_assoc]
  have hBb : IsBlock ε (toMK k⁻¹ * A * toMK k) := (kfa_comm_iff_block ε _).mp hBJ
  have hBh : (toMK k⁻¹ * A * toMK k)ᴴ = toMK k⁻¹ * A * toMK k := by
    rw [InfKA.toMK_inv_eq]; simp [Matrix.conjTranspose_mul, hAh, Matrix.mul_assoc]
  have hdB : T.dτ (toMK k⁻¹ * A * toMK k) = T.op k⁻¹ * T.dτ A * T.op k := by
    have h := dtau_conj T k⁻¹ hA
    rw [inv_inv] at h
    exact h.symm
  have hk3 : ∀ X, T.op k * (T.op k⁻¹ * X) = X := fun X => by rw [← mul_assoc, hok, one_mul]
  have hdA : T.dτ A * (T.op k * projW T * T.op k⁻¹) + (T.op k * projW T * T.op k⁻¹) * T.dτ A =
      T.op k * (T.dτ (toMK k⁻¹ * A * toMK k) * projW T + projW T * T.dτ (toMK k⁻¹ * A * toMK k)) *
        T.op k⁻¹ := by
    rw [hdB]
    simp only [mul_assoc, mul_add, add_mul, hk3, hok, mul_one]
  have hconj : T.dτ A * Gint T μ x k + Gint T μ x k * T.dτ A =
      PhiM μ (toMK k⁻¹ * x * toMK k) • (T.op k * (T.dτ (lowMinusUp (toMK k⁻¹ * A * toMK k)) * projW T -
          projW T * T.dτ (lowMinusUp (toMK k⁻¹ * A * toMK k))) * T.op k⁻¹) +
        ((2 * ∑ a, ((lowK ε lam a : ℝ) : ℂ) * (toMK k⁻¹ * A * toMK k) a a) * PhiM μ (toMK k⁻¹ * x * toMK k)) •
          (T.op k * projW T * T.op k⁻¹) := by
    simp only [Gint]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hdA, tau_part T hBb hBh]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    module
  rw [hH, phiM_part μ (InfKA.conj_mem_omega hx k), Ssum_eq T μ x A k hBb, InfKA.DkL_apply, hconj, scal (ε := ε) μ hμ]
  simp only [Gint]
  module

end InfKH

theorem psM_inf_herm (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsBlock ε A) (hAh : Aᴴ = A) :
    fderiv ℂ (psM T μ) x (A * x + x * A) = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) := by
  have := compactSpace_KG ε
  obtain ⟨U, -, hPU, -, -, hder⟩ := psM_holo T μ
  rw [hder x (hPU hx)]
  have hGI : Integrable (Gint T μ x) (muK ε) := InfKA.integrable_of_cont (InfKA.continuous_Gint T μ hx)
  have hL : ∫ k, T.dτ A * Gint T μ x k ∂(muK ε) = T.dτ A * ∫ k, Gint T μ x k ∂(muK ε) :=
    (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.dτ A)).integral_comp_comm hGI
  have hR : ∫ k, Gint T μ x k * T.dτ A ∂(muK ε) = (∫ k, Gint T μ x k ∂(muK ε)) * T.dτ A :=
    ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V)).flip (T.dτ A)).integral_comp_comm hGI
  have hLI : Integrable (fun k => T.dτ A * Gint T μ x k) (muK ε) :=
    (ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.dτ A)).integrable_comp hGI
  have hRI : Integrable (fun k => Gint T μ x k * T.dτ A) (muK ε) :=
    ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V)).flip (T.dτ A)).integrable_comp hGI
  obtain ⟨hSI, hS0⟩ := InfKH.integral_Ssum T μ hx A
  have hLR : Integrable (fun k => T.dτ A * Gint T μ x k + Gint T μ x k * T.dτ A) (muK ε) := hLI.add hRI
  rw [integral_congr_ae (Filter.Eventually.of_forall (InfKH.pt T μ hμ hx hA hAh)),
    integral_sub hSI hLR, hS0, zero_sub, integral_add hLI hRI, hL, hR]
  have hps : psM T μ x = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, Gint T μ x k ∂(muK ε) := rfl
  rw [hps]
  simp only [smul_neg, smul_add, mul_smul_comm, smul_mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRightA
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma infR_hasFDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) x) x := by
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  have hU : x ∈ Ps1.Uset ε := by
    intro k
    have hk : toMK k⁻¹ = (toMK k)ᴴ := Ps1.toMK_inv_eq k
    have hinv : toMK k⁻¹ * toMK k = 1 := by
      unfold toMK toM
      simp
    have hinj : Function.Injective (toMK k).mulVec := by
      intro v w hvw
      have := congrArg (toMK k⁻¹).mulVec hvw
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hpd : (toMK k⁻¹ * x * toMK k).PosDef := by
      rw [hk]
      exact hx.conjTranspose_mul_mul_same hinj
    intro i
    unfold lead
    rw [dite_eq_left (by omega)]
    exact ((hpd.submatrix (Fin.castLE_injective _)).det_pos).ne'
  exact (Ps1.hasFDerivAt_psM T μ hU).differentiableAt.hasFDerivAt

lemma infR_conj (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A - A * x) = psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
  obtain ⟨γ, -, hγ, hγm⟩ := exists_oneParam ε hA
  have h0 : γ 0 = 1 := by simpa using hγm 0 0
  have hinv : ∀ t, (γ (-t))⁻¹ = γ t := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hγm, neg_add_cancel, h0])

  have heq : ∀ t : ℝ, psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A))
      = T.op (γ (-t)) * psM T μ x * T.op (γ t) := by
    intro t
    have h1 := psM_conj T μ (γ (-t)) x
    rw [hinv, hγ, hγ] at h1
    simpa [Complex.ofReal_neg, neg_smul] using h1

  have hL : HasDerivAt (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
      NormedSpace.exp ((t : ℂ) • A))) (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hc := dga_path A x
    have hψ := infR_hasFDerivAt T μ hx
    exact (hψ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)

  have hR1 := T.hasDeriv A hA γ hγ
  have hR1' : HasDerivAt (fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (T.dτ A) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact hR1
  have hR2 := hR1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hR := (hR2.mul (hasDerivAt_const (0 : ℝ) (psM T μ x))).mul hR1
  have hL' : HasDerivAt (fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) *
      psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hfun : (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
        NormedSpace.exp ((t : ℂ) • A))) = fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) :
          T.V →L[ℂ] T.V) * psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext t
      exact heq t
    rw [hfun] at hL
    exact hL
  rw [hL'.unique hR]
  simp [h0]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

private lemma smul_cancel_lemma {E : Type*} [AddCommGroup E] [Module ℂ E] {c : ℂ} (hc : c ≠ 0)
    {u v : E} (h : c • u = c • v) : u = v := by
  have h' := congrArg (fun w => c⁻¹ • w) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using h'

lemma infR_skew (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A) = -(T.dτ A * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (A * x) = -(psM T μ x * T.dτ A) := by
  obtain ⟨hAs, hAb⟩ := (inK_iff ε A).1 hA
  have hH : IsBlock ε (Complex.I • A) := by
    intro i j hij
    rw [Matrix.smul_apply, hAb i j hij, smul_zero]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hHh : (Complex.I • A)ᴴ = Complex.I • A := by
    rw [Matrix.conjTranspose_smul, hAs, hI, neg_smul_neg]
  have h1 := psM_inf_herm T μ hμ hx hH hHh
  have e1 : Complex.I • A * x + x * (Complex.I • A) = Complex.I • (A * x + x * A) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [e1] at h1

  have hs : fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A) =
      -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) := by
    apply smul_cancel_lemma Complex.I_ne_zero
    simpa only [map_smul, map_add (f := _), smul_mul_assoc, mul_smul_comm, smul_add, smul_neg] using h1

  have hd : fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x) =
      psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
    rw [← map_sub]
    exact infR_conj T μ hx hA
  constructor
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (x * A) + fderiv ℂ (psM T μ) x (x * A)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) +
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) +
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(T.dτ A * psM T μ x) + -(T.dτ A * psM T μ x) := by abel
  · apply smul_cancel_lemma (two_ne_zero : (2 : ℂ) ≠ 0)
    rw [two_smul, two_smul]
    calc fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (A * x)
        = (fderiv ℂ (psM T μ) x (A * x) + fderiv ℂ (psM T μ) x (x * A)) -
          (fderiv ℂ (psM T μ) x (x * A) - fderiv ℂ (psM T μ) x (A * x)) := by abel
      _ = -(T.dτ A * psM T μ x + psM T μ x * T.dτ A) -
          (psM T μ x * T.dτ A - T.dτ A * psM T μ x) := by rw [hs, hd]
      _ = -(psM T μ x * T.dτ A) + -(psM T μ x * T.dτ A) := by abel

theorem psM_inf_right (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    fderiv ℂ (psM T μ) x (x * Y) = -(T.dτ Y * psM T μ x) ∧
      fderiv ℂ (psM T μ) x (Y * x) = -(psM T μ x * T.dτ Y) := by

  obtain ⟨A, B, hA, hB, rfl, -⟩ := block_decomp hY
  have hA' := infR_skew T μ hμ hx hA
  have hB' := infR_skew T μ hμ hx hB
  constructor
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add (f := _), map_smul, hA'.1, hB'.1,
      neg_add, smul_neg]
  · simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add (f := _), map_smul, hA'.2, hB'.2,
      neg_add, smul_neg]

end ReciprocityTheory.ChartRestriction.DS.S7
