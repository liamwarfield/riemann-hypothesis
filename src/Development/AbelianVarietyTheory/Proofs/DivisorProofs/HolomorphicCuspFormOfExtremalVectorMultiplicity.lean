module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.FlowGS

def tri (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (a j : ℕ) : ℂ :=
  if j < a then 0 else if j = a then (ρ (a + 1) : ℂ) / ρ a
  else (τ : ℂ) * Y a * E j * star (Y j) / ((ρ a : ℂ) * ρ (a + 1))

private theorem tri_eq_zero_of_gt (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) {a j : ℕ} (h : j < a) :
    tri E Y τ ρ a j = 0 := by
  unfold tri; rw [if_pos h]

private theorem tri_self (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (a : ℕ) :
    tri E Y τ ρ a a = (ρ (a + 1) : ℂ) / ρ a := by
  unfold tri; rw [if_neg (lt_irrefl a), if_pos rfl]

private theorem tri_of_lt (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) {a j : ℕ} (h : a < j) :
    tri E Y τ ρ a j = (τ : ℂ) * Y a * E j * star (Y j) / ((ρ a : ℂ) * ρ (a + 1)) := by
  unfold tri; rw [if_neg (show ¬ j < a by omega), if_neg (show ¬ j = a by omega)]

theorem tri_gram (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (hE : ∀ a, E a * E a = 1) (hρ : ∀ a, ρ a ≠ 0)
    (h0 : ρ 0 = 1) (hs : ∀ a, (ρ (a + 1) : ℂ) ^ 2 = (ρ a : ℂ) ^ 2 + τ * E a * (Y a * star (Y a))) (i j k : ℕ) :
    ∑ a ∈ Finset.range k, star (tri E Y τ ρ a i) * E a * tri E Y τ ρ a j =
      if k ≤ i ∧ k ≤ j then τ * (E i * Y i) * (E j * star (Y j)) * (1 - 1 / (ρ k : ℂ) ^ 2)
      else (if i = j then (E i : ℂ) else 0) + τ * (E i * Y i) * (E j * star (Y j)) := by
  have hr : ∀ a, (ρ a : ℂ) * (ρ a : ℂ)⁻¹ = 1 := fun a => mul_inv_cancel₀ (by exact_mod_cast hρ a)
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hk := hs k
    have hrk := hr k
    have hrk1 := hr (k + 1)
    rcases lt_trichotomy i k with hi | hi | hi
    · rw [tri_eq_zero_of_gt E Y τ ρ hi, if_neg (show ¬(k ≤ i ∧ k ≤ j) from fun h => by omega),
        if_neg (show ¬(k + 1 ≤ i ∧ k + 1 ≤ j) from fun h => by omega)]
      simp
    · rw [hi]
      rcases lt_trichotomy j k with hj | hj | hj
      · rw [tri_eq_zero_of_gt E Y τ ρ hj, if_neg (show ¬(k ≤ k ∧ k ≤ j) from fun h => by omega),
          if_neg (show ¬(k + 1 ≤ k ∧ k + 1 ≤ j) from fun h => by omega)]
        simp
      · rw [hj, tri_self, if_pos (show k ≤ k ∧ k ≤ k from ⟨le_rfl, le_rfl⟩),
          if_neg (show ¬(k + 1 ≤ k ∧ k + 1 ≤ k) from fun h => by omega), if_pos (rfl : k = k)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((E k : ℂ) * ((ρ k : ℂ) * (ρ k : ℂ)⁻¹ + 1)) * hrk + ((ρ k : ℂ)⁻¹ ^ 2 * (E k : ℂ)) * hk
      · rw [tri_self, tri_of_lt E Y τ ρ hj, if_pos (show k ≤ k ∧ k ≤ j from ⟨le_rfl, hj.le⟩),
          if_neg (show ¬(k + 1 ≤ k ∧ k + 1 ≤ j) from fun h => by omega), if_neg (show ¬(k = j) from by omega)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((τ : ℂ) * (E k : ℂ) * Y k * (E j : ℂ) * (starRingEnd ℂ) (Y j) * (ρ k : ℂ)⁻¹ ^ 2) * hrk1
    · rcases lt_trichotomy j k with hj | hj | hj
      · rw [tri_eq_zero_of_gt E Y τ ρ hj, if_neg (show ¬(k ≤ i ∧ k ≤ j) from fun h => by omega),
          if_neg (show ¬(k + 1 ≤ i ∧ k + 1 ≤ j) from fun h => by omega)]
        simp
      · rw [hj, tri_self, tri_of_lt E Y τ ρ hi, if_pos (show k ≤ i ∧ k ≤ k from ⟨hi.le, le_rfl⟩),
          if_neg (show ¬(k + 1 ≤ i ∧ k + 1 ≤ k) from fun h => by omega), if_neg (show ¬(i = k) from by omega)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((τ : ℂ) * (E i : ℂ) * Y i * (E k : ℂ) * (starRingEnd ℂ) (Y k) * (ρ k : ℂ)⁻¹ ^ 2) * hrk1
      · rw [tri_of_lt E Y τ ρ hi, tri_of_lt E Y τ ρ hj, if_pos (show k ≤ i ∧ k ≤ j from ⟨hi.le, hj.le⟩),
          if_pos (show k + 1 ≤ i ∧ k + 1 ≤ j from ⟨hi, hj⟩)]
        simp only [Complex.star_def, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hk ⊢
        linear_combination ((τ : ℂ) * ((E i : ℂ) * Y i) * ((E j : ℂ) * (starRingEnd ℂ) (Y j))) *
          (-((ρ k : ℂ)⁻¹ ^ 2 * (ρ (k + 1) : ℂ)⁻¹ ^ 2) * hk
            - (ρ (k + 1) : ℂ)⁻¹ ^ 2 * ((ρ k : ℂ) * (ρ k : ℂ)⁻¹ + 1) * hrk
            + (ρ k : ℂ)⁻¹ ^ 2 * ((ρ (k + 1) : ℂ) * (ρ (k + 1) : ℂ)⁻¹ + 1) * hrk1)

theorem tri_vec (E : ℕ → ℝ) (Y : ℕ → ℂ) (τ : ℝ) (ρ : ℕ → ℝ) (hρ : ∀ a, ρ a ≠ 0)
    (hs : ∀ a, (ρ (a + 1) : ℂ) ^ 2 = (ρ a : ℂ) ^ 2 + τ * E a * (Y a * star (Y a))) (a k : ℕ) :
    ∑ j ∈ Finset.range k, tri E Y τ ρ a j * Y j =
      if k ≤ a then 0 else Y a * (ρ k : ℂ) ^ 2 / ((ρ a : ℂ) * ρ (a + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases lt_trichotomy k a with hk | hk | hk
    · rw [tri_eq_zero_of_gt E Y τ ρ hk, if_pos hk.le, if_pos (show k + 1 ≤ a from hk)]
      simp
    · rw [hk, tri_self, if_pos le_rfl, if_neg (show ¬(a + 1 ≤ a) from by omega)]
      have h1 : (ρ (a + 1) : ℂ) * (ρ (a + 1) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hρ (a + 1))
      linear_combination (-((ρ (a + 1) : ℂ) * (ρ a : ℂ)⁻¹ * Y a)) * h1
    · rw [tri_of_lt E Y τ ρ hk, if_neg (show ¬(k ≤ a) from by omega), if_neg (show ¬(k + 1 ≤ a) from by omega)]
      linear_combination (-(Y a * (ρ a : ℂ)⁻¹ * (ρ (a + 1) : ℂ)⁻¹)) * hs k

theorem partial_nonneg (q n : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (hz : ∀ a, n ≤ a → g a = 0)
    (hn : ∑ a ∈ Finset.range n, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a = 0) (k : ℕ) :
    0 ≤ ∑ a ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a := by
  by_cases hkq : k ≤ q
  · apply Finset.sum_nonneg
    intro a ha
    have : a < q := by rw [Finset.mem_range] at ha; omega
    simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_pos this, one_mul]
    exact hg a
  · push_neg at hkq
    have hmn : ∑ a ∈ Finset.range (max k n), ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a = 0 := by
      rw [← Finset.sum_range_add_sum_Ico _ (le_max_right k n), hn, zero_add]
      apply Finset.sum_eq_zero
      intro a ha
      rw [hz a (Finset.mem_Ico.mp ha).1, mul_zero]
    rw [← Finset.sum_range_add_sum_Ico _ (le_max_left k n)] at hmn
    have hneg : ∑ a ∈ Finset.Ico k (max k n), ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a =
        -∑ a ∈ Finset.Ico k (max k n), g a := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have : ¬ a < q := by have := (Finset.mem_Ico.mp ha).1; omega
      simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg this]
      ring
    rw [hneg] at hmn
    have : 0 ≤ ∑ a ∈ Finset.Ico k (max k n), g a := Finset.sum_nonneg fun a _ => hg a
    linarith

theorem partial_le (q n : ℕ) (g : ℕ → ℝ) (hg : ∀ a, 0 ≤ g a) (hz : ∀ a, n ≤ a → g a = 0) (k : ℕ) :
    ∑ a ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a ≤ ∑ a ∈ Finset.range n, g a := by
  calc ∑ a ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * g a ≤ ∑ a ∈ Finset.range k, g a := by
        apply Finset.sum_le_sum
        intro a _
        have h1 : ReciprocityTheory.ChartRestriction.G.FD.sgn q a ≤ 1 := by
          unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
        nlinarith [hg a]
    _ ≤ ∑ a ∈ Finset.range (max k n), g a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (le_max_left k n)) (fun a _ _ => hg a)
    _ = ∑ a ∈ Finset.range n, g a := by
        rw [← Finset.sum_range_add_sum_Ico _ (le_max_right k n)]
        rw [Finset.sum_eq_zero (s := Finset.Ico n (max k n)), add_zero]
        intro a ha
        exact hz a (Finset.mem_Ico.mp ha).1

def sgnM (n q : ℕ) : Mt n := diagonal fun a : Fin n => ((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)

theorem core (n q : ℕ) (y : Fin n → ℂ) (hy : star y ⬝ᵥ (sgnM n q).mulVec y = 0) (t : ℝ) (ht : 0 ≤ t) :
    ∃ b : Mt n, UpT b ∧
      bᴴ * sgnM n q * b = sgnM n q + ((2 * t : ℝ) : ℂ) • vecMulVec ((sgnM n q).mulVec y) (star y ᵥ* sgnM n q) ∧
      (∀ a, ‖b a a‖ ≤ (1 + 2 * ∑ c, ‖y c‖ ^ 2) * (1 + t) ∧ ‖b a a‖⁻¹ ≤ (1 + 2 * ∑ c, ‖y c‖ ^ 2) * (1 + t)) ∧
      ∀ a, ‖(b.mulVec y) a‖ ^ 2 * (1 + t) ≤ ‖y a‖ ^ 2 + 1 := by
  obtain ⟨Y, hYd⟩ : ∃ Y : ℕ → ℂ, ∀ c, Y c = if h : c < n then y ⟨c, h⟩ else 0 := ⟨_, fun _ => rfl⟩
  have hY : ∀ i : Fin n, Y i = y i := fun i => by rw [hYd, dite_eq_left i.isLt]
  have hYz : ∀ c, n ≤ c → Y c = 0 := fun c hc => by rw [hYd, dite_eq_right (show ¬ c < n by omega)]
  obtain ⟨g, hgd⟩ : ∃ g : ℕ → ℝ, ∀ c, g c = ‖Y c‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hgnn : ∀ c, 0 ≤ g c := fun c => by rw [hgd]; positivity
  have hgz : ∀ c, n ≤ c → g c = 0 := fun c hc => by rw [hgd, hYz c hc]; simp
  have hPn : ∑ c ∈ Finset.range n, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c = 0 := by
    have h1 : ((∑ c ∈ Finset.range n, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c : ℝ) : ℂ) =
        star y ⬝ᵥ (sgnM n q).mulVec y := by
      rw [Finset.sum_range]
      simp only [hgd, hY, dotProduct, sgnM, Matrix.mulVec_diagonal, Pi.star_apply]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      have := Complex.conj_mul' (y i)
      rw [Complex.star_def]
      linear_combination (-((ReciprocityTheory.ChartRestriction.G.FD.sgn q i : ℝ) : ℂ)) * this
    have h2 := h1.trans hy
    exact_mod_cast h2
  have hPnn : ∀ k, 0 ≤ ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c :=
    fun k => partial_nonneg q n g hgnn hgz hPn k
  have hPle : ∀ k, ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c ≤ ∑ c ∈ Finset.range n, g c :=
    fun k => partial_le q n g hgnn hgz k
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℕ → ℝ, ∀ k,
      ρ k = Real.sqrt (1 + 2 * t * ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c) := ⟨_, fun _ => rfl⟩
  have hρsq : ∀ k, ρ k ^ 2 = 1 + 2 * t * ∑ c ∈ Finset.range k, ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c := fun k => by
    rw [hρd, Real.sq_sqrt]; nlinarith [hPnn k, mul_nonneg ht (hPnn k)]
  have hρnn : ∀ k, 0 ≤ ρ k := fun k => by rw [hρd]; exact Real.sqrt_nonneg _
  have hρ1 : ∀ k, 1 ≤ ρ k := fun k => by nlinarith [hρsq k, hρnn k, hPnn k, mul_nonneg ht (hPnn k)]
  have hρ0 : ∀ k, ρ k ≠ 0 := fun k => (lt_of_lt_of_le one_pos (hρ1 k)).ne'
  have h0 : ρ 0 = 1 := by rw [hρd]; simp
  have hE : ∀ a, ReciprocityTheory.ChartRestriction.G.FD.sgn q a * ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 := fun a => by
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
  have hs : ∀ a, (ρ (a + 1) : ℂ) ^ 2 = (ρ a : ℂ) ^ 2 +
      ((2 * t : ℝ) : ℂ) * ((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ) * (Y a * star (Y a)) := by
    intro a
    have hr : ρ (a + 1) ^ 2 = ρ a ^ 2 + 2 * t * ReciprocityTheory.ChartRestriction.G.FD.sgn q a * ‖Y a‖ ^ 2 := by
      rw [hρsq, hρsq, Finset.sum_range_succ, hgd]; ring
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    rw [Complex.star_def, Complex.mul_conj']
    push_cast at hc ⊢
    linear_combination hc
  have hlow : ∀ a c : Fin n, c < a → tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a c = 0 :=
    fun a c h => tri_eq_zero_of_gt _ _ _ _ (Fin.lt_iff_val_lt_val.mp h)
  refine ⟨Matrix.of fun a j : Fin n => tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a j, ?_, ?_, ?_, ?_⟩
  · unfold UpT
    refine ⟨?_, fun a c h => by simpa using hlow a c h⟩
    have hUT : (Matrix.of fun a j : Fin n => tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a j).IsUpperTriangular :=
      fun i j h => by simpa using hlow i j h
    rw [Matrix.det_of_isUpperTriangular hUT, Finset.prod_ne_zero_iff]
    intro a _
    simp only [Matrix.of_apply]
    rw [tri_self]
    exact div_ne_zero (by exact_mod_cast hρ0 _) (by exact_mod_cast hρ0 _)
  · ext i j
    have key := tri_gram (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ hE hρ0 h0 hs i j n
    rw [if_neg (show ¬ (n ≤ (i : ℕ) ∧ n ≤ (j : ℕ)) from fun h => by have := i.isLt; omega),
      Finset.sum_range] at key
    simp only [hY] at key
    rw [Matrix.mul_apply]
    simp only [sgnM, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply,
      Matrix.diagonal_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_diagonal,
      Matrix.vecMul_diagonal, Pi.star_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [eq_self_iff_true, if_true] at key ⊢
      linear_combination key
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [hij, hij', if_false] at key ⊢
      linear_combination key
  · have hG : ∑ c, ‖y c‖ ^ 2 = ∑ c ∈ Finset.range n, g c := by
      rw [Finset.sum_range]; simp only [hgd, hY]
    have hGnn : 0 ≤ ∑ c ∈ Finset.range n, g c := Finset.sum_nonneg fun c _ => hgnn c
    have hρle : ∀ k, ρ k ≤ 1 + 2 * t * ∑ c ∈ Finset.range n, g c := fun k => by
      nlinarith [hρsq k, hρ1 k, hPle k, mul_le_mul_of_nonneg_left (hPle k) ht]
    have hM : 1 + 2 * t * ∑ c ∈ Finset.range n, g c ≤ (1 + 2 * ∑ c ∈ Finset.range n, g c) * (1 + t) := by
      nlinarith [mul_nonneg ht hGnn]
    intro a
    simp only [Matrix.of_apply]
    rw [tri_self, hG, ← Complex.ofReal_div, Complex.norm_of_nonneg (div_nonneg (hρnn _) (hρnn _)), inv_div]
    constructor
    · calc ρ ((a : ℕ) + 1) / ρ a ≤ ρ ((a : ℕ) + 1) := div_le_self (hρnn _) (hρ1 _)
        _ ≤ _ := (hρle _).trans hM
    · calc ρ a / ρ ((a : ℕ) + 1) ≤ ρ a := div_le_self (hρnn _) (hρ1 _)
        _ ≤ _ := (hρle _).trans hM
  · intro a
    have key := tri_vec (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ hρ0 hs a n
    rw [if_neg (show ¬ (n ≤ (a : ℕ)) from by have := a.isLt; omega), Finset.sum_range] at key
    simp only [hY] at key
    have hρn : (ρ n : ℂ) ^ 2 = 1 := by
      have : ρ n ^ 2 = 1 := by rw [hρsq, hPn]; ring
      exact_mod_cast this
    rw [hρn, mul_one] at key
    have hv : (Matrix.of fun a j : Fin n => tri (ReciprocityTheory.ChartRestriction.G.FD.sgn q) Y (2 * t) ρ a j).mulVec y a =
        y a / ((ρ a * ρ ((a : ℕ) + 1) : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
      rw [key, Complex.ofReal_mul]
    have hsg : ReciprocityTheory.ChartRestriction.G.FD.sgn q a = 1 ∨ ReciprocityTheory.ChartRestriction.G.FD.sgn q a = -1 := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
    have hPs : ∑ c ∈ Finset.range ((a : ℕ) + 1), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c =
        ∑ c ∈ Finset.range (a : ℕ), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c + ReciprocityTheory.ChartRestriction.G.FD.sgn q a * ‖y a‖ ^ 2 := by
      rw [Finset.sum_range_succ, hgd, hY]
    have hA := hPnn a
    have hB := hPnn ((a : ℕ) + 1)
    have hz : 0 ≤ ‖y a‖ ^ 2 := by positivity
    have hAB : 1 + 2 * t * ‖y a‖ ^ 2 ≤
        (1 + 2 * t * ∑ c ∈ Finset.range (a : ℕ), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c) *
          (1 + 2 * t * ∑ c ∈ Finset.range ((a : ℕ) + 1), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c) := by
      rw [hPs] at hB ⊢
      rcases hsg with h | h
      · rw [h] at hB ⊢
        nlinarith [mul_nonneg ht hA, mul_nonneg ht hz, sq_nonneg (t * ∑ c ∈ Finset.range (a : ℕ), ReciprocityTheory.ChartRestriction.G.FD.sgn q c * g c),
          mul_nonneg (mul_nonneg ht hA) (mul_nonneg ht hz)]
      · rw [h] at hB ⊢
        nlinarith [mul_nonneg ht hB, mul_nonneg ht hz, mul_nonneg (mul_nonneg ht hB) (mul_nonneg ht hB),
          mul_nonneg (mul_nonneg ht hz) (mul_nonneg ht hB), mul_nonneg ht hA]
    rw [hv, norm_div, Complex.norm_of_nonneg (mul_nonneg (hρnn _) (hρnn _)), div_pow, mul_pow, hρsq, hρsq,
      div_mul_eq_mul_div, div_le_iff₀ (by nlinarith [mul_nonneg ht hA, mul_nonneg ht hB, mul_nonneg (mul_nonneg ht hA) (mul_nonneg ht hB)])]
    nlinarith [hAB, mul_le_mul_of_nonneg_left hAB (by positivity : (0 : ℝ) ≤ ‖y a‖ ^ 2 + 1), mul_nonneg ht hz,
      mul_nonneg (mul_nonneg ht hz) hz]

theorem prod_zpow_le {n : ℕ} (v : Fin n → ℂ) (w : Fin n → ℤ) (M : ℝ) (h : ∀ a, ‖v a‖ ≤ M ∧ ‖v a‖⁻¹ ≤ M) :
    ‖∏ a, v a ^ w a‖ ≤ M ^ (∑ a, (w a).natAbs) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun a _ => norm_nonneg _)
  intro a _
  obtain ⟨h1, h2⟩ := h a
  rw [norm_zpow]
  rcases Int.natAbs_eq (w a) with hw | hw
  · conv_lhs => rw [hw]
    rw [zpow_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 _
  · conv_lhs => rw [hw]
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) h2 _

private theorem star_mulVec_dotProduct_mulVec_eq_conjTranspose {n : ℕ} (M N : Mt n) (v : Fin n → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (N *ᵥ (M *ᵥ v)) = star v ⬝ᵥ ((Mᴴ * N * M) *ᵥ v) := by
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

private theorem unit_lemma_5 {n : ℕ} {Hm v : Mt n} (h : vᴴ * Hm * v = Hm) (hH : Hm.det ≠ 0) : IsUnit v.det := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => hH ?_
  rw [← h1, h0, mul_zero]

theorem flowGS : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∀ (w : Fin n → ℤ) (e : Fin n → ℂ), star e ⬝ᵥ Hm.mulVec e = 0 → ∀ u ∈ Formalism.QuantumDeterminants.UH Hm, ∃ (C : ℝ) (A : ℕ), ∀ t : ℝ, 0 ≤ t → ∃ u' ∈ Formalism.QuantumDeterminants.UH Hm, ∃ b, UpT b ∧ (1 - (t : ℂ) • vecMulVec e (star e ᵥ* Hm)) * u * x₀ = u' * x₀ * b ∧ ‖∏ a, b a a ^ w a‖ ≤ C * (1 + t) ^ A ∧ ∀ i, ‖(u'⁻¹.mulVec e) i‖ ^ 2 * (1 + t) ≤ C := by
  intro n Hm q x₀ hx w e he u hu
  obtain ⟨_, hX⟩ := hx
  have hS : x₀ᴴ * Hm * x₀ = -sgnM n q := by
    rw [hX, sgnM, Matrix.diagonal_neg]
  have hSdet : (sgnM n q).det ≠ 0 := by
    rw [sgnM, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro a _
    show ((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ) ≠ 0
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
  have hd : (x₀ᴴ * Hm * x₀).det ≠ 0 := by
    rw [hS, Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hSdet
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hd)
  have hHdet : Hm.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hd)
  have hxHu : IsUnit x₀ᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hxu.star
  have hXu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det x₀).mpr hxu
  have hXHu : IsUnit x₀ᴴ := (Matrix.isUnit_iff_isUnit_det _).mpr hxHu
  have hSH : (sgnM n q)ᴴ = sgnM n q := by
    rw [sgnM, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    first
    | exact Complex.conj_ofReal _
    | simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  have hHH : Hmᴴ = Hm := by
    have h1 : x₀ᴴ * Hmᴴ * x₀ = x₀ᴴ * Hm * x₀ := by
      have h2 := congrArg Matrix.conjTranspose hS
      rw [Matrix.conjTranspose_neg, hSH, ← hS] at h2
      rw [← h2]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    exact hXHu.mul_left_cancel (hXu.mul_right_cancel h1)
  have hu' : uᴴ * Hm * u = Hm := hu
  have huu : IsUnit u.det := unit_lemma_5 hu' hHdet
  obtain ⟨f, hf⟩ : ∃ f : Fin n → ℂ, f = u⁻¹ *ᵥ e := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y : Fin n → ℂ, y = x₀⁻¹ *ᵥ f := ⟨_, rfl⟩
  have huf : u *ᵥ f = e := by rw [hf, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ huu, Matrix.one_mulVec]
  have hxy : x₀ *ᵥ y = f := by rw [hyd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hxu, Matrix.one_mulVec]
  have hSy : star y ⬝ᵥ (sgnM n q).mulVec y = 0 := by
    have hS' : sgnM n q = -(x₀ᴴ * Hm * x₀) := by rw [hS, neg_neg]
    rw [hS', Matrix.neg_mulVec, dotProduct_neg, ← star_mulVec_dotProduct_mulVec_eq_conjTranspose, hxy, ← hu', ← star_mulVec_dotProduct_mulVec_eq_conjTranspose, huf, he, neg_zero]
  obtain ⟨M, hM⟩ : ∃ M : Mt n, M = u * x₀ := ⟨_, rfl⟩
  have hMM : Mᴴ * (Hm * M) = -sgnM n q := by
    have h0 : x₀ᴴ * (uᴴ * Hm * u) * x₀ = -sgnM n q := by rw [hu', hS]
    rw [hM, ← h0]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hMMl : Mᴴ * Hm * M = -sgnM n q := by rw [Matrix.mul_assoc]; exact hMM
  have hMy : M *ᵥ y = e := by rw [hM, ← Matrix.mulVec_mulVec, hxy, huf]
  have he' : (star e ᵥ* Hm) ⬝ᵥ e = 0 := by rw [← Matrix.dotProduct_mulVec]; exact he
  have hVe : vecMulVec e (star e ᵥ* Hm) *ᵥ e = 0 := by
    rw [Matrix.vecMulVec_mulVec, he', MulOpposite.op_zero, zero_smul]
  have hVH : (vecMulVec e (star e ᵥ* Hm))ᴴ = vecMulVec (Hm *ᵥ e) (star e) := by
    rw [Matrix.conjTranspose_vecMulVec, Matrix.star_vecMul, star_star, hHH]
  have h1 : (vecMulVec e (star e ᵥ* Hm))ᴴ * Hm = vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) := by
    rw [hVH, Matrix.vecMulVec_mul]
  have h2 : Hm * vecMulVec e (star e ᵥ* Hm) = vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) := Matrix.mul_vecMulVec _ _ _
  have h3 : (vecMulVec e (star e ᵥ* Hm))ᴴ * (Hm * vecMulVec e (star e ᵥ* Hm)) = 0 := by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec, he', MulOpposite.op_zero, zero_smul,
      Matrix.zero_vecMulVec]
  have expand : ∀ (c : ℂ) (P Q : Mt n),
      (1 - c • P) * Hm * (1 - c • Q) = Hm - c • (Hm * Q) - c • (P * Hm) + (c * c) • (P * (Hm * Q)) := by
    intro c P Q
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
      Matrix.mul_assoc]
    abel
  have ha : Mᴴ *ᵥ (Hm *ᵥ e) = -(sgnM n q *ᵥ y) := by
    rw [← hMy]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hMM, Matrix.neg_mulVec]
  have hb : star e ᵥ* Hm ᵥ* M = -(star y ᵥ* sgnM n q) := by
    rw [← hMy, Matrix.star_mulVec]
    simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
    rw [hMM, Matrix.vecMul_neg]
  have hMW : Mᴴ * vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) * M = vecMulVec (-(sgnM n q *ᵥ y)) (-(star y ᵥ* sgnM n q)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ha, hb]
  refine ⟨(1 + 2 * ∑ c, ‖y c‖ ^ 2) ^ (∑ a, (w a).natAbs) + ∑ i, (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1),
    ∑ a, (w a).natAbs, ?_⟩
  intro t ht
  obtain ⟨b, hbU, hbS, hbd, hby⟩ := core n q y hSy t ht
  have hbdet : b.det ≠ 0 := by unfold UpT at hbU; exact hbU.1
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr hbdet
  obtain ⟨Z, hZ⟩ : ∃ Z : Mt n, Z = x₀ * b := ⟨_, rfl⟩
  have hZu : IsUnit Z.det := by rw [hZ, Matrix.det_mul]; exact hxu.mul hbu
  have hZHu : IsUnit Zᴴ.det := by rw [Matrix.det_conjTranspose]; exact hZu.star
  obtain ⟨G, hGd⟩ : ∃ G : Mt n, G = 1 - (t : ℂ) • vecMulVec e (star e ᵥ* Hm) := ⟨_, rfl⟩
  have hct : star (t : ℂ) = t := Complex.conj_ofReal t
  have hGe : G *ᵥ e = e := by
    rw [hGd, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hVe, smul_zero, sub_zero]
  have h2t : ((2 * t : ℝ) : ℂ) = (t : ℂ) + (t : ℂ) := by push_cast; ring
  have hGHG : Gᴴ * Hm * G = Hm - ((2 * t : ℝ) : ℂ) • vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) := by
    rw [hGd, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hct, expand, h3, smul_zero,
      add_zero, h2, h1, h2t, add_smul, sub_sub]
  have hKK : (G * M)ᴴ * Hm * (G * M) =
      -(sgnM n q + ((2 * t : ℝ) : ℂ) • vecMulVec (sgnM n q *ᵥ y) (star y ᵥ* sgnM n q)) := by
    calc (G * M)ᴴ * Hm * (G * M) = Mᴴ * (Gᴴ * Hm * G) * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * Hm * M - ((2 * t : ℝ) : ℂ) • (Mᴴ * vecMulVec (Hm *ᵥ e) (star e ᵥ* Hm) * M) := by
          rw [hGHG, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by
          rw [hMMl, hMW, Matrix.neg_vecMulVec, Matrix.vecMulVec_neg, neg_neg]
          abel
  have hZZ : Zᴴ * Hm * Z = -(sgnM n q + ((2 * t : ℝ) : ℂ) • vecMulVec (sgnM n q *ᵥ y) (star y ᵥ* sgnM n q)) := by
    rw [← hbS]
    calc Zᴴ * Hm * Z = bᴴ * (x₀ᴴ * Hm * x₀) * b := by
          rw [hZ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hS, mul_neg, neg_mul]
  have hKZ : (G * M)ᴴ * Hm * (G * M) = Zᴴ * Hm * Z := hKK.trans hZZ.symm
  obtain ⟨U, hUd⟩ : ∃ U : Mt n, U = G * M * Z⁻¹ := ⟨_, rfl⟩
  have hUH : Uᴴ * Hm * U = Hm := by
    calc Uᴴ * Hm * U = Z⁻¹ᴴ * ((G * M)ᴴ * Hm * (G * M)) * Z⁻¹ := by
          rw [hUd]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Z⁻¹ᴴ * (Zᴴ * Hm * Z) * Z⁻¹ := by rw [hKZ]
      _ = Hm := by
          rw [Matrix.conjTranspose_nonsing_inv]
          simp only [Matrix.mul_assoc]
          rw [Matrix.mul_nonsing_inv _ hZu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hZHu]
  have hUu : IsUnit U.det := unit_lemma_5 hUH hHdet
  have hUxb : U * x₀ * b = G * M := by
    rw [hUd, Matrix.mul_assoc (G * M * Z⁻¹) x₀ b, ← hZ, Matrix.nonsing_inv_mul_cancel_right _ _ hZu]
  obtain ⟨v, hvd⟩ : ∃ v : Fin n → ℂ, v = x₀ *ᵥ (b *ᵥ y) := ⟨_, rfl⟩
  have hUv : U *ᵥ v = e := by
    rw [hvd, Matrix.mulVec_mulVec y x₀ b, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hUxb, ← Matrix.mulVec_mulVec,
      hMy, hGe]
  have hinv : U⁻¹ *ᵥ e = v := by
    rw [← hUv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mulVec]
  have hC2 : 0 ≤ ∑ i, (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) := by positivity
  have hC1 : 0 ≤ (1 + 2 * ∑ c, ‖y c‖ ^ 2) ^ (∑ a, (w a).natAbs) := by positivity
  refine ⟨U, hUH, b, hbU, ?_, ?_, ?_⟩
  · rw [← hGd, hUxb, hM, Matrix.mul_assoc]
  · refine (prod_zpow_le (fun a => b a a) w ((1 + 2 * ∑ c, ‖y c‖ ^ 2) * (1 + t)) hbd).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC2) (pow_nonneg (by linarith) _)
  · intro i
    rw [hinv]
    have hvi : v i = ∑ j, x₀ i j * (b *ᵥ y) j := by rw [hvd]; rfl
    have hn1 : ‖v i‖ ≤ ∑ j, ‖x₀ i j‖ * ‖(b *ᵥ y) j‖ := by
      rw [hvi]; exact (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_mul]))
    have hn2 : ‖v i‖ ^ 2 ≤ (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, ‖(b *ᵥ y) j‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) hn1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    have hn3 : (∑ j, ‖(b *ᵥ y) j‖ ^ 2) * (1 + t) ≤ ∑ j, (‖y j‖ ^ 2 + 1) := by
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => hby j
    have hn4 : (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) ≤ ∑ i, (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) :=
      Finset.single_le_sum (f := fun i => (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1))
        (fun i _ => show (0 : ℝ) ≤ (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) by positivity) (Finset.mem_univ i)
    have hX0 : 0 ≤ ∑ j, ‖x₀ i j‖ ^ 2 := by positivity
    calc ‖v i‖ ^ 2 * (1 + t) ≤ (∑ j, ‖x₀ i j‖ ^ 2) * (∑ j, ‖(b *ᵥ y) j‖ ^ 2) * (1 + t) :=
          mul_le_mul_of_nonneg_right hn2 (by linarith)
      _ = (∑ j, ‖x₀ i j‖ ^ 2) * ((∑ j, ‖(b *ᵥ y) j‖ ^ 2) * (1 + t)) := by ring
      _ ≤ (∑ j, ‖x₀ i j‖ ^ 2) * ∑ j, (‖y j‖ ^ 2 + 1) := mul_le_mul_of_nonneg_left hn3 hX0
      _ ≤ _ := hn4.trans (le_add_of_nonneg_left hC1)

end GlobalTheory.HolDict.FlowGS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionCuspidalOfRapidDecayHolomorphicType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlowInvSplit
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem flowInv_herm {n : ℕ} {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : Hmᴴ = Hm := by
  obtain ⟨-, hD⟩ := h
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have huH : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [det_conjTranspose]
    exact (star_ne_zero).mpr hdet
  have hself : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    funext a
    simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc] at hself
  exact huH.mul_right_injective (hu.mul_left_injective hself)

theorem flowInv_sq {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0) :
    vecMulVec e (star e ᵥ* Hm) * vecMulVec e (star e ᵥ* Hm) = 0 := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, he, zero_smul]
  ext i j
  simp [vecMulVec_apply]

theorem flowInv_adj {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) (e : Fin n → ℂ) :
    (vecMulVec e (star e ᵥ* Hm))ᴴ * Hm = Hm * vecMulVec e (star e ᵥ* Hm) := by
  rw [conjTranspose_vecMulVec, star_vecMul, star_star, hH, vecMulVec_mul, mul_vecMulVec]

private theorem one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (a b : ℂ) : (1 - (b - a) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      (1 + a • vecMulVec e (star e ᵥ* Hm)) * (1 - b • vecMulVec e (star e ᵥ* Hm)) := by
  have hS := flowInv_sq he
  rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, hS, smul_zero, smul_zero, sub_zero,
    sub_smul]
  abel

theorem flowInv_mem {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (s : ℝ) : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm *
    (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)) = Hm
  have hc : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
    simp [Complex.conj_ofReal]
  have h1 : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm =
      Hm * (1 + (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm)) := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, add_mul, one_mul, smul_mul_assoc,
      flowInv_adj hH e, hc, mul_add, mul_one, mul_smul_comm]
  have h2 := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic he (-((s : ℂ) * Complex.I)) (-((s : ℂ) * Complex.I))
  have h3 : (1 - (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) := by
    rw [neg_smul, sub_neg_eq_add]
  rw [sub_self, zero_smul, sub_zero, h3] at h2
  rw [h1, Matrix.mul_assoc, ← h2, mul_one]

private theorem mul_mem_uh {n : ℕ} {Hm g₁ g₂ : Mt n} (h₁ : g₁ ∈ Formalism.QuantumDeterminants.UH Hm) (h₂ : g₂ ∈ Formalism.QuantumDeterminants.UH Hm) :
    g₁ * g₂ ∈ Formalism.QuantumDeterminants.UH Hm := by
  change g₁ᴴ * Hm * g₁ = Hm at h₁
  change g₂ᴴ * Hm * g₂ = Hm at h₂
  show (g₁ * g₂)ᴴ * Hm * (g₁ * g₂) = Hm
  rw [conjTranspose_mul]
  calc g₂ᴴ * g₁ᴴ * Hm * (g₁ * g₂) = g₂ᴴ * (g₁ᴴ * Hm * g₁) * g₂ := by simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h₁, h₂]

theorem flowInv : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (P : (ι → Fin n → Fin n → ℂ) → ℂ) (e : ι → Fin n → ℂ), (∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) → HolSec Hm q w P → (∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, P (fun τ => (m τ * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n))) → ∀ u ∈ UG Hm, ∀ t : ℝ, 0 ≤ t → P (fun τ => ((1 - (t : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n)) := by
  intro n ι _ _ Hm q x₀ w hO P e he hP hInv u hu t ht
  have hH : ∀ τ, (Hm τ)ᴴ = Hm τ := fun τ => flowInv_herm (hO τ)
  have hu' : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := hu
  obtain ⟨hOpen, -, hStab, hBase⟩ := frDoms_open_preconnected_stable n ι Hm q x₀ hO
  let X : ℂ → (ι → Fin n → Fin n → ℂ) := fun z τ =>
    ((1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)
  have hXaff : X = fun z τ i j => (u τ * x₀ τ) i j - z * (vecMulVec (e τ) (star (e τ) ᵥ* Hm τ) * u τ * x₀ τ) i j := by
    funext z τ i j
    simp only [X, sub_mul, one_mul, smul_mul_assoc, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hXd : Differentiable ℂ X := by
    rw [hXaff]
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
    exact (differentiable_const _).sub (differentiable_id.mul (differentiable_const _))
  have hHU : {z : ℂ | 0 ≤ z.re} ⊆ X ⁻¹' frDoms Hm q := by
    intro z hz
    have hGS := fun τ => FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hO τ) (w τ) (e τ) (he τ) (u τ) (hu' τ)
    choose C A hCA using hGS
    choose u' hu' b hbf using fun τ => hCA τ z.re hz
    have hmem := hStab (fun τ => (1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ)
      (show ∀ τ, _ ∈ Formalism.QuantumDeterminants.UH (Hm τ) from fun τ => mul_mem_uh (flowInv_mem (hH τ) (he τ) (-z.im)) (hu' τ)) b (fun τ => (hbf τ).1)
      (fun τ => (x₀ τ : Mt n)) hBase
    suffices hXz : X z = fun τ => ((1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ * x₀ τ * b τ : Mt n) by
      show X z ∈ frDoms Hm q
      rw [hXz]
      exact hmem
    funext τ
    have hfac := (hbf τ).2.1
    have hsplit := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic (he τ) (((-z.im : ℝ) : ℂ) * Complex.I) (z.re : ℂ)
    have hz' : (z.re : ℂ) - ((-z.im : ℝ) : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    rw [hz'] at hsplit
    show (1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = _
    simp only [Matrix.mul_assoc] at hfac ⊢
    rw [hsplit, Matrix.mul_assoc, hfac]
  let f : ℂ → ℂ := fun z => P (X z)
  have hfU : DifferentiableOn ℂ f (X ⁻¹' frDoms Hm q) :=
    hP.1.comp hXd.differentiableOn fun z hz => hz
  have hUo : IsOpen (X ⁻¹' frDoms Hm q) := hOpen.preimage hXd.continuous
  have h0 : (0 : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simp
  have hVo := hUo.connectedComponentIn (x := (0 : ℂ))
  have hHV := (convex_halfSpace_re_ge (0 : ℝ)).isPreconnected.subset_connectedComponentIn h0 hHU
  have hfV : AnalyticOnNhd ℂ f (connectedComponentIn (X ⁻¹' frDoms Hm q) 0) :=
    (hfU.mono (connectedComponentIn_subset _ _)).analyticOnNhd hVo
  have eX0 : X 0 = fun τ => (u τ * x₀ τ : Mt n) := by
    funext τ
    show (1 - (0 : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = u τ * x₀ τ
    rw [zero_smul, sub_zero, one_mul]
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = (fun _ => f 0) z := by
    have hT : Filter.Tendsto (fun s : ℝ => (s : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Continuous (fun s : ℝ => (s : ℂ) * Complex.I) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hs) Complex.I_ne_zero
    apply hT.frequently
    refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun s => ?_)
    have h1 := hInv (fun τ => 1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ))
      (fun τ => by unfold InZe; exact ⟨-s, rfl⟩) u hu
    have eX : X ((s : ℂ) * Complex.I) =
        fun τ => ((1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n) := by
      funext τ
      simp only [X]
      congr 2
      push_cast
      simp only [neg_mul, neg_smul, sub_eq_add_neg]
    show P (X ((s : ℂ) * Complex.I)) = P (X 0)
    rw [eX, eX0]
    exact h1
  have hEq := hfV.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_connectedComponentIn (mem_connectedComponentIn (hHU h0)) hfreq
  have ht' : (t : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simpa using ht
  have key : f t = f 0 := hEq (hHV ht')
  show f t = _
  rw [key]
  show P (X 0) = _
  rw [eX0]

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionCuspidalOfRapidDecayHolomorphicType
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.ZDecay

theorem eq_zero_of_le_div {x K T : ℝ} (hx : 0 ≤ x) (h : ∀ t : ℝ, T ≤ t → 0 ≤ t → x * (1 + t) ≤ K) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have h1 := h (max (max T 0) (K / x)) ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _))
  have h2 : K / x ≤ max (max T 0) (K / x) := le_max_right _ _
  have h3 : x * (K / x) = K := mul_div_cancel₀ _ hne
  nlinarith

theorem holFn_eq_zero {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n}
    {w : ι → Fin n → ℤ} (hx : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {e : ι → Fin n → ℂ}
    (he : ∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f)
    (hinv : ∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, m * u ∈ UG Hm ∧ f (m * u) = f u)
    (hdec : ∀ k : ℕ, ∃ K : ℝ, ∀ u ∈ UG Hm, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((u τ)⁻¹.mulVec (e τ)) i‖ ≤ δ) →
      ‖f u‖ ≤ K * δ ^ k) :
    ∀ u ∈ UG Hm, f u = 0 := by
  intro u hu
  obtain ⟨P, hP, hfP⟩ := hf
  have hflow := GlobalTheory.HolDict.flowInv n ι Hm q x₀ w hx P e he hP (fun m hm v hv => by
    obtain ⟨h1, h2⟩ := hinv m hm v hv
    rw [hfP _ h1, hfP _ hv] at h2
    exact h2) u hu
  choose C A hCA using fun τ => GlobalTheory.HolDict.FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hx τ) (w τ) (e τ) (he τ) (u τ) (hu τ)
  have hC0 : ∀ τ, 0 ≤ C τ := fun τ => by
    obtain ⟨u', -, b, -, -, h, -⟩ := hCA τ 0 le_rfl
    have := (norm_nonneg _).trans h
    simpa using this
  obtain ⟨K, hK⟩ := hdec (2 * (∑ τ, A τ + 1))
  obtain ⟨-, -, hst, hbase⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ hx
  set C' : ℝ := ∑ τ, C τ + 1 with hC'
  have hCs : 0 ≤ ∑ τ, C τ := Finset.sum_nonneg fun τ _ => hC0 τ
  have hC'pos : 0 < C' := by linarith
  have hCle : ∀ τ, C τ ≤ C' := fun τ => by
    have := Finset.single_le_sum (f := C) (fun τ _ => hC0 τ) (Finset.mem_univ τ)
    linarith
  rw [← norm_eq_zero]
  refine eq_zero_of_le_div (K := (∏ τ, C τ) * K * C' ^ (∑ τ, A τ + 1)) (T := C') (norm_nonneg _) fun t hT ht => ?_
  choose u' hu' b hb hdecomp hchi hshort using fun τ => hCA τ t ht
  have ht1 : 0 < 1 + t := by linarith
  have hone : ∀ _ : ι, UpT (1 : Mt n) := fun _ => ⟨by simp, fun a c hc => Matrix.one_apply_ne hc.ne'⟩
  have hmem : (fun τ => (u' τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
    have := hst u' hu' (fun _ => 1) hone _ hbase
    simp only [Matrix.mul_one] at this
    exact this
  have h1 : f u = (∏ τ, ∏ a, b τ a a ^ w τ a) * f u' := by
    rw [hfP u hu, ← hflow t ht, hfP u' hu', ← hP.2 _ hmem b hb]
    congr 1
    funext τ
    exact hdecomp τ
  have hq : 0 < C' / (1 + t) := div_pos hC'pos ht1
  have h2 := hK u' hu' (Real.sqrt (C' / (1 + t))) (Real.sqrt_pos.2 hq)
    (Real.sqrt_le_one.2 ((div_le_one ht1).2 (by linarith))) fun τ i =>
      Real.le_sqrt_of_sq_le ((le_div_iff₀ ht1).2 ((hshort τ i).trans (hCle τ)))
  rw [pow_mul, Real.sq_sqrt hq.le] at h2
  have h3 : ‖∏ τ, ∏ a, b τ a a ^ w τ a‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => hchi τ
  have h4 : ‖f u‖ ≤ (∏ τ, C τ) * (1 + t) ^ (∑ τ, A τ) * (K * (C' / (1 + t)) ^ (∑ τ, A τ + 1)) := by
    rw [h1, norm_mul]
    exact mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)
  refine (mul_le_mul_of_nonneg_right h4 ht1.le).trans_eq ?_
  rw [div_pow, pow_succ (1 + t)]
  field_simp

theorem setIntegral_translate {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (hc : ∀ a b : G, a * b = b * a) (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ) (hF : ∀ γ ∈ Γ, ∀ z, F (γ * z) = F z) (z₀ : G) :
    ∫ z in 𝓕, F (z₀ * z) ∂μ = ∫ z in 𝓕, F z ∂μ := by
  have : SMulCommClass G Γ G := ⟨fun a γ z => by
    change a * ((γ : G) * z) = γ * (a * z)
    rw [← mul_assoc, hc a, mul_assoc]⟩
  have h2 := h𝓕.smul_of_comm z₀
  rw [h𝓕.setIntegral_eq h2 fun γ z => hF γ γ.2 z]
  exact ((measurePreserving_mul_left μ z₀).setIntegral_image_emb (measurableEmbedding_mulLeft z₀) F 𝓕).symm

theorem iso_tau {D : D7} {V : HSp D} {ξ : Fin V.rank → D.host.E} (hξ : IsoVec V ξ) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (ξ i)) ⬝ᵥ (gramAt D V τ).mulVec (fun i => tauE D τ (ξ i)) = 0 := by
  have hs : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := fun x => by
    have := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x
  have h := congrArg (tauE D τ) hξ.2
  rw [map_zero] at h
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, gramAt, Matrix.map_apply, Pi.star_apply]

theorem zCusp_of_rapidDecay : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  intro D θ V S M w hθ hM φ haut hhol hdec ξ hξ μ 𝓕 hμ h𝓕 g
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : BorelSpace (ZI V ξ) := Subtype.borelSpace (fun x => x ∈ (ZI V ξ : Set (GA D V)))
  have : Countable ((GQ V).subgroupOf (ZI V ξ)) :=
    Function.Injective.countable (f := fun γ : (GQ V).subgroupOf (ZI V ξ) => (⟨γ.1.1, γ.2⟩ : GQ V))
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  obtain ⟨L, hL, hLmul, -, hUG, hLa, -, hsplit, hcomm, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨⟨ε, -⟩, -, -, hlift, -⟩ := GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed D θ V hθ ξ hξ
  have hfin := ((GlobalTheory.T.transvectionSubgroup_cocompact_haar_fundamentalDomain D θ V hθ ξ hξ).2.1 μ 𝓕 hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have hc : ∀ a b : ZI V ξ, a * b = b * a := fun a b => by
    obtain ⟨a, rfl⟩ := ε.surjective a
    obtain ⟨b, rfl⟩ := ε.surjective b
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨a, ha, u, hu, rfl⟩ := hsplit g
  have hx : ∀ τ, OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) := fun τ => ((GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.2 hM).1
  obtain ⟨B, hB⟩ := hdec.bounded
  have hf : HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w
      fun v => ∫ z in 𝓕, φ ((z : GA D V) * a * L v) ∂μ := by
    refine GlobalTheory.T.integral_holomorphicTypeFamily_holomorphicType _ _ _ _ _ w hx (ZI V ξ) (μ.restrict 𝓕) (fun z v => φ ((z : GA D V) * a * L v)) B
      (fun z => ?_) (fun z v _ => hB _) fun v _ => ?_
    · obtain ⟨f, ⟨P, hP, hfP⟩, hφf⟩ := hhol ((z : GA D V) * a)
      refine ⟨P, hP, fun v hv => ?_⟩
      beta_reduce
      rw [hφf _ (hL v hv).1, ← hfP v hv]
      congr 1
      funext τ
      exact (hL v hv).2 τ
    · exact (haut.cont.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)).measurable.aestronglyMeasurable
  have key := holFn_eq_zero hx (iso_tau hξ) hf (fun m hm v hv => ?_) (fun k => ?_) _ (hUG u)
  · simp only [hLa u hu, mul_assoc] at key
    exact key
  · obtain ⟨z₀, hz₀, hz₁, hz₂⟩ := hlift m hm
    have hm' : m = fun τ => archM V (θ τ) z₀ := funext fun τ => (hz₂ τ).symm
    have hmU : m ∈ UG (gramAt D V) := hm' ▸ hUG z₀
    have hLm : L m = z₀ := by rw [hm']; exact hLa z₀ hz₁
    refine ⟨fun τ => GlobalTheory.PointAtPlaceHom.mul_mem_UH (hmU τ) (hv τ), ?_⟩
    rw [← setIntegral_translate hc _ μ h𝓕 (fun z => φ ((z : GA D V) * a * L v)) (fun γ hγ z => ?_) ⟨z₀, hz₀⟩]
    · refine integral_congr_ae (.of_forall fun z => ?_)
      have h1 := congrArg Subtype.val (hc ⟨z₀, hz₀⟩ z)
      simp only [Subgroup.coe_mul] at h1 ⊢
      rw [hLmul m hmU v hv, hLm, h1, mul_assoc (z : GA D V) z₀, ← hcomm a ha z₀ hz₁]
      simp only [mul_assoc]
    · simp only [Subgroup.coe_mul, mul_assoc]
      exact haut.left _ hγ _
  · obtain ⟨c, N, hc0, hh⟩ := GlobalTheory.T.quotientHeight_lower_bound_short_isotropic_vector D θ V hθ ξ hξ a ha
    obtain ⟨C, hC⟩ := hdec (N * k)
    refine ⟨C / c ^ k * (μ.restrict 𝓕).real Set.univ, fun v hv δ h0 h1 hs => ?_⟩
    rw [mul_right_comm]
    refine norm_integral_le_of_norm_le_const (.of_forall fun z => ?_)
    have h2 := hh z z.2 (L v) (hL v hv).1 δ h0 h1 fun τ i => by rw [(hL v hv).2 τ]; exact hs τ i
    have h3 := pow_le_pow_left₀ hc0.le h2 k
    rw [mul_pow, ← pow_mul] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc0 k)]
    calc _ ≤ ‖φ ((z : GA D V) * a * L v)‖ * (δ ^ k * _) := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (‖φ ((z : GA D V) * a * L v)‖ * _) * δ ^ k := by rw [mul_comm (δ ^ k), ← mul_assoc]
      _ ≤ C * δ ^ k := mul_le_mul_of_nonneg_right (hC _) (pow_nonneg h0.le _)

end GlobalTheory.HolDict.ZDecay

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionCuspidalOfRapidDecayHolomorphicTypeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionCuspidal_of_rapidDecay_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → ∀ φ : GA D V → ℂ, IsAutFun V φ → HolAd θ M w φ → GlobalTheory.CuspDecay.IsRapidDecay θ V φ → ZCusp V φ := by
  first | exact @GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay | exact GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay | (intros; apply GlobalTheory.HolDict.ZDecay.zCusp_of_rapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspFormOfExtremalVectorMultiplicity
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem holForm_zCusp_of_mem_mult : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, HolForm θ M w J χ (T v) ∧ ZCusp V (T v) := by
  intro hP D θ V S M w v hθ hM hw hv J χ T hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  have hd := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ (h.aut v) (h.cusp v)
  have hh := GlobalTheory.T.multiplicityMap_extremalVector_holomorphicType D θ V S M w v hθ hM hw hv J χ T h
  exact ⟨⟨(h.aut v).toIsAutFun, hd.bounded, h.lev v, hh⟩,
    GlobalTheory.T.transvectionCuspidal_of_rapidDecay_holomorphicType D θ V S M w hθ hM _ (h.aut v).toIsAutFun hh hd⟩

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspFormOfExtremalVectorMultiplicityStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_cusp_form_of_extremal_vector_multiplicity : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, HolForm θ M w J χ (T v) ∧ ZCusp V (T v) := by
  first | exact @GlobalTheory.HolDict.holForm_zCusp_of_mem_mult | exact GlobalTheory.HolDict.holForm_zCusp_of_mem_mult | (intros; apply GlobalTheory.HolDict.holForm_zCusp_of_mem_mult <;> assumption)
end
