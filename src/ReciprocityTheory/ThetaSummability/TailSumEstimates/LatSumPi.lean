module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ThetaSummability.TailSumEstimates.LatSumPi
namespace ReciprocityTheory.ThetaSummability.Est

open Module

theorem summable_and_tsum_pi_prod {α : Type*} {q : ℕ} (f : Fin q → α → ℝ)
    (hf0 : ∀ i a, 0 ≤ f i a) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : Fin q → α => ∏ i, f i (x i)) ∧
      ∑' x : Fin q → α, ∏ i, f i (x i) = ∏ i, ∑' a, f i a := by
  induction q with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact ⟨Summable.of_finite, by rw [tsum_const, Nat.card_unique, one_smul]⟩
  | succ q ih =>
    obtain ⟨hs, ht⟩ := ih (fun i => f i.succ) (fun i => hf0 i.succ) (fun i => hf i.succ)
    obtain ⟨e, he⟩ : ∃ e : α × (Fin q → α) ≃ (Fin (q + 1) → α),
        ∀ p, e p = (Fin.cons p.1 p.2 : Fin (q + 1) → α) :=
      ⟨Fin.consEquiv (fun _ : Fin (q + 1) => α), fun p => rfl⟩
    have key : ∀ p : α × (Fin q → α), ∏ i, f i (e p i) = f 0 p.1 * ∏ i, f i.succ (p.2 i) := by
      intro p
      rw [he, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hprod : Summable (fun p : α × (Fin q → α) => f 0 p.1 * ∏ i, f i.succ (p.2 i)) := by
      have h1 : (0 : α → ℝ) ≤ f 0 := Pi.le_def.mpr fun a => hf0 0 a
      have h2 : (0 : (Fin q → α) → ℝ) ≤ fun x => ∏ i, f i.succ (x i) :=
        Pi.le_def.mpr fun x => Finset.prod_nonneg fun i _ => hf0 _ _
      have hs0 : Summable (fun x : Fin q → α => ∏ i, f i.succ (x i)) := hs
      have hf00 : Summable (f 0) := hf 0
      have := Summable.mul_of_nonneg hf00 hs0 h1 h2
      exact this
    have hs' : Summable (fun p : α × (Fin q → α) => ∏ i, f i (e p i)) :=
      hprod.congr fun p => (key p).symm
    refine ⟨(e.summable_iff (f := fun x : Fin (q + 1) → α => ∏ i, f i (x i))).mp hs', ?_⟩
    calc ∑' x : Fin (q + 1) → α, ∏ i, f i (x i)
        = ∑' p : α × (Fin q → α), ∏ i, f i (e p i) := (e.tsum_eq (fun x => ∏ i, f i (x i))).symm
      _ = ∑' p : α × (Fin q → α), f 0 p.1 * ∏ i, f i.succ (p.2 i) := tsum_congr key
      _ = (∑' a, f 0 a) * ∑' x : Fin q → α, ∏ i, f i.succ (x i) := (Summable.tsum_mul_tsum (hf 0) hs hprod).symm
      _ = ∏ i, ∑' a, f i a := by rw [ht, Fin.prod_univ_succ]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

end ReciprocityTheory.ThetaSummability.Est
end

section -- merged from ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeExp
section -- merged from ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeChange
section -- merged from ReciprocityTheory.ThetaSummability.TailSumEstimates.ConeDefs
namespace ReciprocityTheory.ThetaSummability.Est

open Finset

def gap {r : ℕ} (x : Fin r → ℝ) (k : Fin r) : ℝ :=
  x k - (if h : k.val + 1 < r then x ⟨k.val + 1, h⟩ else 0)

def tailSum {r : ℕ} (y : Fin r → ℝ) (k : Fin r) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin r => k ≤ j), y j

def partialSum {r : ℕ} (s : Fin r → ℝ) (k : Fin r) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin r => i ≤ k), s i

def logCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  {x | ∀ k, c ≤ gap x k}

def lowerBox (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ici c)

def multCone (r : ℕ) (c : ℝ) : Set (Fin r → ℝ) :=
  {t | ∀ k : Fin r, (if h : k.val + 1 < r then c * t ⟨k.val + 1, h⟩ else c) ≤ t k}

end ReciprocityTheory.ThetaSummability.Est
end

namespace ReciprocityTheory.ThetaSummability.Est

open MeasureTheory Finset

variable {r : ℕ}

theorem tailSum_eq_add (y : Fin r → ℝ) (k : Fin r) :
    tailSum y k = y k + (if h : k.val + 1 < r then tailSum y ⟨k.val + 1, h⟩ else 0) := by
  have h1 : univ.filter (fun j : Fin r => k ≤ j) = insert k (univ.filter (fun j : Fin r => k < j)) := by
    ext j; simp [le_iff_eq_or_lt, eq_comm]
  unfold tailSum
  rw [h1, Finset.sum_insert (by simp)]
  congr 1
  split_ifs with h
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]; omega
  · apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hj; omega

theorem gap_tailSum (y : Fin r → ℝ) : gap (tailSum y) = y := by
  funext k
  unfold gap
  rw [tailSum_eq_add]
  split_ifs <;> ring

theorem tailSum_gap_apply (x : Fin r → ℝ) (k : Fin r) : tailSum (gap x) k = x k := by
  rw [tailSum_eq_add]
  split_ifs with h
  · rw [tailSum_gap_apply x ⟨k.val + 1, h⟩, gap, dite_eq_left h]; ring
  · rw [gap, dite_eq_right h]; ring
termination_by r - k.val
decreasing_by omega

theorem tailSum_gap (x : Fin r → ℝ) : tailSum (gap x) = x := funext (tailSum_gap_apply x)

def tailMat (r : ℕ) : Matrix (Fin r) (Fin r) ℝ := fun i j => if i ≤ j then 1 else 0

theorem tailMat_mulVec (y : Fin r → ℝ) : (tailMat r).mulVec y = tailSum y := by
  funext k
  simp [Matrix.mulVec, dotProduct, tailMat, tailSum, Finset.sum_filter, ite_mul]

theorem det_tailMat : (tailMat r).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [tailMat]
  · intro i j hij
    have : ¬ i ≤ j := not_le.mpr hij
    simp [tailMat, this]

theorem tailSum_eq_toLin' : (tailSum (r := r)) = ⇑(Matrix.toLin' (tailMat r)) := by
  funext y; rw [Matrix.toLin'_apply, tailMat_mulVec]

theorem continuous_tailSum : Continuous (tailSum (r := r)) := by
  rw [tailSum_eq_toLin']; exact LinearMap.continuous_of_finiteDimensional _

theorem continuous_gap : Continuous (gap (r := r)) := by
  refine continuous_pi fun k => ?_
  unfold gap
  split_ifs
  · exact (continuous_apply _).sub (continuous_apply _)
  · exact (continuous_apply _).sub continuous_const

theorem measurePreserving_tailSum :
    MeasurePreserving (tailSum (r := r)) volume volume := by
  refine ⟨continuous_tailSum.measurable, ?_⟩
  rw [tailSum_eq_toLin', Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · simp [LinearMap.det_toLin', det_tailMat]
  · simp [LinearMap.det_toLin', det_tailMat]

def tailSumEquiv (r : ℕ) : (Fin r → ℝ) ≃ᵐ (Fin r → ℝ) where
  toFun := tailSum
  invFun := gap
  left_inv := gap_tailSum
  right_inv := tailSum_gap
  measurable_toFun := continuous_tailSum.measurable
  measurable_invFun := continuous_gap.measurable

theorem measurableEmbedding_tailSum : MeasurableEmbedding (tailSum (r := r)) :=
  (tailSumEquiv r).measurableEmbedding

theorem tailSum_mem_logCone_iff (c : ℝ) (y : Fin r → ℝ) :
    tailSum y ∈ logCone r c ↔ y ∈ lowerBox r c := by
  simp [logCone, lowerBox, gap_tailSum, Pi.le_def]

theorem preimage_tailSum_logCone (c : ℝ) : tailSum ⁻¹' logCone r c = lowerBox r c := by
  ext y; exact tailSum_mem_logCone_iff c y

theorem integrableOn_logCone_iff (c : ℝ) (f : (Fin r → ℝ) → ℝ) :
    IntegrableOn f (logCone r c) ↔ IntegrableOn (fun y => f (tailSum y)) (lowerBox r c) := by
  rw [← preimage_tailSum_logCone c]
  exact (measurePreserving_tailSum.integrableOn_comp_preimage measurableEmbedding_tailSum).symm

end ReciprocityTheory.ThetaSummability.Est
end

namespace ReciprocityTheory.ThetaSummability.Est

open MeasureTheory Finset Real

variable {r : ℕ}

theorem sum_mul_tailSum (s y : Fin r → ℝ) :
    ∑ i, s i * tailSum y i = ∑ k, partialSum s k * y k := by
  simp only [tailSum, partialSum, Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem exp_sum_mul_tailSum_eq (s : Fin r → ℝ) :
    (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) =
      fun y => ∏ k, (fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t)) k (y k) := by
  funext y
  rw [sum_mul_tailSum, Real.exp_sum]

theorem integrableOn_exp_logCone (c : ℝ) {s : Fin r → ℝ} (hs : ∀ k, partialSum s k < 0) :
    IntegrableOn (fun x => exp (∑ i, s i * x i)) (logCone r c) := by
  rw [integrableOn_logCone_iff]
  show IntegrableOn (fun y : Fin r → ℝ => exp (∑ i, s i * tailSum y i)) (lowerBox r c)
  rw [exp_sum_mul_tailSum_eq, IntegrableOn, lowerBox, volume_pi, Measure.restrict_pi_pi]
  refine Integrable.fintype_prod (E := ℝ) (f := fun (k : Fin r) (t : ℝ) => exp (partialSum s k * t))
    (μ := fun _ => volume.restrict (Set.Ici c)) fun k => ?_
  show IntegrableOn (fun t : ℝ => exp (partialSum s k * t)) (Set.Ici c)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (hs k) c

end ReciprocityTheory.ThetaSummability.Est
end
