module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScMuExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScRefExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScXuExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiBuild
public import Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasWCore
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasInfXfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.BesselNVGapPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SplitPrimeCounts.LsSetresInt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.HJSumSmulRight
noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

def sg (ε : Fin n → Bool) (j : Fin n) : ℂ := if ε j then 1 else -1

theorem star_sg (ε : Fin n → Bool) (j : Fin n) : star (sg ε j) = sg ε j := by
  unfold sg; split_ifs <;> simp

theorem hJ_eq_sum (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    hJ ε x y = ∑ j, star (x j) * (sg ε j * y j) := by
  simp [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal, sg]

theorem hJ_conj (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  rw [hJ_eq_sum, hJ_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', star_mul', star_star, star_sg]; ring

theorem hJ_sub_left (ε : Fin n → Bool) (x x' y : Fin n → ℂ) :
    hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  simp only [hJ_eq_sum, Pi.sub_apply, star_sub, sub_mul, Finset.sum_sub_distrib]

theorem hJ_sub_right (ε : Fin n → Bool) (x y y' : Fin n → ℂ) :
    hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp only [hJ_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε (c • x) y = star c * hJ ε x y := by
  simp only [hJ_eq_sum, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hJ_smul_right (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem hJ_sum_smul_right (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (x : Fin n → ℂ) :
    hJ ε x (∑ b, g b • m b) = ∑ b, g b * hJ ε x (m b) := by
  simp only [hJ_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring

theorem hJ_sum_smul_left (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (m : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ a, g a • m a) y = ∑ a, star (g a) * hJ ε (m a) y := by
  simp only [hJ_eq_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, star_mul',
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by ring

theorem hJ_self (ε : Fin n → Bool) (x : Fin n → ℂ) :
    hJ ε x x = ((∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) : ℝ) : ℂ) := by
  rw [hJ_eq_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  unfold sg
  split_ifs <;> simp

theorem hJ_self_re (ε : Fin n → Bool) (x : Fin n → ℂ) :
    (hJ ε x x).re = ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (x j) := by
  rw [hJ_self]; exact Complex.ofReal_re _

theorem exists_rel {ι κ : Type*} [Fintype ι] [Fintype κ] (v : κ → ι → ℂ)
    (h : Fintype.card ι < Fintype.card κ) : ∃ g : κ → ℂ, ∑ j, g j • v j = 0 ∧ ∃ j, g j ≠ 0 := by
  apply Fintype.not_linearIndependent_iff.mp
  intro hli
  have := hli.fintype_card_le_finrank
  simp at this
  omega

theorem exists_perp (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (u : ι → Fin n → ℂ)
    (h : Fintype.card ι < n) : ∃ y : Fin n → ℂ, y ≠ 0 ∧ ∀ i, hJ ε (u i) y = 0 := by
  obtain ⟨g, hg, j, hj⟩ := exists_rel (fun (j : Fin n) (i : ι) => star (u i j) * sg ε j)
    (by simpa using h)
  refine ⟨g, fun h0 => hj (congrFun h0 j), fun i => ?_⟩
  have := congrFun hg i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  rw [hJ_eq_sum, ← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem re_star_mul_mul (a b : ℂ) : (star a * (a * b)).re = Complex.normSq a * b.re := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]; ring

end PI.ScPiFrameW
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeHW
noncomputable section

namespace Formalism.MainNotions.BridgeHW

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem highest_weight_exists_bis [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] : DiscreteSeriesWeylDimension.HighestWeightExists := Fact.out

variable {eps : ℝ} (Fm : FamP eps)



end Formalism.MainNotions.BridgeHW

end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPiFrame
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameHolds
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.FrameCore
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.PosOfPerp
noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

private theorem nonneg_term_lemma (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0) (i : Fin n) :
    0 ≤ (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
  cases hi : ε i
  · obtain ⟨k, hk⟩ := hσ i hi
    subst hk
    simp [hw0]
  · simp [Complex.normSq_nonneg]

private theorem pos_of_vanish_lemma_2 (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0)
    (hw : w ≠ 0) : 0 < (hJ ε w w).re := by
  rw [hJ_self_re]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  have hεi : ε i = true := by
    cases hj : ε i
    · obtain ⟨k, hk⟩ := hσ i hj
      exact (hi (by rw [← hk]; exact hw0 k)).elim
    · rfl
  calc (0 : ℝ) < (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
        rw [if_pos hεi, one_mul]
        exact Complex.normSq_pos.mpr hi
    _ ≤ ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (w j) :=
        Finset.single_le_sum (fun j _ => nonneg_term_lemma ε σ hσ w hw0 j) (Finset.mem_univ i)

theorem pos_of_perp (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (y : Fin n → ℂ) (hey : ∀ c, hJ ε (e c) y = 0) (hfy : ∀ c, hJ ε (f c) y = 0)
    (hzy : hJ ε z y = 0) (hy : y ≠ 0) : 0 < (hJ ε y y).re := by
  by_contra hcon
  have hle : (hJ ε y y).re ≤ 0 := not_lt.mp hcon
  obtain ⟨m, hm⟩ : ∃ m : Fin r ⊕ Bool → Fin n → ℂ,
      m = Sum.elim (fun a => e a - f a) (fun b => if b then y else z) := ⟨_, rfl⟩
  have hmi : ∀ a, m (Sum.inl a) = e a - f a := fun a => by rw [hm]; rfl
  have hmf : m (Sum.inr false) = z := by rw [hm]; rfl
  have hmt : m (Sum.inr true) = y := by rw [hm]; rfl
  obtain ⟨D, hD⟩ : ∃ D : Fin r ⊕ Bool → ℂ,
      D = Sum.elim (fun _ => (-2 : ℂ)) (fun b => if b then hJ ε y y else -(t : ℂ)) := ⟨_, rfl⟩
  have hDi : ∀ a, D (Sum.inl a) = -2 := fun a => by rw [hD]; rfl
  have hDf : D (Sum.inr false) = -(t : ℂ) := by rw [hD]; rfl
  have hDt : D (Sum.inr true) = hJ ε y y := by rw [hD]; rfl
  have hG : ∀ k l, hJ ε (m k) (m l) = if k = l then D k else 0 := by
    intro k l
    rcases k with a | i <;> rcases l with b | j
    · simp only [hmi, hJ_sub_left, hJ_sub_right, hee, hff, hef, hJ_conj ε (e b) (f a), hDi]
      by_cases hab : a = b
      · subst hab
        norm_num
      · simp [hab, Ne.symm hab]
    · cases j <;> simp [hmi, hmf, hmt, hJ_sub_left, hez, hfz, hey, hfy]
    · cases i <;> simp [hmi, hmf, hmt, hJ_sub_right, hJ_conj ε (e b) z, hJ_conj ε (f b) z,
        hJ_conj ε (e b) y, hJ_conj ε (f b) y, hez, hfz, hey, hfy]
    · cases i <;> cases j <;> simp [hmf, hmt, hDf, hDt, hzz, hzy, hJ_conj ε z y]
  obtain ⟨g, hg, k0, hk0⟩ := exists_rel (fun k : Fin r ⊕ Bool => fun j : Fin (r + 1) => m k (σ j))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]; omega)
  obtain ⟨v, hv⟩ : ∃ v : Fin n → ℂ, v = ∑ k, g k • m k := ⟨_, rfl⟩
  have hv0 : ∀ j, v (σ j) = 0 := by
    intro j
    have h := congrFun hg j
    rw [hv]
    simpa [Finset.sum_apply] using h
  have hvv : (hJ ε v v).re = ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [hv, hJ_sum_smul_left, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hJ_sum_smul_right]
    simp only [hG, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact re_star_mul_mul _ _
  have hterm : ∀ k, Complex.normSq (g k) * (D k).re ≤ 0 := by
    intro k
    refine mul_nonpos_iff.mpr (Or.inl ⟨Complex.normSq_nonneg _, ?_⟩)
    rcases k with a | b
    · rw [hDi]
      norm_num
    · cases b
      · rw [hDf]
        simp [ht.le]
      · rw [hDt]
        exact hle
  have hsum : 0 ≤ ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [← hvv, hJ_self_re]
    exact Finset.sum_nonneg fun i _ => nonneg_term_lemma ε σ hσ v hv0 i
  have hzero : ∀ k, Complex.normSq (g k) * (D k).re = 0 := by
    have h0 : ∑ k, Complex.normSq (g k) * (D k).re = 0 :=
      le_antisymm (Finset.sum_nonpos fun k _ => hterm k) hsum
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).mp h0 k (Finset.mem_univ k)
  have hga : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    simpa [hDi] using hzero (Sum.inl a)
  have hgf : g (Sum.inr false) = 0 := by
    simpa [hDf, ht.ne'] using hzero (Sum.inr false)
  have hvy : v = g (Sum.inr true) • y := by
    rw [hv, Fintype.sum_sum_type, Fintype.sum_bool]
    simp [hga, hgf, hmt]
  have hgt : g (Sum.inr true) ≠ 0 := by
    rcases k0 with a | b
    · exact absurd (hga a) hk0
    · cases b
      · exact absurd hgf hk0
      · exact hk0
  have hy0 : ∀ j, y (σ j) = 0 := by
    intro j
    have h := hv0 j
    rw [hvy, Pi.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hgt
  exact hcon (pos_of_vanish_lemma_2 ε σ hσ y hy0 hy)

end PI.ScPiFrameW
end
end

noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

theorem gs_step (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (m : ℕ) (hm : m < k) (w : Fin m → Fin n → ℂ)
    (hwo : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hwp : ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0) :
    ∃ w' : Fin (m + 1) → Fin n → ℂ, (∀ a b, hJ ε (w' a) (w' b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w' a) = 0 ∧ hJ ε (f c) (w' a) = 0) ∧ hJ ε z (w' a) = 0 := by
  obtain ⟨y, hy, hperp⟩ := exists_perp ε
    (Sum.elim e (Sum.elim f (Sum.elim (fun _ : Unit => z) w)))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega)
  have hey : ∀ c, hJ ε (e c) y = 0 := fun c => hperp (Sum.inl c)
  have hfy : ∀ c, hJ ε (f c) y = 0 := fun c => hperp (Sum.inr (Sum.inl c))
  have hzy : hJ ε z y = 0 := hperp (Sum.inr (Sum.inr (Sum.inl ())))
  have hwy : ∀ a, hJ ε (w a) y = 0 := fun a => hperp (Sum.inr (Sum.inr (Sum.inr a)))
  have hs0 : 0 < (hJ ε y y).re :=
    pos_of_perp ε σ hσ e f z t ht hee hff hef hez hfz hzz y hey hfy hzy hy
  obtain ⟨s, hs_eq⟩ : ∃ s : ℝ, s = (hJ ε y y).re := ⟨_, rfl⟩
  have hs : 0 < s := hs_eq ▸ hs0
  have hyy : hJ ε y y = (s : ℂ) := by
    rw [hs_eq, hJ_self, Complex.ofReal_re]
  have hμ : star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * hJ ε y y) = 1 := by
    rw [hyy, show star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) = (starRingEnd ℂ) (((Real.sqrt s)⁻¹ : ℝ) : ℂ)
      from rfl, Complex.conj_ofReal]
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have h1 : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ hs.ne']
    exact_mod_cast h1
  refine ⟨Fin.cons ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) • y) w, ?_, ?_⟩
  · intro a b
    refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b
    · rw [if_pos rfl]
      simp only [Fin.cons_zero, hJ_smul_left, hJ_smul_right]
      rw [mul_left_comm]
      exact hμ
    · rw [if_neg (Fin.succ_ne_zero b').symm]
      simp only [Fin.cons_zero, Fin.cons_succ, hJ_smul_left, hJ_conj ε (w b') y, hwy, star_zero,
        mul_zero]
    · rw [if_neg (Fin.succ_ne_zero a')]
      simp only [Fin.cons_zero, Fin.cons_succ, hJ_smul_right, hwy, mul_zero]
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact hwo a' b'
  · intro a
    refine Fin.cases ?_ (fun a' => ?_) a
    · simp [hJ_smul_right, hey, hfy, hzy]
    · simp only [Fin.cons_succ]
      exact hwp a'

theorem frame_core (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
  have key : ∀ m, m ≤ k → ∃ w : Fin m → Fin n → ℂ,
      (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨w, h1, h2⟩ := ih (by omega)
      exact gs_step ε hn σ hσ e f z t ht hee hff hef hez hfz hzz m (by omega) w h1 h2
  exact key k le_rfl

end PI.ScPiFrameW
end
end

noncomputable section

namespace PI.ScPiFrameW

open PI.ScPiExists

theorem frame_holds : PI.ScPiExists.Frame := by
  intro I r k e f z hn hfr ⟨t, ht, hzz⟩ hε v
  obtain ⟨hee, hff, hef, hz⟩ := hfr
  have hσ : ∃ σ : Fin (r + 1) → Fin I.n, ∀ i, I.ε v i = false → ∃ j, σ j = i := by
    refine ⟨fun j => ⟨min ((k - 1) + 2 * j.val + 1) (I.n - 1), by omega⟩, ?_⟩
    intro i hi
    rw [hε v i] at hi
    have h2 : ¬ i.val < k - 1 ∧ (i.val - (k - 1)) % 2 ≠ 0 := by
      by_cases h1 : i.val < k - 1
      · simp [h1] at hi
      · simp [h1] at hi
        exact ⟨h1, by omega⟩
    have hi' := i.isLt
    refine ⟨⟨(i.val - (k - 1)) / 2, by omega⟩, ?_⟩
    apply Fin.ext
    show min ((k - 1) + 2 * ((i.val - (k - 1)) / 2) + 1) (I.n - 1) = i.val
    omega
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨w, hw1, hw2⟩ := frame_core (I.ε v) hn σ hσ (fun a => rv I v (e a))
    (fun a => rv I v (f a)) (rv I v z) (t : ℝ) (by exact_mod_cast ht)
    (fun a b => by rw [hJ_rv, hee a b, map_zero]) (fun a b => by rw [hJ_rv, hff a b, map_zero])
    (fun a b => by rw [hJ_rv, hef a b]; split_ifs <;> simp)
    (fun a => by rw [hJ_rv, (hz a).1, map_zero]) (fun a => by rw [hJ_rv, (hz a).2, map_zero])
    (by rw [hJ_rv, hzz]; simp)
  exact ⟨w, hw1, hw2⟩

end PI.ScPiFrameW
end
end

theorem sc_pi_frame : PI.ScPiExists.Frame := PI.ScPiFrameW.frame_holds
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScPsiExists
theorem sc_psi_exists : PI.ScPsiExists.Target :=
  PI.ScPsiExists.UnitaryGroupMassFormula.norm_units_of_calculation
end

namespace Formalism.L2.SG.Closed.ScPsi

theorem chkScPsiExists (h : PI.ScPsiExists.Target) (D : Formalism.BasicNotions.D7) :
    Formalism.L2.SG.SplitPrimeNormLemmas.PsiExists D := by
  intro A
  obtain ⟨p, h1, h2, h3⟩ := h A.I
  exact ⟨⟨p, h1, h2, h3⟩⟩

end Formalism.L2.SG.Closed.ScPsi

namespace Formalism.L2.SG.Closed.ScGap

end Formalism.L2.SG.Closed.ScGap

namespace Formalism.L2.SG.Closed.ScMu

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScMu

theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

theorem chkScMuExists (h : PI.ScMuExists.Target) (D : D7) : MuExists D := by
  intro A L
  have key : ∀ u, ∃ muN muH nuQ : Measure A.I.Ginf,
      IsHaarOnSet A.I (Ninf A.I (eC A L) (zC A L u)) muN ∧
      IsHaarOnSet A.I (Hset A.I (Set.range (eC A L) ∪ Set.range (fC A L) ∪ {zC A L u})) muH ∧
      IsQuotMeasS A.I (((muN.prod muH).map (fun p => p.1 * p.2))) nuQ := by
    intro u
    refine h A.I D.R.rS (eC A L) (fC A L) (zC A L u) ?_ ?_ ?_ ?_ ?_
    · intro a b; simp only [eC, hform_eq, L.ee, map_zero]
    · intro a b; simp only [fC, hform_eq, L.ff, map_zero]
    · intro a b; simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp
    · intro a; simp only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self]
    · simp only [zC, hform_eq, L.zu_norm]
      intro h0
      have h1 := congrArg A.ιE h0
      simp only [RingEquiv.apply_symm_apply, map_zero, neg_eq_zero, Nat.cast_eq_zero] at h1
      have h2 := D.T_mod_g u 0
      rw [h1] at h2
      simp at h2
  choose muN muH nuQ hN hH hQ using key
  exact ⟨⟨muN, muH, hN, hH, nuQ, hQ⟩⟩

end ChkScMu
end

end Formalism.L2.SG.Closed.ScMu

namespace Formalism.L2.SG.Closed.ScRef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScRef

theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

def SplitAtG (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.F)), ((gD D : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal →
    Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.E) //
      w.asIdeal.comap (algebraMap (𝓞 A.I.F) (𝓞 A.I.E)) = v.asIdeal} = 2

def IntAtG (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (a : Fin D.R.rS),
    InAt A.I (gD D) 1 (incl A.I (eC A L a)) ∧ InAt A.I (gD D) 1 (incl A.I (fC A L a))

theorem chkScRefExists (h : PI.ScRefExists.Target) (D : D7) (hs : SplitAtG D) (hi : IntAtG D) :
    RefExists D := by
  intro A L
  have hn : A.I.n = 2 * D.R.rS + D.R.k + 1 := A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm
  have hg : 1 ≤ gD D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨P⟩ := h A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) hg (hs A) hn
    (fun a b => by simp only [eC, hform_eq, L.ee, map_zero])
    (fun a b => by simp only [fC, hform_eq, L.ff, map_zero])
    (fun a b => by simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp)
    (hi A L)
  exact ⟨{ e0 := P.e0
           f0 := P.f0
           z0 := P.z0
           bw := P.bw
           bwd := P.bwd
           ew := P.ew
           vectorsInLattice := P.vectorsInLattice
           basisApprox := P.basisApprox
           gramIntegral := P.gramIntegral
           formsAtZero := P.formsAtZero
           weightVectorsIntegral := P.weightVectorsIntegral
           ew_idem := P.ew_idem
           ew_orth := P.ew_orth
           ew_int := P.ew_int
           ew_full := P.ew_full
           bw_w := P.bw_w
           bwd_w := P.bwd_w
           bw_dual := P.bw_dual
           latticeSpan := P.latticeSpan }⟩

end ChkScRef
end

end Formalism.L2.SG.Closed.ScRef

namespace Formalism.L2.SG.Closed.ScXu

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScXu

theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

def SplitAtG (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.F)), ((gD D : ℕ) : 𝓞 A.I.F) ∈ v.asIdeal →
    Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 A.I.E) //
      w.asIdeal.comap (algebraMap (𝓞 A.I.F) (𝓞 A.I.E)) = v.asIdeal} = 2

def IntAtGZ (D : D7) : Prop :=
  ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D),
    (∀ a : Fin D.R.rS, InAt A.I (gD D) 1 (incl A.I (eC A L a)) ∧ InAt A.I (gD D) 1 (incl A.I (fC A L a))) ∧
    ∀ u, InAt A.I (gD D) 1 (incl A.I (zC A L u))

theorem chkScXuExists (h : PI.ScXuExists.Target) (D : D7) (hs : SplitAtG D) (hi : IntAtGZ D) :
    XuExists D := by
  intro A L Rf
  have hn : A.I.n = 2 * D.R.rS + D.R.k + 1 := A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm
  have hg : 1 ≤ gD D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  let P : PI.ScRefExists.RefData A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) :=
    { e0 := Rf.e0
      f0 := Rf.f0
      z0 := Rf.z0
      bw := Rf.bw
      bwd := Rf.bwd
      ew := Rf.ew
      vectorsInLattice := Rf.vectorsInLattice
      basisApprox := Rf.basisApprox
      gramIntegral := Rf.gramIntegral
      formsAtZero := Rf.formsAtZero
      weightVectorsIntegral := Rf.weightVectorsIntegral
      ew_idem := Rf.ew_idem
      ew_orth := Rf.ew_orth
      ew_int := Rf.ew_int
      ew_full := Rf.ew_full
      bw_w := Rf.bw_w
      bwd_w := Rf.bwd_w
      bw_dual := Rf.bw_dual
      latticeSpan := Rf.latticeSpan }
  have key : ∀ u, ∃ x : A.I.Gf, (∀ a, A.I.fmat x *ᵥ incl A.I (eC A L a) = incl A.I (eC A L a) ∧
      A.I.fmat x *ᵥ incl A.I (fC A L a) = incl A.I (fC A L a)) ∧
      InAt A.I (gD D) (gD D) (A.I.fmat x⁻¹ *ᵥ incl A.I (zC A L u) - Rf.z0) ∧ OneOff A.I (gD D) x ∧
      x ∈ A.I.Kset := by
    intro u
    have hT : (D.mem u).A.T ≡ 1 [MOD gD D] :=
      D.T_modEq_of_dvd u (dvd_trans (dvd_pow_self _ two_ne_zero) D.gg_dvd_modT)
    exact h A.I (gD D) D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) P hg (hs A) hn
      (fun a b => by simp only [eC, hform_eq, L.ee, map_zero])
      (fun a b => by simp only [fC, hform_eq, L.ff, map_zero])
      (fun a b => by simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp)
      (fun a => by simp only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self])
      ⟨(D.mem u).A.T, hT, by simp only [zC, hform_eq, L.zu_norm, map_neg, map_natCast]⟩
      (hi A L).1 ((hi A L).2 u)
  choose xu hfix hz hone hK using key
  exact ⟨{ xu := xu
           xu_fix := fun u a => hfix u a
           xu_z := hz
           xu_one := hone
           xu_K := hK }⟩

end ChkScXu
end

end Formalism.L2.SG.Closed.ScXu

namespace Formalism.L2.SG.Closed.ScPi

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ChkScPi

theorem hform_crdA {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hform_eq {D : D7} (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdA, RingEquiv.symm_apply_apply]

theorem isFrame {D : D7} (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (u : D.what₂.Word) :
    PI.ScPiExists.IsFrame A.I (eC A L) (fC A L) (zC A L u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b; simp only [eC, hform_eq, L.ee, map_zero]
  · intro a b; simp only [fC, hform_eq, L.ff, map_zero]
  · intro a b; simp only [eC, fC, hform_eq, L.ef]; split_ifs <;> simp
  · intro a; simp only [eC, fC, zC, hform_eq, (L.zu_orth u a).1, (L.zu_orth u a).2, map_zero, and_self]

theorem zz_eq {D : D7} (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (u : D.what₂.Word) :
    Formalism.UG.hform (starRingEnd A.I.E) A.I.J (zC A L u) (zC A L u) = -(((D.mem u).A.T : ℕ) : A.I.E) := by
  simp only [zC, hform_eq, L.zu_norm, map_neg, map_natCast]

theorem T_pos {D : D7} (u : D.what₂.Word) : 0 < (D.mem u).A.T := by
  have h2 := D.T_mod_g u 0
  rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
  · rw [h] at h2; simp at h2
  · exact h

theorem strictAnti_fin {k : ℕ} (g : Fin k → ℝ) (hs : ∀ (i j : Fin k), j.1 = i.1 + 1 → g j < g i) :
    StrictAnti g := by
  have key : ∀ a : ℕ, ∀ i j : Fin k, j.1 = i.1 + a + 1 → g j < g i := by
    intro a
    induction a with
    | zero => intro i j h; exact hs i j (by omega)
    | succ a ih =>
      intro i j h
      have hm : i.1 + a + 1 < k := by omega
      exact lt_trans (hs ⟨i.1 + a + 1, hm⟩ j (by simp; omega)) (ih i ⟨i.1 + a + 1, hm⟩ rfl)
  intro i j hij
  exact key (j.1 - i.1 - 1) i j (by have : i.1 < j.1 := hij; omega)

theorem hcParam (D : D7) (P : HCParam D.R) : PI.UpqRep.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  refine ⟨?_, ?_⟩
  · apply strictAnti_fin
    intro i j hj
    have hi : i.1 < D.R.k - 1 := by omega
    have h1 := P.u_gt_v ⟨i.1, hi⟩
    have h2 := P.v_gt_u ⟨i.1, hi⟩
    have hj' : j = ⟨i.1 + 1, by omega⟩ := Fin.ext hj
    have e1 : P.u ⟨i.1 + 1, by omega⟩ < P.u i := lt_trans h2 h1
    rw [hj']
    exact_mod_cast e1
  · intro a
    obtain ⟨z, hz⟩ := P.u_half a
    obtain ⟨j, hj⟩ := D.R.k_even
    refine ⟨z - j + 1, ?_⟩
    show ((P.u a : ℚ) : ℝ) - _ = _
    rw [hz]
    have hk : (D.R.k : ℝ) = j + j := by exact_mod_cast hj
    rw [hk]
    push_cast
    ring

theorem chkScPiExists (hW : Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists) (hF : PI.ScPiExists.Frame)
    (hB : PI.ScPiExists.Build) (D : D7) : PiExists D := by
  intro A L
  have hW' : PI.ScPiExists.WeylHyp := fun k u hu => hW k u hu
  have hn : A.I.n = 2 * D.R.rS + D.R.k + 1 := A.n_eq.trans (Formalism.MainNotions.S.dimS_eq D.R).symm
  have heps : ∀ v (i : Fin A.I.n), A.I.ε v i =
      if i.val < D.R.k - 1 then true else decide ((i.val - (D.R.k - 1)) % 2 = 0) := by
    intro v i
    rw [A.eps_eq v i]
    simp only [epsS, Fin.val_cast]
  have key : ∀ u, Nonempty (PI.ScPiExists.PiData A.I D.R.k (eC A L) (fC A L) (zC A L u)
      (fun v i => (((D.hcW u (A.pl v)).u i : ℚ) : ℝ))) := by
    intro u
    refine hB hW' A.I D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) _ hn (isFrame A L u) ?_ ?_ ?_
    · rw [zz_eq]
      intro h0
      have h1 : (((D.mem u).A.T : ℕ) : A.I.E) = 0 := neg_eq_zero.mp h0
      rw [Nat.cast_eq_zero] at h1
      exact (Nat.pos_iff_ne_zero.mp (T_pos u)) h1
    · intro v; exact hcParam D (D.hcW u (A.pl v))
    · exact hF A.I D.R.rS D.R.k (eC A L) (fC A L) (zC A L u) hn (isFrame A L u)
        ⟨(D.mem u).A.T, T_pos u, zz_eq A L u⟩ heps
  let P := fun u => Classical.choice (key u)
  exact ⟨{ Vpi := fun u => (P u).Vpi
           vN := fun u => (P u).vN
           vI := fun u => (P u).vI
           vF := fun u => (P u).vF
           piU := fun u => (P u).piU
           piU_rep := fun u => (P u).piU_rep
           Vloc := fun u => (P u).Vloc
           lN := fun u => (P u).lN
           lI := fun u => (P u).lI
           lF := fun u => (P u).lF
           piLoc := fun u => (P u).piLoc
           piLoc_type := fun u => (P u).piLoc_type
           wfr := fun u => (P u).wfr
           wfr_on := fun u => (P u).wfr_on
           wfr_perp := fun u => (P u).wfr_perp
           tensU := fun u => (P u).tensU
           tensU_inner := fun u => (P u).tensU_inner
           tensU_span := fun u => (P u).tensU_span
           tensU_equiv := fun u => (P u).tensU_equiv }⟩

end ChkScPi
end

end Formalism.L2.SG.Closed.ScPi

namespace Formalism.L2.SG.Closed

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.SplitPrimeNormLemmas

theorem PsiExists_holds (D : D7) : PsiExists D := ScPsi.chkScPsiExists sc_psi_exists D

theorem MuExists_holds (D : D7) : MuExists D := ScMu.ChkScMu.chkScMuExists PI.sc_mu_exists D

theorem RefExists_holds (D : D7) : RefExists D :=
  ScRef.ChkScRef.chkScRefExists sc_reference_exists D (Formalism.L2.SG.SplitPrimeNormLemmas.SplitG.splitAtG_holds D)
    (fun A L a => (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.intAtGZ_holds D A L).1 a)

theorem XuExists_holds (D : D7) : XuExists D :=
  ScXu.ChkScXu.chkScXuExists sc_xu_exists D (Formalism.L2.SG.SplitPrimeNormLemmas.SplitG.splitAtG_holds D)
    (Formalism.L2.SG.SplitPrimeNormLemmas.IntG.intAtGZ_holds D)

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.HighestWeightExists] in
theorem PiExists_holds (D : D7) : PiExists D :=
  ScPi.ChkScPi.chkScPiExists Formalism.MainNotions.BridgeHW.highest_weight_exists_bis sc_pi_frame sc_pi_construction D

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.DiscreteSeriesExistsG] in
theorem BunExists_holds (D : D7) : BunExists D :=
  Formalism.L2.SG.Pf.automorphic_bundle_exists Formalism.MainNotions.BridgeDS3.discrete_series_exists_gapped D

theorem CoefWeightedLoc_holds [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] : CoefWeightedLoc := Fact.out


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap] in
theorem BesselNVGap_holds : BesselNVGap := Formalism.L2.SG.BesselDiscreteSeries.besselNVGap

theorem WlocExists_holds : WlocExists := scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end Formalism.L2.SG.Closed
