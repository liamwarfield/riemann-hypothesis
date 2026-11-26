module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def UnitInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ q ∈ UWb k r, qᴴ * q = 1 → ν.map (rmulM q) = ν

def HermInv : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, B₀ᴴ * Hb k * B₀ = Hb k → B₀ᴴ = B₀ →
      ν.map (rmulM (embWb k r B₀)) = ν

def PolarDecW : Prop :=
  ∀ (k r : ℕ) (p : Mat k r), p ∈ UWb k r → ∃ B₀ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ,
    B₀ᴴ * Hb k * B₀ = Hb k ∧ B₀ᴴ = B₀ ∧ ∃ q ∈ UWb k r, qᴴ * q = 1 ∧ p = embWb k r B₀ * q

theorem rmulM_comp {k r : ℕ} (a b : Mat k r) : rmulM b ∘ rmulM a = rmulM (a * b) := by
  funext x
  show Matrix.of x * a * b = Matrix.of x * (a * b)
  rw [Matrix.mul_assoc]

theorem rmulM_meas {k r : ℕ} (p : Mat k r) : Measurable (rmulM p : Mt k r → Mt k r) :=
  (rmulM_cont p).measurable

theorem unimodW_of (hU : UnitInv) (hH : HermInv) (hP : PolarDecW) : UnimodW := by
  intro k r ν hk hG p hp
  obtain ⟨B₀, hB, hBh, q, hq, hqu, rfl⟩ := hP k r p hp
  rw [← rmulM_comp, ← Measure.map_map (rmulM_meas q) (rmulM_meas _), hH k r ν hk hG B₀ hB hBh,
    hU k r ν hk hG q hq hqu]

end PI.RhsWLim.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.UnimodS
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {k r : ℕ}

def BallConj : Prop :=
  ∀ (k r : ℕ) (ρ : ℝ) (q : Mat k r), q ∈ UWb k r → qᴴ * q = 1 →
    rmulM q ⁻¹' bBall k r ρ ⊆ lmulM q ⁻¹' bBall k r ρ

def rmulE (p : Mat k r) (hp : IsUnit p.det) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulM p
  invFun := rmulM p⁻¹
  left_inv x := by
    show (Matrix.of x * p) * p⁻¹ = x
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hp, Matrix.mul_one]; rfl
  right_inv x := by
    show (Matrix.of x * p⁻¹) * p = x
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.mul_one]; rfl
  measurable_toFun := rmulM_meas p
  measurable_invFun := rmulM_meas p⁻¹

theorem lr_comm (s p : Mat k r) : lmulM s ∘ rmulM p = rmulM p ∘ lmulM s := by
  funext x
  show s * (Matrix.of x * p) = (s * Matrix.of x) * p
  rw [Matrix.mul_assoc]

theorem rmul_haar (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r) :
    IsHaarOn (UWb k r) (ν.map (rmulM p)) := by
  obtain ⟨hσ, h0, hc, hl⟩ := hH
  have hu := uwb_unit hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rmulE p hu).sigmaFinite_map
  · rw [Ne, Measure.map_eq_zero_iff (rmulM_meas p).aemeasurable]; exact h0
  · have hms : MeasurableSet {x : Mt k r | Matrix.of x ∉ UWb k r} := amb_closed.isOpen_compl.measurableSet
    rw [Measure.map_apply (rmulM_meas p) hms]
    refine measure_mono_null (fun x hx => ?_) hc
    intro hxm
    apply hx
    show Matrix.of x * p ∈ UWb k r
    exact uwb_mul hxm hp
  · intro s hs
    rw [Measure.map_map (lmulM_cont s).measurable (rmulM_meas p), lr_comm,
      ← Measure.map_map (rmulM_meas p) (lmulM_cont s).measurable, hl s hs]

theorem gauge_ball (ν : Measure (Mt k r)) (hG : IsGaugeOn k r (UWb k r) ν) :
    ∃ ρ : ℝ, 0 < ν (bBall k r ρ) ∧ ν (bBall k r ρ) < ⊤ := by
  have h := hG.2.eventually_const_lt (show (0 : ℝ) < 1 from one_pos)
  obtain ⟨ρ, hρ⟩ := h.exists
  refine ⟨ρ, ?_, ?_⟩
  · rcases eq_or_ne (ν (bBall k r ρ)) 0 with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact pos_iff_ne_zero.2 h0
  · rcases eq_or_ne (ν (bBall k r ρ)) ⊤ with h0 | h0
    · exfalso
      have : (ν (expBall (k := k) (r := r) (UWb k r) ρ)).toReal = 0 := by
        show (ν (bBall k r ρ)).toReal = 0
        rw [h0]; rfl
      rw [this, zero_div] at hρ; exact lt_irrefl _ hρ
    · exact lt_top_iff_ne_top.2 h0

theorem rmul_scale (ν : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) ν) (p : Mat k r) (hp : p ∈ UWb k r)
    (s : Set (Mt k r)) (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) :
    ν.map (rmulM p) = (ν.map (rmulM p) s / ν s) • ν := by
  have h1 := rmul_haar ν hH p hp
  obtain ⟨hσ1, h01, hc1, hl1⟩ := h1
  obtain ⟨hσ2, h02, hc2, hl2⟩ := hH
  have i1 : SigmaFinite (pull (ν.map (rmulM p))) := pull_sigmaFinite _
  have i2 : SigmaFinite (pull ν) := pull_sigmaFinite ν
  have i3 : (pull (ν.map (rmulM p))).IsMulLeftInvariant := pull_left _ hl1
  have i4 : (pull ν).IsMulLeftInvariant := pull_left ν hl2
  have key := measure_eq_div_smul (pull (ν.map (rmulM p))) (pull ν) (s := inc ⁻¹' s)
    (by rw [pull_apply ν hc2]; exact h0) (by rw [pull_apply ν hc2]; exact ht)
  calc ν.map (rmulM p) = (pull (ν.map (rmulM p))).map inc := (map_pull _ hc1).symm
    _ = ((pull (ν.map (rmulM p)) (inc ⁻¹' s) / pull ν (inc ⁻¹' s)) • pull ν).map inc := by rw [← key]
    _ = _ := by rw [Measure.map_smul _ inc_cont.measurable.aemeasurable, map_pull ν hc2, pull_apply _ hc1, pull_apply ν hc2]

theorem one_of_le (c c' : ℝ≥0∞) (h : c * c' = 1) (hc : c ≤ 1) (hc' : c' ≤ 1) : c = 1 := by
  refine le_antisymm hc ?_
  calc 1 = c * c' := h.symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

theorem one_of_sq (c : ℝ≥0∞) (h : c * c = 1) : c = 1 := by
  rcases le_total c 1 with hc | hc
  · exact one_of_le c c h hc hc
  · refine le_antisymm ?_ hc
    calc c = c * 1 := (mul_one c).symm
      _ ≤ c * c := by gcongr
      _ = 1 := h

theorem map_rmul_one (ν : Measure (Mt k r)) : ν.map (rmulM (1 : Mat k r)) = ν := by
  have : (rmulM (1 : Mat k r) : Mt k r → Mt k r) = id := by
    funext x; unfold rmulM; rw [Matrix.mul_one]; rfl
  rw [this, Measure.map_id]

theorem scale_mul_one (ν : Measure (Mt k r)) (p p' : Mat k r) (hpp : p * p' = 1) (s : Set (Mt k r))
    (h0 : ν s ≠ 0) (ht : ν s ≠ ⊤) (c c' : ℝ≥0∞) (hc : ν.map (rmulM p) = c • ν)
    (hc' : ν.map (rmulM p') = c' • ν) : c * c' = 1 := by
  have e : ν = (c * c') • ν := by
    calc ν = ν.map (rmulM (p * p')) := by rw [hpp, map_rmul_one]
      _ = (ν.map (rmulM p)).map (rmulM p') := by
          rw [Measure.map_map (rmulM_meas p') (rmulM_meas p), rmulM_comp]
      _ = (c * c') • ν := by rw [hc, Measure.map_smul _ (rmulM_meas p').aemeasurable, hc', smul_smul]
  have e2 := congrArg (fun m : Measure (Mt k r) => m s) e
  simp only [Measure.smul_apply, smul_eq_mul] at e2
  exact (ENNReal.mul_left_inj h0 ht).1 (show (c * c') * ν s = 1 * ν s by rw [one_mul]; exact e2.symm)

theorem unitInv_of (hB : BallConj) : UnitInv := by
  intro k r ν hk hG q hq hqu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hs : MeasurableSet (bBall k r ρ) := measurableSet_expBall k r (UWb k r) ρ
  have hu := uwb_unit hq
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hqu
  have hq' : qᴴ ∈ UWb k r := by rw [← hqi]; exact uwb_inv hq
  have hqu' : (qᴴ)ᴴ * qᴴ = 1 := by rw [conjTranspose_conjTranspose, ← hqi, Matrix.mul_nonsing_inv _ hu]
  have le1 : ∀ q : Mat k r, q ∈ UWb k r → qᴴ * q = 1 → ν.map (rmulM q) (bBall k r ρ) ≤ ν (bBall k r ρ) := by
    intro q hq hqu
    rw [Measure.map_apply (rmulM_meas q) hs]
    calc ν (rmulM q ⁻¹' bBall k r ρ) ≤ ν (lmulM q ⁻¹' bBall k r ρ) := measure_mono (hB k r ρ q hq hqu)
      _ = ν.map (lmulM q) (bBall k r ρ) := (Measure.map_apply (lmulM_cont q).measurable hs).symm
      _ = ν (bBall k r ρ) := by rw [hG.1.2.2.2 q hq]
  have hsc := rmul_scale ν hG.1 q hq _ h0.ne' ht.ne
  have hsc' := rmul_scale ν hG.1 qᴴ hq' _ h0.ne' ht.ne
  have hm := scale_mul_one ν q qᴴ (by rw [← hqi, Matrix.mul_nonsing_inv _ hu]) _ h0.ne' ht.ne _ _ hsc hsc'
  have hc1 : ν.map (rmulM q) (bBall k r ρ) / ν (bBall k r ρ) ≤ 1 :=
    (ENNReal.div_le_iff h0.ne' ht.ne).2 (by rw [one_mul]; exact le1 q hq hqu)
  have hc1' : ν.map (rmulM qᴴ) (bBall k r ρ) / ν (bBall k r ρ) ≤ 1 :=
    (ENNReal.div_le_iff h0.ne' ht.ne).2 (by rw [one_mul]; exact le1 qᴴ hq' hqu')
  rw [hsc, one_of_le _ _ hm hc1 hc1', one_smul]

theorem hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> norm_num

theorem hermInv_of (hU : UnitInv) : HermInv := by
  intro k r ν hk hG B₀ hB hBh
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  have hE : embWb k r (Hb k) ∈ UWb k r := MB.emb_mem_UWb (by rw [hHbh, hb_sq, Matrix.one_mul])
  have hEu : (embWb k r (Hb k))ᴴ * embWb k r (Hb k) = 1 := by
    rw [MB.emb_conjT, hHbh, ← MB.emb_mul, hb_sq, MB.emb_one]
  have hBm : embWb k r B₀ ∈ UWb k r := MB.emb_mem_UWb hB
  have hinv : embWb k r B₀ * (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k)) = 1 := by
    rw [← MB.emb_mul, ← MB.emb_mul, ← MB.emb_mul]
    have : B₀ * (Hb k * B₀ * Hb k) = 1 := by
      calc B₀ * (Hb k * B₀ * Hb k) = (B₀ᴴ * Hb k * B₀) * Hb k := by rw [hBh]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hB, hb_sq]
    rw [this, MB.emb_one]
  have hEinv := hU k r ν hk hG _ hE hEu
  obtain ⟨ρ, h0, ht⟩ := gauge_ball ν hG
  have hsc := rmul_scale ν hG.1 _ hBm _ h0.ne' ht.ne
  set c := ν.map (rmulM (embWb k r B₀)) (bBall k r ρ) / ν (bBall k r ρ) with hc
  have h2 : ν.map (rmulM (embWb k r (Hb k) * embWb k r B₀ * embWb k r (Hb k))) = c • ν := by
    rw [← rmulM_comp, ← rmulM_comp, ← Measure.map_map (rmulM_meas _) ((rmulM_meas _).comp (rmulM_meas _)),
      ← Measure.map_map (rmulM_meas _) (rmulM_meas _), hEinv, hsc, Measure.map_smul _ (rmulM_meas _).aemeasurable, hEinv]
  have hcc := scale_mul_one ν _ _ hinv _ h0.ne' ht.ne c c hsc h2
  rw [hsc, one_of_sq c hcc, one_smul]

theorem unimodW_of_two (hB : BallConj) (hP : PolarDecW) : UnimodW :=
  unimodW_of (unitInv_of hB) (hermInv_of (unitInv_of hB)) hP

end PI.RhsWLim.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.BallConj
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {m : ℕ}

def realE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

theorem realE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    realE X p = realifyFun X p := rfl

theorem unr_realE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realE X) = X := by
  funext i j
  simp only [unrealify, realE_apply, realifyFun]
  simp

theorem realE_unr (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realE (unrealify x) = x := by
  ext ⟨i, j, b⟩
  rw [realE_apply]
  cases b <;> simp [realifyFun, unrealify]

theorem unr_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem unr_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem realE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realE (X + Y) = realE X + realE Y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

theorem realE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realE ((c : ℂ) • X) = c • realE X := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

def conjL (q : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realE (q * unrealify x * q⁻¹)
  map_add' x y := by rw [unr_add, Matrix.mul_add, Matrix.add_mul, realE_add]
  map_smul' c x := by
    rw [unr_smul, Matrix.mul_smul, Matrix.smul_mul, realE_smul]; rfl

theorem conjL_apply (q : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    conjL q x = realE (q * unrealify x * q⁻¹) := rfl

theorem norm_realE (X : Matrix (Fin m) (Fin m) ℂ) :
    ‖realE X‖ = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [realE_apply, realifyFun, Real.norm_eq_abs, sq_abs, if_true, Bool.false_eq_true, if_false,
    Complex.normSq_apply]
  ring

theorem frob_trace (X : Matrix (Fin m) (Fin m) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (X i j) : ℝ) : ℂ) = (X * Xᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj]

theorem frob_conj (q X : Matrix (Fin m) (Fin m) ℂ) (hq : qᴴ * q = 1) :
    ∑ i, ∑ j, Complex.normSq ((q * X * q⁻¹) i j) = ∑ i, ∑ j, Complex.normSq (X i j) := by
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hq
  apply Complex.ofReal_injective
  rw [frob_trace, frob_trace, hqi]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (q * X * qᴴ * (q * (Xᴴ * qᴴ))).trace = (q * (X * (qᴴ * q) * Xᴴ) * qᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (X * Xᴴ * (qᴴ * q)).trace := by
        rw [hq, Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hq, Matrix.one_mul]
    _ = (X * Xᴴ).trace := by rw [hq, Matrix.mul_one]

theorem conj_lieOf {k r : ℕ} (q : Mat k r) (hq : q ∈ UWb k r) (X : Mat k r) (hX : X ∈ lieOf (UWb k r)) :
    q * X * q⁻¹ ∈ lieOf (UWb k r) := by
  intro t
  have hu := uwb_unit hq
  have e : (t : ℂ) • (q * X * q⁻¹) = q * ((t : ℂ) • X) * q⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu)]
  exact uwb_mul (uwb_mul hq (hX t)) (uwb_inv hq)

theorem ballConj : BallConj := by
  intro k r ρ q hq hqu x hx
  have hu := uwb_unit hq
  obtain ⟨v, hv, hvx⟩ := hx

  have hmap : Submodule.map (conjL q) (lieE (UWb k r)) ≤ lieE (UWb k r) := by
    rw [lieE, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨q * X * q⁻¹, conj_lieOf q hq X hX, ?_⟩
    show realE (q * X * q⁻¹) = conjL q (realE X)
    rw [conjL_apply, unr_realE]
  have hmem : conjL q (v : EuclideanSpace ℝ _) ∈ lieE (UWb k r) :=
    hmap ⟨v, v.2, rfl⟩
  refine ⟨⟨conjL q v, hmem⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    show ‖conjL q (v : EuclideanSpace ℝ _)‖ < ρ
    rw [conjL_apply, norm_realE, frob_conj q _ hqu, ← norm_realE, realE_unr]
    exact hv
  · have hx' : (Matrix.of x : Mat k r) * q = NormedSpace.exp (unrealify (v : EuclideanSpace ℝ _)) := by
      have := congrArg (fun f : Mt k r => (Matrix.of f : Mat k r)) hvx
      exact this.symm
    show (fun i j => NormedSpace.exp (unrealify (conjL q (v : EuclideanSpace ℝ _))) i j) =
      q * Matrix.of x
    rw [conjL_apply, unr_realE, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu), ← hx']
    funext i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end PI.RhsWLim.W
end
end

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem hpk_mulVec_gen (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = HU.sgn k r i * v (HU.tau k r i) := hpk_mulVec_apply v i

theorem herm_bvec (u : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) u (bvec i) = (Hpk k r *ᵥ u) i := by
  unfold herm bvec
  have : star (Pi.single i (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single i (1 : ℂ) := by
    funext j; simp [Pi.single_apply]
  rw [this, single_dotProduct, one_mul]

theorem herm_pres {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (p *ᵥ u) (p *ᵥ v) = herm (Hpk k r) u v := by
  rw [herm_mulVec_right hp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (HU.isUnit_of_uh hp), Matrix.one_mulVec]

theorem uwb_emb {p : Mat k r} (hp : p ∈ UWb k r) :
    p = embWb k r (fun i j => p (wI k r i) (wI k r j)) := by
  ext i j
  by_cases hj : j.val < r ∨ r + k < j.val
  ·
    have hcol : p *ᵥ bvec j = bvec j := by
      rcases hj with hj | hj
      · have := (hp.2 ⟨j.val, hj⟩).1
        have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
        rwa [e] at this
      · have := (hp.2 ⟨2 * r + k - j.val, by omega⟩).2
        have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rwa [e] at this
    have h1 := congrFun hcol i
    rw [MB.mulVec_bvec, MB.bvec_apply] at h1
    rw [h1]
    unfold embWb
    rw [dite_eq_right (by omega)]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos ⟨rfl, by omega⟩]
    · rw [if_neg hij, if_neg (fun h => hij h.1)]
  · push Not at hj
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (k + 1), wI k r j' = j :=
      ⟨⟨j.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    by_cases hi : i.val < r ∨ r + k < i.val
    ·
      have hw : (p *ᵥ bvec (wI k r j')) i = 0 := by
        rcases hi with hi | hi
        ·
          set a : Fin r := ⟨i.val, hi⟩
          have hfix := (hp.2 a).2
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (esI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (esI k r a) = i := by
            unfold HU.tau esI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (esI k r a) = 1 := by
            unfold HU.sgn esI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
        · set a : Fin r := ⟨2 * r + k - i.val, by omega⟩
          have hfix := (hp.2 a).1
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (eI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (eI k r a) = i := by
            unfold HU.tau eI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (eI k r a) = 1 := by
            unfold HU.sgn eI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
      rw [MB.mulVec_bvec] at hw
      rw [hw]
      unfold embWb
      rw [dite_eq_right (by omega), if_neg (fun h => by have := congrArg Fin.val h.1; simp only [wI] at this; omega)]
    · push Not at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (k + 1), wI k r i' = i :=
        ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
      have := embWb_wI (k := k) (r := r) (fun i j => p (wI k r i) (wI k r j)) i' j'
      exact this.symm

theorem col_unitary (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hμ : μᴴ * Hb k * μ = Hb k) (l : ℂ)
    (hl : conj l * l = 1) (hcol : ∀ i, μ i (Fin.last k) = if i = Fin.last k then l else 0) : μᴴ * μ = 1 := by
  have hl0 : conj l ≠ 0 := by intro h; rw [h, zero_mul] at hl; exact zero_ne_one hl
  have hrow : ∀ j, j ≠ Fin.last k → μ (Fin.last k) j = 0 := by
    intro j hj
    have h := congrFun (congrFun hμ (Fin.last k)) j
    rw [form_apply] at h
    simp only [hcol, Fin.castSucc_ne_last, if_false, map_zero, zero_mul, Finset.sum_const_zero, if_true,
      zero_sub, Hb, Matrix.diagonal_apply_ne _ (Ne.symm hj)] at h
    have : conj l * μ (Fin.last k) j = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left hl0
  have key : ∀ i j, (μᴴ * μ) i j = Hb k i j + 2 * (conj (μ (Fin.last k) i) * μ (Fin.last k) j) := by
    intro i j
    have h := congrFun (congrFun hμ i) j
    rw [form_apply] at h
    rw [← h, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    ring
  ext i j
  rw [key]
  by_cases hi : i = Fin.last k
  · by_cases hj : j = Fin.last k
    · subst hi; subst hj
      rw [hcol, if_pos rfl, hl]
      simp [Hb]; norm_num
    · rw [hrow j hj, mul_zero, mul_zero, add_zero, Hb, Matrix.diagonal_apply_ne _ (fun h => hj (h.symm.trans hi)),
        Matrix.one_apply_ne (fun h => hj (h.symm.trans hi))]
  · rw [hrow i hi, map_zero, zero_mul, mul_zero, add_zero, Hb, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; exact hi (h1 ▸ h2))

theorem boost_herm (y : Fin k → ℂ) (n : ℝ) (hn : 0 < n) : (boost y (n : ℂ))ᴴ = boost y (n : ℂ) := by
  have hnn : ‖(n : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  ext i j
  rw [Matrix.conjTranspose_apply, Complex.star_def]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [boost]
    | cast j => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
    | cast j =>
      simp only [boost, Fin.lastCases_castSucc, hnn, map_add (f := _), map_div₀, map_mul, Complex.conj_conj,
        Complex.conj_ofReal, map_one]
      by_cases h : i = j
      · subst h; simp; ring
      · rw [if_neg (Ne.symm h), if_neg h]; simp; ring

theorem polarDecW : PolarDecW := by
  intro k r p hp
  set μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j => p (wI k r i) (wI k r j) with hμdef
  have hpμ : p = embWb k r μ := uwb_emb hp
  have hμ : μᴴ * Hb k * μ = Hb k := (MB.emb_mem μ).1 (hpμ ▸ hp.1)
  set y : Fin k → ℂ := fun l => μ l.castSucc (Fin.last k) with hy
  set c : ℂ := μ (Fin.last k) (Fin.last k) with hc
  have hform := congrFun (congrFun hμ (Fin.last k)) (Fin.last k)
  rw [form_apply] at hform
  have hS0 : ∑ l, conj (y l) * y l = conj c * c - 1 := by
    simp only [Hb, Matrix.diagonal_apply_eq, if_true] at hform
    simp only [hy, hc]; linear_combination hform
  have hA : ∑ l, conj (y l) * y l = ((∑ l, Complex.normSq (y l) : ℝ) : ℂ) := by
    push_cast [Complex.normSq_eq_conj_mul_self]; rfl
  have hA0 : 0 ≤ ∑ l, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hcc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul, zero_sub, hA] at hS0
    have := congrArg Complex.re hS0
    simp at this; linarith
  set n : ℝ := ‖c‖ with hn
  have hnpos : 0 < n := norm_pos_iff.2 hc0
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hnpos.ne'
  set y' : Fin k → ℂ := fun l => y l * ((n : ℂ) / c) with hy'
  have hnn : ‖((n : ℝ) : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  have hS' : ∑ l, conj (y' l) * y' l = ((‖((n : ℝ) : ℂ)‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e : ∀ l, conj (y' l) * y' l = conj (y l) * y l * (((n : ℂ) ^ 2) / (conj c * c)) := by
      intro l; simp only [hy', map_mul, map_div₀, Complex.conj_ofReal]; field_simp
    simp only [e, ← Finset.sum_mul, hS0, hcc, hnn]
    field_simp
  set B₀ := boost y' (n : ℂ) with hB₀
  have hB : B₀ᴴ * Hb k * B₀ = Hb k := boost_mem y' (n : ℂ) hS' hn0
  have hBh : B₀ᴴ = B₀ := boost_herm y' n hnpos
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  set Bi := Hb k * B₀ᴴ * Hb k with hBi
  have hBiB : Bi * B₀ = 1 := by
    calc Bi * B₀ = Hb k * (B₀ᴴ * Hb k * B₀) := by simp only [hBi, Matrix.mul_assoc]
      _ = 1 := by rw [hB, hb_sq]
  have hBBi : B₀ * Bi = 1 := mul_eq_one_comm.mp hBiB
  have hBHB : B₀ * Hb k * B₀ᴴ = Hb k := by
    have : B₀ * Hb k * B₀ᴴ * Hb k = 1 := by rw [← hBBi, hBi]; simp only [Matrix.mul_assoc]
    calc B₀ * Hb k * B₀ᴴ = B₀ * Hb k * B₀ᴴ * Hb k * Hb k := by rw [Matrix.mul_assoc (B₀ * Hb k * B₀ᴴ) (Hb k) (Hb k), hb_sq, Matrix.mul_one]
      _ = Hb k := by rw [this, Matrix.one_mul]
  set μq := Bi * μ with hμq
  have hμqU : μqᴴ * Hb k * μq = Hb k := by
    have hBi' : Biᴴ * Hb k * Bi = Hb k := by
      simp only [hBi, Matrix.conjTranspose_mul, hHbh, conjTranspose_conjTranspose]
      calc Hb k * (B₀ * Hb k) * Hb k * (Hb k * B₀ᴴ * Hb k) = Hb k * (B₀ * (Hb k * Hb k) * Hb k * B₀ᴴ) * Hb k := by
            simp only [Matrix.mul_assoc]
        _ = Hb k := by rw [hb_sq, Matrix.mul_one, hBHB, hb_sq, Matrix.one_mul]
    calc μqᴴ * Hb k * μq = μᴴ * (Biᴴ * Hb k * Bi) * μ := by
          simp only [hμq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hb k := by rw [hBi', hμ]
  set e : ℂ := c / n with he
  have hucol : ∀ l, μ l (Fin.last k) = e * B₀ l (Fin.last k) := by
    intro l
    induction l using Fin.lastCases with
    | last => simp only [hB₀, boost, Fin.lastCases_last, he, hc]; field_simp
    | cast j => simp only [hB₀, boost, Fin.lastCases_last, Fin.lastCases_castSucc, he, hy', hy]; field_simp
  have hcol : ∀ i, μq i (Fin.last k) = if i = Fin.last k then e else 0 := by
    intro i
    have : μq i (Fin.last k) = e * (Bi * B₀) i (Fin.last k) := by
      simp only [hμq, Matrix.mul_apply, hucol, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, hBiB, Matrix.one_apply]
    split_ifs <;> simp
  have he1 : conj e * e = 1 := by
    simp only [he, map_div₀, Complex.conj_ofReal]
    rw [div_mul_div_comm, hcc]
    field_simp
  have hqu := col_unitary μq hμqU e he1 hcol
  refine ⟨B₀, hB, hBh, embWb k r μq, MB.emb_mem_UWb hμqU, ?_, ?_⟩
  · rw [MB.emb_conjT, ← MB.emb_mul, hqu, MB.emb_one]
  · rw [← MB.emb_mul, hμq, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, ← hpμ]

theorem unimodW : UnimodW := unimodW_of_two ballConj polarDecW

end PI.RhsWLim.W
