module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumns
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory

theorem uJ_col_sum {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h)
    (j : Fin n) :
    ∑ i, (if ε i then (1 : ℝ) else -1) * ‖h i j‖ ^ 2 = if ε j then (1 : ℝ) else -1 := by
  have h1 := congrFun (congrFun hh j) j
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  apply Complex.ofReal_injective
  push_cast
  have : ((if ε j then (1 : ℝ) else -1 : ℝ) : ℂ) = if ε j then (1 : ℂ) else -1 := by
    split_ifs <;> simp
  rw [this, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((‖h i j‖ : ℝ) : ℂ) ^ 2 = star (h i j) * h i j := by
    rw [Complex.star_def, Complex.conj_mul']
  rw [h2]
  split_ifs <;> simp

theorem uJ_conjTranspose {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) : inUJ ε hᴴ := by
  have h1 := (uJInv n ε h hh).1
  have hJ : Jm ε * Jm ε = 1 := by
    simp only [Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  unfold inUJ
  rw [Matrix.conjTranspose_conjTranspose]
  calc h * Jm ε * hᴴ = h * (Jm ε * hᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem hs_le_of_cols (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) :
    hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  set e : Fin n → ℝ := fun i => if ε i then (1 : ℝ) else -1 with he
  set σ : ℝ := if s then (1 : ℝ) else -1 with hσ
  have hc : ∀ j, ∑ i, e i * ‖h i j‖ ^ 2 = e j := uJ_col_sum ε h hh
  have hr : ∀ i, ∑ j, e j * ‖h i j‖ ^ 2 = e i := fun i => by
    have := uJ_col_sum ε hᴴ (uJ_conjTranspose ε h hh) i
    simpa only [Matrix.conjTranspose_apply, norm_star] using this
  have hee : ∀ i, e i * e i = 1 := fun i => by
    simp only [he]; split_ifs <;> simp
  have A : ∑ i, ∑ j, e i * (e j * ‖h i j‖ ^ 2) = n := by
    simp only [← Finset.mul_sum, hr, hee]
    simp
  have B : ∑ i, ∑ j, e j * ‖h i j‖ ^ 2 = ∑ i, ∑ j, e i * ‖h i j‖ ^ 2 := by
    rw [Finset.sum_comm (f := fun i j => e i * ‖h i j‖ ^ 2)]
    simp only [hr, hc]
  have C : ∑ i, ∑ j, (‖h i j‖ ^ 2 - e i * (e j * ‖h i j‖ ^ 2) + σ * (e j * ‖h i j‖ ^ 2)
      - σ * (e i * ‖h i j‖ ^ 2)) ≤ ∑ i, ∑ j, 4 * (if ε j = s then ‖h i j‖ ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 : 0 ≤ ‖h i j‖ ^ 2 := by positivity
    simp only [he, hσ]
    cases ε i <;> cases ε j <;> cases s <;> simp <;> linarith
  have D : ∑ i, ∑ j, σ * (e j * ‖h i j‖ ^ 2) = ∑ i, ∑ j, σ * (e i * ‖h i j‖ ^ 2) := by
    have := congrArg (σ * ·) B
    simpa only [Finset.mul_sum] using this
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at C
  rw [A, D] at C
  simp only [Finset.sum_filter, Finset.mul_sum, hs]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtInUJLeOfSignColumnsStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ), inUJ ε h → hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  first | exact @GlobalTheory.hs_le_of_cols | exact GlobalTheory.hs_le_of_cols | (intros; apply GlobalTheory.hs_le_of_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNetCardLeOfSubsetClosedBall
open Metric

namespace GlobalTheory

theorem exists_net_card_le_of_subset_closedBall :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (S : Set E)
      (R δ : ℝ), 0 < δ → 0 ≤ R → S ⊆ closedBall 0 R →
      ∃ T : Finset E, (T : Set E) ⊆ S ∧ (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E ∧
        ∀ x ∈ S, ∃ t ∈ T, dist x t ≤ δ := by
  intro E _ _ _ S R δ hδ hR hS
  classical
  let P : Finset E → Prop := fun T =>
    (T : Set E) ⊆ S ∧ (T : Set E).Pairwise fun a b => δ ≤ dist a b
  have hb : ∀ T, P T → (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E := fun T hT =>
    finset_card_le_of_separated T hδ hR 0 (fun a ha => hS (hT.1 ha)) hT.2
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + 2 * R / δ) ^ Module.finrank ℝ E)
  let Q : ℕ → Prop := fun n => ∃ T, P T ∧ T.card = n
  have hQ0 : Q 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨T, hT, hTc⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  refine ⟨T, hT.1, hb T hT, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hP : P (insert x T) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hT.1
    · rw [Finset.coe_insert]
      refine hT.2.insert fun b hb' _ => ⟨(hcon b hb').le, ?_⟩
      rw [dist_comm]
      exact (hcon b hb').le
  have hle : (insert x T).card ≤ N := by
    exact_mod_cast (hb _ hP).trans hN
  have := Nat.le_findGreatest (P := Q) hle ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxT] at this
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.BallVol

lemma entry_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2)
    (i j : Fin n) : ‖g i j‖ ≤ R :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 ((f1auxiliary_entry_le g i j).trans hg)

lemma inv_mul_uMat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  have : uMat g⁻¹ * uMat g = uMat (g⁻¹ * g) := rfl
  rw [this, inv_mul_cancel]; rfl

lemma norm_inv_entry {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (i k : Fin n) :
    ‖uMat g⁻¹ i k‖ = ‖uMat g k i‖ := by
  have h1 := (uJInv n ε (uMat g) g.2).1
  have h2 : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (Jm ε * (uMat g)ᴴ * Jm ε)) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, inv_mul_uMat, Matrix.one_mul]
  rw [h2]
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

lemma close_entry {n : ℕ} {ε : Fin n → Bool} (g t : UJ ε) {R : ℝ} (hR : 0 < R)
    (ht : hsG t ≤ R ^ 2) (j : Fin n) (hj : ∀ k, ‖uMat g k j - uMat t k j‖ ≤ 1 / R) (i : Fin n) :
    ‖uMat (t⁻¹ * g) i j‖ ≤ 1 + n := by
  have e : uMat (t⁻¹ * g) = 1 + uMat t⁻¹ * (uMat g - uMat t) := by
    rw [Matrix.mul_sub, inv_mul_uMat]
    have : uMat (t⁻¹ * g) = uMat t⁻¹ * uMat g := rfl
    rw [this]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  have h3 : ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  refine (norm_add_le _ _).trans (add_le_add h3 ?_)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖uMat t⁻¹ i k * (uMat g - uMat t) k j‖ ≤ ∑ _k : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_inv_entry, Matrix.sub_apply]
        calc _ ≤ R * (1 / R) :=
              mul_le_mul (entry_le hR.le ht k i) (hj k) (norm_nonneg _) hR.le
          _ = 1 := by field_simp
    _ = n := by simp

lemma vol_sign (n : ℕ) (ε : Fin n → Bool) (s : Bool) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤
      ENNReal.ofReal (C * R ^ (4 * n * (univ.filter fun a => ε a = s).card)) := by
  classical
  set q := (univ.filter fun a => ε a = s).card with hq
  let E := Fin n → {j // ε j = s} → ℂ
  have hfr : Module.finrank ℝ E = 2 * n * q := by
    simp only [E, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_subtype, ← hq]
    ring
  let Y : UJ ε → E := fun g i j => uMat g i j.1
  let W : Set (UJ ε) := {g | hsG g ≤ n + 4 * (n * (n * (1 + n) ^ 2))}
  have hW : muG ε W < ⊤ := ballFinite n ε _
  refine ⟨3 ^ (2 * n * q) * (muG ε W).toReal, by positivity, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hsub : Y '' S ⊆ Metric.closedBall 0 R := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le]
    intro i
    rw [pi_norm_le_iff_of_nonneg hR0.le]
    intro j
    exact entry_le hR0.le hg i j.1
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.exists_net_card_le_of_subset_closedBall E (Y '' S) R (1 / R) (by positivity) hR0.le hsub
  have hch : ∀ x : E, ∃ t : UJ ε, x ∈ T → t ∈ S ∧ Y t = x := by
    intro x
    by_cases hx : x ∈ T
    · obtain ⟨t, ht, rfl⟩ := hT1 hx
      exact ⟨t, fun _ => ⟨ht, rfl⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose τ hτ using hch
  have hcov : S ⊆ ⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W := by
    intro g hg
    obtain ⟨x, hx, hd⟩ := hT3 (Y g) ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := hτ x hx
    simp only [Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    show hs (uMat ((τ x)⁻¹ * g)) ≤ _
    refine (GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns n ε s _ ((τ x)⁻¹ * g).2).trans ?_
    gcongr
    calc ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖uMat ((τ x)⁻¹ * g) i j‖ ^ 2
        ≤ ∑ _i : Fin n, ∑ _j ∈ univ.filter (fun j => ε j = s), ((1 : ℝ) + n) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine close_entry g (τ x) hR0 h1 j (fun k => ?_) i
          have hj' : ε j = s := (Finset.mem_filter.1 hj).2
          rw [← h2, dist_eq_norm] at hd
          exact ((norm_le_pi_norm ((Y g - Y (τ x)) k) ⟨j, hj'⟩).trans
            (norm_le_pi_norm (Y g - Y (τ x)) k)).trans hd
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((1 : ℝ) + n) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp
  have hcard : (T.card : ℝ) ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) := by
    refine hT2.trans ?_
    rw [hfr, show 4 * n * q = 2 * (2 * n * q) by ring, pow_mul R, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : 2 * R / (1 / R) = 2 * R ^ 2 := by field_simp
    rw [this]; nlinarith
  calc muG ε S ≤ muG ε (⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_mono hcov
    _ ≤ ∑ x ∈ T, muG ε ((fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ T, muG ε W := Finset.sum_congr rfl fun x _ => measure_preimage_mul _ _ _
    _ = ENNReal.ofReal ((T.card : ℝ) * (muG ε W).toReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hW.ne, ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (T.card : ℝ) * (muG ε W).toReal
            ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) * (muG ε W).toReal := by gcongr
          _ = _ := by ring

lemma hs_le_of_dOp {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (h : dOp g ≤ r) :
    hs g ≤ ((n + 1) * Real.exp r) ^ 2 := by
  have h1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ ≤ Real.exp r :=
    Real.le_exp_of_log_le h
  have h2 : ∀ i j, ‖g i j‖ ≤ Real.exp r := by
    intro i j
    have h3 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm
      (EuclideanSpace.single j (1 : ℂ))
    have h4 := PiLp.norm_apply_le ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ))) i
    have h5 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ)) i = g i j := by
      simp [Matrix.toLpLin_apply]
    rw [h5] at h4
    have h6 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
    rw [h6, mul_one] at h3
    exact h4.trans (h3.trans h1)
  have hp := Real.exp_pos r
  calc hs g ≤ ∑ _i : Fin n, ∑ _j : Fin n, Real.exp r ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h2 i j) 2
    _ = (n * Real.exp r) ^ 2 := by simp; ring
    _ ≤ _ := by gcongr; linarith

theorem ballVol : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, (∀ R : ℝ, 1 ≤ R → muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (4 * n * rkR ε))) ∧ ∀ r : ℝ, 0 ≤ r → muG ε {g | dOp (uMat g) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
  intro n ε
  obtain ⟨s, hs'⟩ : ∃ s : Bool, rkR ε = (univ.filter fun a => ε a = s).card := by
    unfold rkR
    rcases min_choice (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨C, hC, h⟩ := vol_sign n ε s
  rw [← hs'] at h
  have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn' : (1 : ℝ) ≤ (n + 1) ^ (4 * n * rkR ε) := one_le_pow₀ hn
  refine ⟨C * (n + 1) ^ (4 * n * rkR ε), fun R hR => (h R hR).trans ?_, fun r hr => ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ R ^ (4 * n * rkR ε) := by positivity
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hn') this
  · have he : 1 ≤ Real.exp r := Real.one_le_exp hr
    have h1 := h ((n + 1) * Real.exp r) (one_le_mul_of_one_le_of_one_le hn he)
    refine (measure_mono fun g hg => ?_).trans (h1.trans (le_of_eq ?_))
    · exact hs_le_of_dOp hg
    · rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc]
      push_cast
      rfl

end GlobalTheory.BallVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_ball_growth_unitaryJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, (∀ R : ℝ, 1 ≤ R → muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (4 * n * rkR ε))) ∧ ∀ r : ℝ, 0 ≤ r → muG ε {g | dOp (uMat g) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
  first | exact @GlobalTheory.BallVol.ballVol | exact GlobalTheory.BallVol.ballVol | (intros; apply GlobalTheory.BallVol.ballVol <;> assumption)
end
