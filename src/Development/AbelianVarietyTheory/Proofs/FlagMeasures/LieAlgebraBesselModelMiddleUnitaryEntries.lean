module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellLieAlg

theorem mem_lieE_iff {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (P : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hP : ∀ X, X ∈ lieOf S ↔ X ∈ P) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE S ↔ unrealify x ∈ P := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      have e : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
        ext i j; rfl
      show unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ P
      rw [e]; exact (hP X).1 hX
    | zero =>
      have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.zero_mem
    | add x y _ _ hx hy =>
      have e : unrealify (x + y) = unrealify x + unrealify y := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.add_mem hx hy
    | smul c x _ hx =>
      have e : unrealify (c • x) = c • unrealify x := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.smul_mem c hx
  · intro hx
    refine Submodule.subset_span ⟨unrealify x, (hP _).2 hx, ?_⟩
    ext ⟨i, j, b⟩
    cases b <;> rfl

open scoped Matrix.Norms.Operator in
theorem mem_lieOf_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) (X : Matrix (Fin N) (Fin N) ℂ) :
    X ∈ lieOf (UH H) ↔ Xᴴ * H + H * X = 0 := by
  constructor
  · intro h
    have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) = fun _ => H := by
      funext t
      have h1 : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
      rw [← Matrix.exp_conjTranspose, Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial] at h1
      exact h1
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) _ 0 :=
      ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0).mul_const H).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
    rw [hc] at hd
    have := hd.unique (hasDerivAt_const _ _)
    simpa using this
  · intro hX t
    set Y : Matrix (Fin N) (Fin N) ℂ := (t : ℂ) • X with hYdef
    have hY : Yᴴ * H + H * Y = 0 := by
      rw [hYdef, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, ← smul_add, hX, smul_zero]
    have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hH
    have hu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hH)
    have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
      have e : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
      calc Yᴴ = Yᴴ * (H * H) := by rw [hH, Matrix.mul_one]
        _ = (Yᴴ * H) * H := by rw [Matrix.mul_assoc]
        _ = _ := by rw [e, hinv, Matrix.mul_neg]
    have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
      rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv]
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
    rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH,
      Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

open scoped Matrix.Norms.Operator in
theorem exp_mul_eq_iff {N : ℕ} (X E : Matrix (Fin N) (Fin N) ℂ) :
    (∀ t : ℝ, NormedSpace.exp (t • X) * E = E) ↔ X * E = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * E)
      (NormedSpace.exp (t • X) * X * E) t := fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).mul_const E
  constructor
  · intro h
    have h0 := hd 0
    rw [show (fun t : ℝ => NormedSpace.exp (t • X) * E) = fun _ => E from funext h] at h0
    simpa using h0.unique (hasDerivAt_const _ _)
  · intro h t
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => by rw [(hd t).deriv, Matrix.mul_assoc, h, Matrix.mul_zero]) t 0
    simpa using this

theorem mul_single_eq_iff {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    g * Matrix.single j j (1 : ℂ) = h * Matrix.single j j (1 : ℂ) ↔ g *ᵥ bvec j = h *ᵥ bvec j := by
  simp only [bvec, Matrix.mulVec_single_one]
  constructor
  · intro e
    funext i
    simpa using congrFun (congrFun e i) j
  · intro e
    ext i l
    by_cases hl : l = j
    · subst hl
      simpa using congrFun e i
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]

theorem exp_fix_iff {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) ↔ ∀ i, X i j = 0 := by
  have h1 := exp_mul_eq_iff X (Matrix.single j j (1 : ℂ))
  have h2 := mul_single_eq_iff X 0 j
  rw [Matrix.zero_mul] at h2
  rw [h2] at h1
  have h3 : X *ᵥ bvec j = (0 : Matrix (Fin N) (Fin N) ℂ) *ᵥ bvec j ↔ ∀ i, X i j = 0 := by
    simp [bvec, funext_iff]
  rw [← h3, ← h1]
  refine forall_congr' fun t => ?_
  have h4 := mul_single_eq_iff (NormedSpace.exp (t • X)) 1 j
  rw [Matrix.one_mul, Matrix.one_mulVec] at h4
  rw [h4, Complex.coe_smul]

theorem rows_zero {k r : ℕ} {X : Mat k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0)
    (hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0)
    (i : Fin (2 * r + k + 1)) (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) : X i j = 0 := by
  have hil := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hv : i'.val = 2 * r + k - i.val := rfl
  have h := congrFun (congrFun hX i') j
  have h1 : (Xᴴ * Hpk k r) i' j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.conjTranspose_apply, hc i' (by omega) l, star_zero, zero_mul]
  have h2 : (Hpk k r * X) i' j = X i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · have : Hpk k r i' i = 1 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, one_mul]
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun e => hl (Fin.ext e)
      have : Hpk k r i' l = 0 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · simp
  rw [Matrix.add_apply, h1, h2, zero_add] at h
  exact h

theorem mem_lieOf_UWb (k r : ℕ) (X : Mat k r) :
    X ∈ lieOf (Formalism.FourierDecayAlt.B2.UWb k r) ↔ (Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0) := by
  have hH := (hpkFacts k r).2.1
  constructor
  · intro h
    have hX := (mem_lieOf_UH _ hH X).1 fun t => (h t).1
    have hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0 := by
      intro j hj
      have hjl := j.isLt
      by_cases hr : j.val < r
      · exact (exp_fix_iff X j).1 fun t => ((h t).2 ⟨j.val, hr⟩).1
      · have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rw [← e]
        exact (exp_fix_iff X _).1 fun t => ((h t).2 _).2
    refine ⟨hX, fun i j hij => ?_⟩
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · exact hc j (fun hj => hij ⟨hi, hj⟩) i
    · exact rows_zero hX hc i hi j
  · rintro ⟨hX, h0⟩ t
    refine ⟨(mem_lieOf_UH _ hH X).2 hX t, fun a => ⟨?_, ?_⟩⟩
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.1; have := a.isLt
      simp only [eI] at *; omega
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.2; have := a.isLt
      simp only [esI] at *; omega

def skewSub {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    have ha' : aᴴ * H + H * a = 0 := ha
    have hb' : bᴴ * H + H * b = 0 := hb
    show (a + b)ᴴ * H + H * (a + b) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' c a ha := by
    have ha' : aᴴ * H + H * a = 0 := ha
    show (c • a)ᴴ * H + H * (c • a) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha', smul_zero]

def midSub (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {a b} ha hb := fun i j h => by rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  smul_mem' c a ha := fun i j h => by rw [Matrix.smul_apply, ha i j h, smul_zero]

theorem lie_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  intro k r x
  have h2 := mem_lieE_iff (S := Formalism.FourierDecayAlt.B2.UWb k r) (skewSub (Hpk k r) ⊓ midSub k r) (mem_lieOf_UWb k r) x
  refine ⟨mem_lieE_iff (skewSub (Hpk k r)) (mem_lieOf_UH _ (hpkFacts k r).2.1) x, h2, fun hx => ?_⟩
  have h := (mem_lieOf_UWb k r _).2 (h2.1 hx) 1
  simpa using h

end GlobalTheory.CellLieAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntriesStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  first | exact @GlobalTheory.CellLieAlg.lie_entries | exact GlobalTheory.CellLieAlg.lie_entries | (intros; apply GlobalTheory.CellLieAlg.lie_entries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

variable {k r : ℕ}

def oneM (k r : ℕ) : Mt k r := fun i j => (1 : Mat k r) i j

def nbd (k r : ℕ) (j : ℕ) : Set (Mt k r) := Metric.closedBall (oneM k r) (1 / ((j : ℝ) + 1))

def avgR {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℝ Wp] (μ : Measure (Mt k r)) (j : ℕ)
    (g : Mt k r → Wp) (x : Mt k r) : Wp :=
  ((μ (nbd k r j)).toReal)⁻¹ • ∫ y in nbd k r j, g (rmulM (Matrix.of x) y) ∂μ

theorem isCompact_nbd (j : ℕ) : IsCompact (nbd k r j) := by
  unfold nbd
  exact isCompact_closedBall _ _

theorem oneM_mem_nbd (j : ℕ) : oneM k r ∈ nbd k r j := by
  unfold nbd
  exact Metric.mem_closedBall_self (by positivity)

private lemma single_mem_inWb_and_Tz_pos (k r : ℕ) :
    Formalism.QuantumDeterminants.inWb k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) ∧
      0 < Formalism.QuantumDeterminants.Tz k r (Pi.single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1)) 1) := by
  constructor
  · intro i hi
    have hne : i ≠ ⟨r + k, by omega⟩ := by
      rintro rfl
      simp at hi
    simp [hne]
  · simp only [Formalism.QuantumDeterminants.Tz, Formalism.QuantumDeterminants.herm, Formalism.QuantumDeterminants.Hpk, dotProduct, mulVec, Pi.single_apply,
      Pi.star_apply, Complex.re_sum, neg_pos]
    rw [Finset.sum_eq_single (⟨r + k, by omega⟩ : Fin (2 * r + k + 1))]
    · have h1 : ¬ (r + k < r) := by omega
      simp [h1, Finset.sum_ite_eq']
    · intro b _ hb
      simp [hb]
    · simp

theorem gg_closedSub (k r : ℕ) : IsClosedSub k r (GG k r) :=
  (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r _ (single_mem_inWb_and_Tz_pos k r).1 (single_mem_inWb_and_Tz_pos k r).2).1

theorem haar_compact_lt_top {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {C : Set (Mt k r)}
    (hC : IsCompact C) : μ C < ⊤ :=
  (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).1 C hC

theorem nbd_pos {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) (j : ℕ) : 0 < μ (nbd k r j) := by
  have h1 : Matrix.of (oneM k r) = (1 : Mat k r) := by
    ext a b
    simp [oneM]
  have hone : Matrix.of (oneM k r) ∈ GG k r := by
    rw [h1]
    exact (gg_closedSub k r).2.2.1
  have hU := (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r (GG k r) μ (gg_closedSub k r) hμ).2
    (Metric.ball (oneM k r) (1 / ((j : ℝ) + 1))) Metric.isOpen_ball
    ⟨oneM k r, Metric.mem_ball_self (by positivity), hone⟩
  unfold nbd
  exact lt_of_lt_of_le hU (measure_mono Metric.ball_subset_closedBall)

end GlobalTheory.SgInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistances
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistances
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagPartialWedge

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

theorem len_castLE {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {l n : ℕ} (hl : l ≤ n)
    (y : Fin n → V) (a : Fin l) :
    majorantDistance (fun b : Fin l => y (Fin.castLE hl b)) a = majorantDistance y (Fin.castLE hl a) := by
  have ha := a.isLt
  have hS : (fun b : Fin l => y (Fin.castLE hl b)) '' {b | b < a} = y '' {b | b < Fin.castLE hl a} := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Fin.castLE hl b, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb ⊢
      exact hb
    · rintro ⟨b, hb, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb
      refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, Fin.lt_def]
        exact hb
      · exact congrArg y (Fin.ext rfl)
  unfold majorantDistance
  rw [hS]

theorem fixes_partial_wedge_and_length : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  intro k r l hl z hz
  refine ⟨fun s hs => ?_, fun g _ => ?_⟩
  ·
    obtain ⟨U, hU0, hU1, hsF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge]
    refine GlobalTheory.FlagFix.wedge_eq_of_mul _ _ (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) ?_ ?_ ?_
    · intro c a hac
      simp only [Matrix.submatrix_apply]
      refine hU0 _ _ ?_
      simp only [Fin.lt_def, Fin.val_castLE] at hac ⊢
      exact hac
    · intro c
      simp only [Matrix.submatrix_apply]
      exact hU1 _
    · intro i a
      have ha := a.isLt
      show (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
        ∑ c : Fin l, Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl c) i * U (Fin.castLE hl c) (Fin.castLE hl a)
      have h1 := congrFun (congrFun hsF i) (Fin.castLE hl a)
      simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply] at h1
      have h2 : (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
          ∑ j, s i j * Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a) j := rfl
      rw [h2, h1]
      refine Formalism.QuantumDeterminants.sum_fin_castLE hl _ ?_
      intro j hj
      show Formalism.QuantumDeterminants.fvec k r z j i * U j (Fin.castLE hl a) = 0
      rw [hU0 j (Fin.castLE hl a) ?_, mul_zero]
      rw [Fin.lt_def, Fin.val_castLE]
      omega
  ·
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge, GlobalTheory.TensLen.sum_norm_wedge]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    exact len_castLE hl (fun b : Fin (r + 1) =>
      (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a

end GlobalTheory.FlagPartialWedge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistancesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  first | exact @GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length | exact GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length | (intros; apply GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
open MeasureTheory GlobalTheory.Dec

namespace GlobalTheory.Dec

theorem integral_mul_eq_zero_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤) (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (F φ : G → ℂ) (hF : Measurable F) (hφ : Measurable φ) (hinv : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y)
    (hint : Integrable (fun y => F y * φ y) μ) (h0 : ∀ y, ∫ m, φ (m * y) ∂ν = 0) :
    ∫ y, F y * φ y ∂μ = 0 := by
  set f : G × G → ℂ := fun p => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * (F p.2 * φ p.2) with hf_def
  have hβm : Measurable fun p : G × G => β (p.1⁻¹ * p.2) :=
    hβ.comp (measurable_fst.inv.mul measurable_snd)
  have hfm : Measurable f :=
    (Complex.measurable_ofReal.comp hβm.ennreal_toReal).mul
      ((hF.comp measurable_snd).mul (hφ.comp measurable_snd))

  have hβy : ∀ y, Measurable fun m : G => β (m⁻¹ * y) := fun y =>
    hβ.comp (measurable_inv.mul_const y)
  have hfib : ∀ y, ∫ m, (β (m⁻¹ * y)).toReal ∂ν = 1 := by
    intro y
    rw [integral_toReal (hβy y).aemeasurable (Filter.Eventually.of_forall fun m => (hβt _).lt_top),
      hβ1 y, ENNReal.toReal_one]
  have hfibI : ∀ y, Integrable (fun m => (β (m⁻¹ * y)).toReal) ν := fun y =>
    integrable_toReal_of_lintegral_ne_top (hβy y).aemeasurable (by rw [hβ1 y]; exact ENNReal.one_ne_top)

  have hA : ∫ y, F y * φ y ∂μ = ∫ y, ∫ m, f (m, y) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    rw [integral_mul_const, integral_complex_ofReal, hfib y]
    simp

  have hfI : Integrable f (ν.prod μ) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · simp only [hf_def]
      exact (hfibI y).ofReal.mul_const _
    · have hn : (fun y => ∫ m, ‖f (m, y)‖ ∂ν) = fun y => ‖F y * φ y‖ := by
        funext y
        simp only [hf_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, ENNReal.abs_toReal]
        rw [integral_mul_const, hfib y, one_mul]
      rw [hn]
      exact hint.norm

  have hmp : MeasurePreserving (fun p : G × G => (p.1, p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    measurePreserving_prod_mul ν μ
  have hemb : MeasurableEmbedding (fun p : G × G => (p.1, p.1 * p.2)) :=
    (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hae : ∀ᵐ p ∂(ν.prod μ),
      f (p.1, p.1 * p.2) = ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) := by
    have h1 : ∀ᵐ p ∂(ν.prod μ), ∀ y, F (p.1 * y) = F y :=
      Measure.quasiMeasurePreserving_fst.ae hinv
    filter_upwards [h1] with p hp
    simp only [hf_def, inv_mul_cancel_left, hp]
  have hgI : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)))
      (ν.prod μ) :=
    ((hmp.integrable_comp_emb hemb).2 hfI).congr hae
  calc ∫ y, F y * φ y ∂μ
      = ∫ p, ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) ∂(ν.prod μ) := by
        rw [hA, ← integral_prod_symm f hfI, ← hmp.integral_comp hemb f]
        exact integral_congr_ae hae
    _ = ∫ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν ∂μ := integral_prod_symm _ hgI
    _ = 0 := by
        have hz : ∀ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν = 0 := by
          intro z
          simp_rw [← mul_assoc]
          rw [integral_const_mul, h0 z, mul_zero]
        simp only [hz, integral_zero]

theorem weilVanish : WeilVanish := by
  unfold WeilVanish
  intro G _ _ _ _ _ _ _ _ μ _ N ν hN hν F φ hF hφ hinv hint h0
  obtain ⟨β, hβ, hβt, hβ1⟩ := exists_measurable_cutoff_fibre_integral_one G N ν hN hν
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  have hN' : ∀ᵐ m ∂ν, m ∈ (N : Set G) := mem_ae_iff.2 hν.2.2.1
  have hae : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y := hN'.mono fun m hm y => hinv m hm y
  exact integral_mul_eq_zero_of_cutoff μ ν β hβ hβt hβ1 F φ hF hφ hae hint h0

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegralsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integral_vanishing_of_fibre_integrals : WeilVanish := by
  first | exact @GlobalTheory.Dec.weilVanish | exact GlobalTheory.Dec.weilVanish | (intros; apply GlobalTheory.Dec.weilVanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlag
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

private lemma Hpk_apply_of_lt_eq_ite (k r : ℕ) (c s : Fin (2 * r + k + 1)) (hc : c.val < r) :
    Formalism.QuantumDeterminants.Hpk k r c s = if c.val + s.val = 2 * r + k then 1 else 0 := by
  by_cases h : c.val + s.val = 2 * r + k
  · simp [Formalism.QuantumDeterminants.Hpk, hc, h]
  · have h' : ¬ r ≤ c.val := Nat.not_le.mpr hc
    simp [Formalism.QuantumDeterminants.Hpk, h, h']

private lemma Hpk_mul_apply_eq_Hpk_apply_of_lt_val (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r)
    (hcol : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (Formalism.QuantumDeterminants.eI k r a) = if i = Formalism.QuantumDeterminants.eI k r a then 1 else 0)
    (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    ∀ c : ℕ, ∀ hc : c + q.val ≤ 2 * r + k,
      (Formalism.QuantumDeterminants.Hpk k r * g) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    have hcr : c < r := by omega
    have hE : Formalism.QuantumDeterminants.eI k r ⟨c, hcr⟩ = ⟨c, by omega⟩ := Fin.ext rfl
    have h1 : (gᴴ * (Formalism.QuantumDeterminants.Hpk k r * g)) ⟨c, by omega⟩ q = Formalism.QuantumDeterminants.Hpk k r ⟨c, by omega⟩ q := by
      rw [← Matrix.mul_assoc, hU]
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨c, by omega⟩ : Fin (2 * r + k + 1))] at h1
    · have hd := hcol ⟨c, hcr⟩ ⟨c, by omega⟩ le_rfl
      rw [hE, if_pos rfl] at hd
      rw [Matrix.conjTranspose_apply, hd, star_one, one_mul] at h1
      exact h1
    · intro t _ htc
      rw [Matrix.conjTranspose_apply]
      have htc' : t.val ≠ c := fun h => htc (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne htc' with hlt | hgt
      · have h2 := ih t.val hlt (by omega)
        simp only [Fin.eta] at h2
        rw [h2, Hpk_apply_of_lt_eq_ite k r t q (by omega), if_neg (by omega), mul_zero]
      · have hz := hcol ⟨c, hcr⟩ t (by simp; omega)
        rw [hE, if_neg htc] at hz
        rw [hz, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem nset_block_unitriangular : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1),
    lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  intro k r g hg i j hlev
  obtain ⟨hU, hcol, hmid⟩ := hg
  have hU' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hU
  rw [Matrix.one_apply]
  unfold GlobalTheory.CellDens.lev at hlev
  by_cases hj : j.val < r
  · have hij : j.val ≤ i.val := by split_ifs at hlev <;> omega
    have h := hcol ⟨j.val, hj⟩ i hij
    have he : Formalism.QuantumDeterminants.eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
    rw [he] at h
    exact h
  · by_cases hj2 : j.val ≤ r + k
    · have hi : r ≤ i.val := by split_ifs at hlev <;> omega
      exact hmid i j (by omega) hj2 hi
    · have hi : r + k < i.val ∧ j.val ≤ i.val := by split_ifs at hlev <;> omega
      have hC : 2 * r + k - i.val < r := by omega
      have h := Hpk_mul_apply_eq_Hpk_apply_of_lt_val k r g hU' hcol j (by omega) (2 * r + k - i.val) (by omega)
      rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
      · rw [Hpk_apply_of_lt_eq_ite k r _ i hC, if_pos (by simp; omega), one_mul] at h
        rw [h, Hpk_apply_of_lt_eq_ite k r _ j hC]
        by_cases hij : i = j
        · subst hij
          rw [if_pos (by simp; omega), if_pos rfl]
        · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
          rw [if_neg (by simp; omega), if_neg hij]
      · intro s _ hs
        have hv : s.val ≠ i.val := fun h => hs (Fin.ext h)
        rw [Hpk_apply_of_lt_eq_ite k r _ s hC, if_neg (by simp; omega), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'

end GlobalTheory.CellDens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlagStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_block_unitriangular_flag : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  first | exact @GlobalTheory.CellDens.nset_block_unitriangular | exact GlobalTheory.CellDens.nset_block_unitriangular | (intros; apply GlobalTheory.CellDens.nset_block_unitriangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBound
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Cheb

theorem isClosed_GG (k r : ℕ) : IsClosed (GG k r) := by
  unfold GG UH
  exact isClosed_eq (by fun_prop) continuous_const

theorem measurableSet_len_gt (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) (T : ℝ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 ((LenCont.lA_Sg_continuousOn k r z).1 a) (Set.Ioi T) isOpen_Ioi
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem cheb_one {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T < l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx).le n

theorem tail_mass_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  intro k r Wp _ _ _ z νS Φ q H₁ hH _ _ hM i
  rcases i with _ | j
  · refine (setLIntegral_le_lintegral _ _).trans ?_
    refine le_mul_of_one_le_left' ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : (1 : ℝ) ≤ 4 ^ q := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one, mul_one]
    nlinarith
  · set T : ℝ := 2 ^ (j + 1) * H₁ / 2 with hTdef
    have hT' : T = 2 ^ j * H₁ := by rw [hTdef]; ring
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hT1 : 1 ≤ T := by rw [hT']; nlinarith
    have hsub : {x : Mt k r | Matrix.of x ∈ GG k r ∧ (j + 1 = 0 ∨ T < Sg k r z (Matrix.of x))} ⊆
        ⋃ a : Fin (r + 1), {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a} := by
      rintro x ⟨hx, h | h⟩
      · omega
      · unfold Sg at h
        rw [Finset.lt_fold_max] at h
        rcases h with h | ⟨a, -, h⟩
        · linarith
        · exact Set.mem_iUnion.2 ⟨a, hx, h⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_iUnion_le _ _).trans ?_)
    rw [tsum_fintype]
    have hone : ∀ a : Fin (r + 1),
        ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ T < lA k r z (Matrix.of x) a},
          (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
          ENNReal.ofReal (4 ^ q * ((2 ^ (j + 1) : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
      intro a
      refine (cheb_one νS (fun x => lA k r z (Matrix.of x) a) _ _ (measurableSet_len_gt k r z a T) T
        (by linarith) (fun x hx => hx.2) (2 * q)).trans ?_
      refine (mul_le_mul_right (hM a) _).trans (le_of_eq ?_)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hH0 : H₁ ≠ 0 := by linarith
      have h4 : (4 : ℝ) ^ q = 2 ^ (2 * q) := by rw [pow_mul]; norm_num
      rw [hT', h4, pow_succ, mul_pow, mul_pow]
      field_simp
    refine (Finset.sum_le_sum fun a _ => hone a).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_assoc ((r : ℝ) + 1),
      ENNReal.ofReal_mul (p := (r : ℝ) + 1) (by positivity)]
    congr 2
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl

end GlobalTheory.Amp.Cheb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBoundStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_mass_le_of_majorantLengthMomentBound : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ), 1 ≤ H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → ∀ i : ℕ, ∫⁻ x in {x : Mt k r | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z (Matrix.of x))}, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS Φ := by
  first | exact @GlobalTheory.Amp.Cheb.tail_mass_le | exact GlobalTheory.Amp.Cheb.tail_mass_le | (intros; apply GlobalTheory.Amp.Cheb.tail_mass_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvariance
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.YInv
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YjInv

variable {k r j : ℕ}

theorem N_ej (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin j) :
    n *ᵥ bvec (eI k r (Fin.castLE hj a)) =
      ∑ b : Fin j, n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj b)) := by
  rw [N_e hn]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ((Fin.castLE_injective hj).injOn) (by simp) ?_ (by simp)
  intro b _ hb
  have hb' : j ≤ b.val := by
    by_contra h
    exact hb ⟨⟨b.val, by omega⟩, by simp, rfl⟩
  have ha := a.isLt
  rw [hn.2.1 (Fin.castLE hj a) _ (by simp [eI]; omega), if_neg, zero_smul]
  intro h
  have := congrArg Fin.val h
  simp [eI] at this
  omega

theorem N_detj (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) :
    (Matrix.of fun b a : Fin j => n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a))).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) _ le_rfl, if_pos rfl]
  · intro b a hab
    have hab' : a.val < b.val := hab
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) (eI k r (Fin.castLE hj b)) hab'.le, if_neg]
    intro h
    have := congrArg Fin.val h
    simp [eI] at this
    omega

theorem Yj_N (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (γ : Mat k r)
    {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x) := by
  have h₁' := (nSubgroup k r).2.2 _ h₁
  unfold Yj Dj
  rw [dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂), Ppos_N hz hz' h₁ h₂,
    ← gramProj_comb _ (fun a : Fin j => (n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) _ (N_detj hj h₁')]
  congr 2
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    N_ej hj h₁']
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.of_apply, ← Matrix.mulVec_mulVec]

theorem Yj_K (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) {κ : Mat k r} (hG : κ ∈ GG k r)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x := by
  have h1 : star κ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ
  have h2 : κ * star κ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ
  have hG' : star κ * Hpk k r * κ = Hpk k r := hG
  have hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1) := by
    have : κ * Hpk k r = Hpk k r * κ := by
      conv_lhs => rw [← hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.mul_sub, this, Matrix.one_mul, Matrix.mul_one]
  unfold Yj
  rw [gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ]
  · congr 2
    funext a
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ κ,
      Matrix.mul_nonsing_inv _ (det_unit hG), Matrix.one_mulVec]
  · intro p
    rw [mem_Ppos, mem_Ppos]
    simp only [Matrix.mulVec_mulVec, hc]
    refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
    · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    · have := congrArg (star κ *ᵥ ·) h
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← Matrix.mul_assoc, h1, Matrix.one_mul] at this

theorem yj_invariant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  intro k r j hj z z' γ hz hz' hγ x _
  refine ⟨fun κ hκ => Yj_K hj z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yj_N hj hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩
  rw [← Yj_N hj hz hz' γ ((nSubgroup k r).2.2 _ hρ.2) hρ.1 x]
  congr 1
  have hm : IsUnit (γ * ρ * γ⁻¹).det := det_unit hρ.2.1
  have e : γ * ρ = γ * ρ * γ⁻¹ * γ := by
    rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul _ (det_unit hγ), Matrix.mul_one]
  rw [Matrix.mul_assoc]
  conv_lhs => rw [show (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ) = (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ * γ⁻¹ * γ) from by rw [← e]]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hm, Matrix.one_mul]

end GlobalTheory.Amp.YjInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvarianceStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGramNumberNormalized_invariance : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  first | exact @GlobalTheory.Amp.YjInv.yj_invariant | exact GlobalTheory.Amp.YjInv.yj_invariant | (intros; apply GlobalTheory.Amp.YjInv.yj_invariant <;> assumption)
end
end
