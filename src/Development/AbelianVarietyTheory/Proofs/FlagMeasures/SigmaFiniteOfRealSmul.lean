module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Formalism.REAL (Jm UJ inUJ hs muG Jm_mul_self Jm_conjTranspose)

noncomputable section

namespace GlobalTheory.LeviIso

def haarLoc (j : ℕ) : Measure (Fin j → Fin j → ℂ) :=
  (volume : Measure (Fin j → Fin j → ℂ)).withDensity
    fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)

instance (j : ℕ) : SigmaFinite (haarLoc j) := by
  unfold haarLoc
  infer_instance

instance sigmaFinite_ofReal_smul {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : ℝ) :
    SigmaFinite (ENNReal.ofReal c • μ) :=
  inferInstanceAs (SigmaFinite (c.toNNReal • μ))

def IsRadial {X : Type} [MeasurableSpace X] (μ : Measure X) (q : X → ℝ) (d : ℕ) : Prop :=
  Filter.Tendsto (fun r : ℝ => μ {x | Real.sqrt (q x) ≤ r} / ENNReal.ofReal (r ^ d))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

def SpansFlag (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ k y, y ∈ W k ↔ ∃ u : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧ y = ∑ i, B i *ᵥ u i

def IsFrame (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (B₀ : Matrix (Fin n) (Fin n₀) ℂ) : Prop :=
  (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ i k, (B i)ᴴ * Jm ε * B k = 0) ∧
    (∀ i, (B i)ᴴ * B₀ = 0) ∧ B₀ᴴ * B₀ = 1 ∧ Jm ε * B₀ = B₀ * Jm ε₀ ∧
    ∑ i, B i * (B i)ᴴ + ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε + B₀ * B₀ᴴ = 1

def lev (ε : Fin n → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ)
    (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Matrix (Fin n₀) (Fin n₀) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, B i * x i * (B i)ᴴ + ∑ i, Jm ε * B i * (x i)⁻¹ᴴ * (B i)ᴴ * Jm ε + B₀ * g * B₀ᴴ

variable {ε : Fin n → Bool} {ε₀ : Fin n₀ → Bool} {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ}
  {B₀ : Matrix (Fin n) (Fin n₀) ℂ}

theorem IsFrame.J_B₀ (h : IsFrame ε ε₀ B B₀) (i : Fin a) : (B i)ᴴ * Jm ε * B₀ = 0 := by
  rw [Matrix.mul_assoc, h.2.2.2.2.2.1, ← Matrix.mul_assoc, h.2.2.2.1 i, Matrix.zero_mul]

theorem IsFrame.B₀_B (h : IsFrame ε ε₀ B B₀) (i : Fin a) : B₀ᴴ * B i = 0 := by
  have e := congrArg Matrix.conjTranspose (h.2.2.2.1 i)
  simpa [Matrix.conjTranspose_mul] using e

theorem IsFrame.B₀_J (h : IsFrame ε ε₀ B B₀) (i : Fin a) : B₀ᴴ * Jm ε * B i = 0 := by
  have e := congrArg Matrix.conjTranspose (h.J_B₀ i)
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc] using e

theorem IsFrame.sum_mul (h : IsFrame ε ε₀ B B₀) {m : Type} (y : ∀ i, Matrix m (Fin (j i)) ℂ) (i : Fin a) :
    (∑ k, y k * (B k)ᴴ) * B i = y i := by
  rw [Matrix.sum_mul, Finset.sum_eq_single i]
  · rw [Matrix.mul_assoc, h.1 i, Matrix.mul_one]
  · intro k _ hk
    rw [Matrix.mul_assoc, h.2.1 k i hk, Matrix.mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

variable (x x' : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g g' : Matrix (Fin n₀) (Fin n₀) ℂ)

theorem IsFrame.lev_mul_B (h : IsFrame ε ε₀ B B₀) (i : Fin a) : lev ε B B₀ x g * B i = B i * x i := by
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B i) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.2.2.1 k i
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * B i = B i * x i := h.sum_mul (fun k => B k * x k) i
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * B i = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s3 : B₀ * g * B₀ᴴ * B i = 0 := by
    simp only [Matrix.mul_assoc, h.B₀_B i, Matrix.mul_zero]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, add_zero, add_zero]

theorem IsFrame.lev_mul_JB (h : IsFrame ε ε₀ B B₀) (i : Fin a) :
    lev ε B B₀ x g * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
  have hJJ : ∀ {m : Type} (M : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B i) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.2.2.1 k i
  have e₀ : B₀ᴴ * (Jm ε * B i) = 0 := by
    rw [← Matrix.mul_assoc]
    exact h.B₀_J i
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * (Jm ε * B i) = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * (Jm ε * B i) = Jm ε * B i * (x i)⁻¹ᴴ := by
    rw [Matrix.sum_mul, Finset.sum_eq_single i]
    · simp only [Matrix.mul_assoc, hJJ, h.1 i, Matrix.mul_one]
    · intro k _ hk
      simp only [Matrix.mul_assoc, hJJ, h.2.1 k i hk, Matrix.mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have s3 : B₀ * g * B₀ᴴ * (Jm ε * B i) = 0 := by
    simp only [Matrix.mul_assoc, e₀, Matrix.mul_zero]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, add_zero]

theorem IsFrame.lev_mul_B₀ (h : IsFrame ε ε₀ B B₀) : lev ε B B₀ x g * B₀ = B₀ * g := by
  have eJ : ∀ k, (B k)ᴴ * (Jm ε * B₀) = 0 := fun k => by
    rw [← Matrix.mul_assoc]
    exact h.J_B₀ k
  have s1 : (∑ k, B k * x k * (B k)ᴴ) * B₀ = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by
      simp only [Matrix.mul_assoc, h.2.2.2.1 k, Matrix.mul_zero]
  have s2 : (∑ k, Jm ε * B k * (x k)⁻¹ᴴ * (B k)ᴴ * Jm ε) * B₀ = 0 := by
    rw [Matrix.sum_mul]
    exact Finset.sum_eq_zero fun k _ => by simp only [Matrix.mul_assoc, eJ, Matrix.mul_zero]
  have s3 : B₀ * g * B₀ᴴ * B₀ = B₀ * g := by
    simp only [Matrix.mul_assoc, h.2.2.2.2.1, Matrix.mul_one]
  unfold lev
  rw [Matrix.add_mul, Matrix.add_mul, s1, s2, s3, zero_add, zero_add]

theorem IsFrame.ext (h : IsFrame ε ε₀ B B₀) {m : Type} {M N : Matrix m (Fin n) ℂ} (h1 : ∀ i, M * B i = N * B i)
    (h2 : ∀ i, M * (Jm ε * B i) = N * (Jm ε * B i)) (h3 : M * B₀ = N * B₀) : M = N := by
  have h2' : ∀ i, M * Jm ε * B i = N * Jm ε * B i := fun i => by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h2 i]
  calc M = M * (1 : Matrix (Fin n) (Fin n) ℂ) := (Matrix.mul_one M).symm
    _ = N * (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← h.2.2.2.2.2.2]
      simp only [Matrix.mul_add, Matrix.mul_sum, ← Matrix.mul_assoc, h1, h2', h3]
    _ = N := Matrix.mul_one N

theorem IsFrame.lev_mul (h : IsFrame ε ε₀ B B₀) :
    lev ε B B₀ (fun i => x i * x' i) (g * g') = lev ε B B₀ x g * lev ε B B₀ x' g' := by
  refine h.ext (fun i => ?_) (fun i => ?_) ?_
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_B x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_B x g, h.lev_mul_B, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_JB x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_JB x g, h.lev_mul_JB]
    simp only [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rw [Matrix.mul_assoc (lev ε B B₀ x g), h.lev_mul_B₀ x' g', ← Matrix.mul_assoc (lev ε B B₀ x g),
      h.lev_mul_B₀ x g, h.lev_mul_B₀, Matrix.mul_assoc]

theorem lev_conjTranspose : (lev ε B B₀ x g)ᴴ = lev ε B B₀ (fun i => (x i)ᴴ) gᴴ := by
  unfold lev
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Jm_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    Matrix.mul_assoc]

theorem IsFrame.inUJ_lev (h : IsFrame ε ε₀ B B₀) (hx : ∀ i, (x i).det ≠ 0) (hg : inUJ ε₀ g) :
    inUJ ε (lev ε B B₀ x g) := by
  have hl : ∀ i, (x i)⁻¹ * x i = 1 := fun i => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hx i))
  have hr : ∀ i, (x i)ᴴ * ((x i)ᴴ)⁻¹ = 1 := fun i => by
    rw [← Matrix.conjTranspose_nonsing_inv, ← Matrix.conjTranspose_mul, hl i, Matrix.conjTranspose_one]
  have hJJ : ∀ {m : Type} (M : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hJ₀ : ∀ {m : Type} (M : Matrix (Fin n₀) m ℂ), Jm ε * (B₀ * M) = B₀ * (Jm ε₀ * M) := fun M => by
    rw [← Matrix.mul_assoc, h.2.2.2.2.2.1, Matrix.mul_assoc]
  have hg' : gᴴ * (Jm ε₀ * g) = Jm ε₀ := by
    rw [← Matrix.mul_assoc]
    exact hg
  have eB : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ) (i : Fin a)
      {m : Type} (M : Matrix (Fin (j i)) m ℂ), lev ε B B₀ y k * (B i * M) = B i * (y i * M) :=
    fun y k i {_} M => by rw [← Matrix.mul_assoc, h.lev_mul_B, Matrix.mul_assoc]
  have eJB : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ) (i : Fin a)
      {m : Type} (M : Matrix (Fin (j i)) m ℂ),
      lev ε B B₀ y k * (Jm ε * (B i * M)) = Jm ε * (B i * ((y i)⁻¹ᴴ * M)) :=
    fun y k i {_} M => by
      rw [← Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc, h.lev_mul_JB]
      simp only [Matrix.mul_assoc]
  have eB₀ : ∀ (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (k : Matrix (Fin n₀) (Fin n₀) ℂ)
      {m : Type} (M : Matrix (Fin n₀) m ℂ), lev ε B B₀ y k * (B₀ * M) = B₀ * (k * M) :=
    fun y k {_} M => by rw [← Matrix.mul_assoc, h.lev_mul_B₀, Matrix.mul_assoc]
  show (lev ε B B₀ x g)ᴴ * Jm ε * lev ε B B₀ x g = Jm ε
  rw [lev_conjTranspose]
  refine h.ext (fun i => ?_) (fun i => ?_) ?_
  · simp only [Matrix.mul_assoc, h.lev_mul_B, eJB, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose, hl, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, h.lev_mul_JB, hJJ, eB, Matrix.conjTranspose_nonsing_inv, hr,
      Matrix.mul_one]
  · simp only [Matrix.mul_assoc, h.lev_mul_B₀, hJ₀, eB₀, hg', h.2.2.2.2.2.1]

theorem IsFrame.lev_inj (h : IsFrame ε ε₀ B B₀) (e : lev ε B B₀ x g = lev ε B B₀ x' g') : x = x' ∧ g = g' := by
  have hB : ∀ i, B i * x i = B i * x' i := fun i => by
    rw [← h.lev_mul_B x g i, e, h.lev_mul_B]
  have hB₀ : B₀ * g = B₀ * g' := by
    rw [← h.lev_mul_B₀ x g, e, h.lev_mul_B₀]
  refine ⟨funext fun i => ?_, ?_⟩
  · have e' := congrArg ((B i)ᴴ * ·) (hB i)
    simpa [← Matrix.mul_assoc, h.1 i] using e'
  · have e' := congrArg (B₀ᴴ * ·) hB₀
    simpa [← Matrix.mul_assoc, h.2.2.2.2.1] using e'

def IsLeviChart (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ)
    (θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε) : Prop :=
  Measurable θ ∧
  (∀ m, m ∈ flagM ε W ↔ ∃ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) ∧ θ z = m) ∧
  (∀ z z' : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
    (∀ i, (Matrix.of (z'.1 i)).det ≠ 0) →
    θ z * θ z' = θ (fun i r s => (Matrix.of (z.1 i) * Matrix.of (z'.1 i)) r s, z.2 * z'.2) ∧
      (θ z = θ z' → z = z')) ∧
  (∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
    (∀ i, locSize j W (uMat (θ z)) i = ‖(Matrix.of (z.1 i)).det‖ ^ (-(1 : ℝ) / j i)) ∧
    ∀ g : UJ ε, (∀ i, uMat g * A i = A i * (Matrix.of (z.1 i)).map τ) → uMat g * A₀ = A₀ * (uMat z.2).map τ₀ →
      g * (θ z)⁻¹ ∈ flagN ε W) ∧
  ∀ (μ : Measure (UJ ε)) (c : ℝ), IsGaugeSub (flagM ε W) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) μ → IsGauge ε₀ c →
    μ = ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
      (ENNReal.ofReal c • muG ε₀)).map θ

end GlobalTheory.LeviIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec

variable {n : ℕ}

theorem posDef_mem_Omega {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ Omega n := by
  intro i
  have hsub : (x.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).PosDef :=
    hx.submatrix (Fin.castLE_injective _)
  exact hsub.det_pos.ne'

theorem posDef_mem_kConjNonzeroMinorsSet (ε : Fin n → Bool) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ U1 ε := by
  intro k hk
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
  rw [Matrix.inv_eq_left_inv hu, Matrix.star_eq_conjTranspose]
  apply posDef_mem_Omega
  apply hx.conjTranspose_mul_mul_same
  intro v v' h
  have h2 := congrArg (fun u => (star k).mulVec u) h
  simpa only [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] using h2

theorem continuous_leadMinor_conj (ε : Fin n → Bool) (l : ℕ) (hl : l ≤ n) :
    Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) =>
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) l hl) := by
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp ((mem_KG ε _).1 k.2).1)
  simp_rw [hinv]
  unfold leadMinor
  have hc : Continuous (fun k : KG ε => toMK k) := toMK_cont ε
  have hz : Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) => Matrix.of p.2) := continuous_snd
  exact ((((hc.comp continuous_fst).matrix_conjTranspose).matrix_mul hz).matrix_mul
    (hc.comp continuous_fst)).matrix_submatrix _ _ |>.matrix_det

theorem isOpen_kConjNonzeroMinorsSet (ε : Fin n → Bool) : IsOpen {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
  have hset : {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} =
      (Prod.snd '' {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
        leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0})ᶜ := by
    ext z
    constructor
    · rintro hz ⟨⟨k, z'⟩, ⟨i, hi⟩, rfl⟩
      exact hz (toMK k) ((mem_KG ε _).1 k.2) i hi
    · intro hz g hg i hi
      obtain ⟨k, rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
      exact hz ⟨⟨k, z⟩, ⟨i, hi⟩, rfl⟩
  rw [hset, isOpen_compl_iff]
  refine isClosedMap_snd_of_compactSpace _ ?_
  have hu : {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} =
      ⋃ i : Fin n, {p | leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} := by
    ext p; simp
  rw [hu]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_eq (continuous_leadMinor_conj ε (i.val + 1) i.isLt) continuous_const

theorem differentiable_leadMinor_mul (a b : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    Differentiable ℂ (fun z : Fin n → Fin n → ℂ => leadMinor (a * Matrix.of z * b) l hl) := by
  unfold leadMinor
  simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem IsTau.isURepOn {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w) :
    IsURepOn (Kset ε) τ := by
  obtain ⟨hfd, ⟨h1, hmul⟩, hdiff, hadj, -⟩ := h
  have hsub : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ KC ε := fun g hg =>
    ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp hg.1, Matrix.mem_unitaryGroup_iff'.mp hg.1⟩, rfl⟩, hg.2⟩
  refine ⟨⟨h1, fun a ha b hb => hmul a (hsub a ha) b (hsub b hb)⟩, ?_, ?_⟩
  · intro g hg v
    have hs : star g ∈ Formalism.REAL.Kset ε := Formalism.REAL.Kset_star ε hg
    have hgg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
    have hc : (τ (star g)).comp (τ g) = 1 := by
      rw [← hmul _ (hsub _ hs) _ (hsub _ hg), hgg, h1]
    have hv : τ (star g) (τ g v) = v := by
      rw [← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.one_apply]
    have hi : ⟪τ g v, τ g v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [hadj g (hsub g hg) v (τ g v), ← Matrix.star_eq_conjTranspose, hv]
    have h2 : ‖τ g v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) v, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · intro v
    haveI := hfd
    let bs := stdOrthonormalBasis ℂ W
    have hco : ∀ u : W, ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ g v⟫_ℂ)
        (Formalism.REAL.Kset ε) :=
      fun u => (hdiff u v).continuousOn.mono (fun g hg => hsub g hg)
    have heq : (fun g => τ g v) = fun g => ∑ i, ⟪bs i, τ g v⟫_ℂ • bs i := by
      funext g; exact (bs.sum_repr' (τ g v)).symm
    rw [heq]
    exact continuousOn_finsetSum _ fun i _ => (hco (bs i)).smul continuousOn_const

theorem psBasic : PsBasic := by
  intro n ε lam W _ _ τ w _hlam htau
  have hrep : IsURepOn (Formalism.REAL.Kset ε) τ := htau.isURepOn
  obtain ⟨hfd, -, -, -, hirr, hw, -⟩ := htau
  haveI := hfd
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hK : ∀ k : KG ε, toMK k ∈ Formalism.REAL.Kset ε := fun k => (mem_KG ε _).1 k.2
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = star (toMK k) := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp (hK k).1)
  have hτc : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hrep.2.2 w).comp_continuous (toMK_cont ε) hK
  have hPc : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have := (ContinuousLinearMap.smulRightL ℂ W W).continuous₂.comp₂ ((innerSL ℂ).continuous.comp hτc) hτc
    exact this
  refine ⟨isOpen_kConjNonzeroMinorsSet ε, fun x hx => posDef_mem_kConjNonzeroMinorsSet ε hx, ?_, ?_⟩
  · have hU := isOpen_kConjNonzeroMinorsSet ε
    have hmem : ∀ k : KG ε, ∀ z ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}, ∀ i : Fin n,
        leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ≠ 0 :=
      fun k z hz i => hz (toMK k) (hK k) i
    have hcont : ContinuousOn (Function.uncurry fun (k : KG ε) (z : Fin n → Fin n → ℂ) =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
      show ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
        Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1) •
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w)) _
      have hA : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
        unfold Phi
        exact continuousOn_finsetProd _ fun i _ =>
          (continuous_leadMinor_conj ε (i.val + 1) i.isLt).continuousOn.zpow₀ _
            fun q hq => Or.inl (hmem q.1 q.2 hq.2 i)
      have hB : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) :=
        (hPc.comp continuous_fst).continuousOn
      exact hA.smul hB
    have hdiff : ∀ k : KG ε, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
      intro k
      apply DifferentiableOn.smul_const
      unfold Phi
      have hg : ∀ i : Fin n, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := fun i =>
        ((differentiable_leadMinor_mul _ _ (i.val + 1) i.isLt).differentiableOn).zpow
          (Or.inl fun z hz => hmem k z hz i)
      have hprod : ∀ s : Finset (Fin n), DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          ∏ i ∈ s, leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp only [Finset.prod_empty]
          exact differentiableOn_const _
        · intro a s ha ih
          simp only [Finset.prod_insert ha]
          exact (hg a).mul ih
      exact hprod Finset.univ
    have hint := (GlobalTheory.differentiableOn_integral_of_holomorphic_of_continuousOn (μ := muK ε) hU hcont hdiff).1
    unfold ps
    exact DifferentiableOn.congr (hint.const_smul (Module.finrank ℂ W : ℂ)) fun z _ => rfl
  · have hI : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : KG ε → E), Continuous f →
        Integrable f (muK ε) := fun f hf =>
      integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
    have h1 : ∀ k : KG ε, Phi lam ((toMK k)⁻¹ * 1 * toMK k) = 1 := fun k => by
      rw [hinv, Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp (hK k).1, Phi_at_one]
    unfold ps
    simp_rw [h1, one_smul]
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hfd hrep hirr hw0
    have hnorm : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => by rw [hrep.2.1 _ (hK k), hw]
    let b := stdOrthonormalBasis ℂ W
    have hsum : (Module.finrank ℂ W : ℂ) * c = 1 := by
      have e1 : ∀ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = c := by
        intro i
        have hbi : ⟪b i, b i⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
        have := hc (b i) (innerSL ℂ (b i))
        simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl, hbi, mul_one] at this
        exact this
      have e2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = 1 := by
        rw [← MeasureTheory.integral_finsetSum _ fun i _ => hI (fun k : KG ε => ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ)
          ((hτc.inner continuous_const).mul (continuous_const.inner hτc))]
        simp_rw [b.sum_inner_mul_inner]
        have hone : ∀ k : KG ε, ⟪τ (toMK k) w, τ (toMK k) w⟫_ℂ = 1 := fun k => by
          rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
        simp_rw [hone]
        simp
      simp_rw [e1] at e2
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using e2
    ext u
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply (hI _ hPc),
      ContinuousLinearMap.id_apply]
    simp only [ContinuousLinearMap.smulRight_apply, show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl]
    apply ext_inner_left ℂ
    intro y
    rw [inner_smul_right, ← integral_inner (hI (fun k : KG ε => ⟪τ (toMK k) w, u⟫_ℂ • τ (toMK k) w)
      ((hτc.inner continuous_const).smul hτc))]
    simp_rw [inner_smul_right]
    have := hc u (innerSL ℂ y)
    simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl] at this
    rw [this, ← mul_assoc, hsum, one_mul]

end GlobalTheory.Dec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOneStatement
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one : PsBasic := by
  first | exact @GlobalTheory.Dec.psBasic | exact GlobalTheory.Dec.psBasic | (intros; apply GlobalTheory.Dec.psBasic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.OrbitTerm

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

def oneInf (E : Type) [Field E] [NumberField E] (j : ℕ) : MatInf E j := fun _ a b => if a = b then 1 else 0

theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := by
  ext a b; simp [oneInf, Matrix.one_apply]

theorem of_mul (x y : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl

theorem matInf_ext {x y : MatInf E j} (h : ∀ w, Matrix.of (x w) = Matrix.of (y w)) : x = y :=
  funext fun w => Matrix.of.injective (h w)

theorem matInf_mul_assoc (x y z : MatInf E j) : x * y * z = x * (y * z) :=
  matInf_ext fun w => by simp only [of_mul, Matrix.mul_assoc]

theorem oneInf_mul (x : MatInf E j) : oneInf E j * x = x :=
  matInf_ext fun w => by rw [of_mul, of_oneInf, Matrix.one_mul]

theorem mul_oneInf (x : MatInf E j) : x * oneInf E j = x :=
  matInf_ext fun w => by rw [of_mul, of_oneInf, Matrix.mul_one]

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  simp only [detNorm, of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem detNorm_oneInf : detNorm E j (oneInf E j) = 1 := by
  simp [detNorm, of_oneInf]

theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem detNorm_pos_iff (x : MatInf E j) : 0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  rw [(detNorm_nonneg x).lt_iff_ne', detNorm, Finset.prod_ne_zero_iff]
  simp

theorem measurable_entry (w : InfinitePlace E) (a b : Fin j) : Measurable fun x : MatInf E j => x w a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    (measurable_pi_apply (X := fun _ : InfinitePlace E => Fin j → Fin j → ℂ) w))

theorem measurable_detNorm : Measurable (detNorm E j) := by
  have h : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2 := by
    refine continuous_finsetProd _ fun w _ => Continuous.pow (Continuous.norm ?_) 2
    exact Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)
  exact h.measurable

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
  measurableSet_lt measurable_const measurable_detNorm

theorem measurable_mul_left (γ : MatInf E j) : Measurable fun g : MatInf E j => γ * g := by
  refine Measurable.of_eval (X := fun _ : InfinitePlace E => Fin j → Fin j → ℂ) fun w =>
    Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  show Measurable fun g : MatInf E j => ∑ c, γ w a c * g w c b
  exact Finset.measurable_sum _ fun c _ => (measurable_entry w c b).const_mul _

theorem measurable_inv_entry (w : InfinitePlace E) (a b : Fin j) :
    Measurable fun g : MatInf E j => (Matrix.of (g w))⁻¹ a b := by
  have h1 : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (x w)).det :=
    Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)
  have h2 : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (x w)).adjugate a b :=
    (Continuous.matrix_adjugate (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)).matrix_elem a b
  have h3 := h1.measurable.inv.mul h2.measurable
  have : (fun g : MatInf E j => (Matrix.of (g w))⁻¹ a b) =
      fun g : MatInf E j => ((Matrix.of (g w)).det)⁻¹ * (Matrix.of (g w)).adjugate a b := by
    funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']; rfl
  rw [this]; exact h3

theorem haarGL_singular (hj : 1 ≤ j) : haarGL E j {g | 0 < detNorm E j g}ᶜ = 0 := by
  have hm : MeasurableSet {g : MatInf E j | 0 < detNorm E j g}ᶜ := measurableSet_detNorm_pos.compl
  unfold haarGL
  erw [withDensity_apply _ hm]
  refine setLIntegral_eq_zero hm fun g hg => ?_
  have h0 : detNorm E j g = 0 := le_antisymm (not_lt.1 hg) (detNorm_nonneg g)
  simp [h0, zero_pow (by omega : j ≠ 0)]

theorem haarGL_restrict (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j :=
  Measure.restrict_eq_self_of_ae_mem (haarGL_singular hj)

instance : SigmaFinite (haarGL E j) :=
  haveI : SigmaFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin j → ℂ)) := inferInstance
  @SigmaFinite.withDensity_ofReal (InfinitePlace E → Fin j → Fin j → ℂ) _ volume inferInstance
    fun x => (detNorm E j x)⁻¹ ^ j

def embGL (γ : GL (Fin j) E) : MatInf E j := fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

theorem embGL_mul (γ δ : GL (Fin j) E) : embGL (γ * δ) = embGL γ * embGL δ := by
  funext w a b
  show embGL (γ * δ) w a b = ∑ c, embGL γ w a c * embGL δ w c b
  simp [embGL, Matrix.mul_apply]

theorem embGL_one : embGL (1 : GL (Fin j) E) = oneInf E j := by
  funext w a b
  simp only [embGL, oneInf, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} : x ∈ autGL E j Λ ↔
    ∃ γ : GL (Fin j) E, (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧ x = embGL γ :=
  ⟨fun ⟨γ, h, h'⟩ => ⟨γ, h, funext fun w => funext fun a => funext fun b => h' w a b⟩,
    fun ⟨γ, h, h'⟩ => ⟨γ, h, fun _ _ _ => by rw [h']; rfl⟩⟩

theorem countable_autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : (autGL E j Λ).Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  have : Countable (GL (Fin j) E) := Units.val_injective.countable
  refine (Set.countable_range (embGL : GL (Fin j) E → MatInf E j)).mono fun x hx => ?_
  obtain ⟨γ, -, rfl⟩ := mem_autGL.1 hx
  exact ⟨γ, rfl⟩

theorem oneInf_mem_autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : oneInf E j ∈ autGL E j Λ :=
  mem_autGL.2 ⟨1, by simp, embGL_one.symm⟩

theorem mul_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x y : MatInf E j} (hx : x ∈ autGL E j Λ)
    (hy : y ∈ autGL E j Λ) : x * y ∈ autGL E j Λ := by
  obtain ⟨γ, h, rfl⟩ := mem_autGL.1 hx
  obtain ⟨δ, h', rfl⟩ := mem_autGL.1 hy
  refine mem_autGL.2 ⟨γ * δ, fun z => ?_, (embGL_mul γ δ).symm⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h, h']

theorem exists_inv_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ autGL E j Λ) :
    ∃ y ∈ autGL E j Λ, y * x = oneInf E j ∧ x * y = oneInf E j := by
  obtain ⟨γ, h, rfl⟩ := mem_autGL.1 hx
  refine ⟨embGL γ⁻¹, mem_autGL.2 ⟨γ⁻¹, fun z => ?_, rfl⟩, ?_, ?_⟩
  · rw [← h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rw [← embGL_mul, inv_mul_cancel, embGL_one]
  · rw [← embGL_mul, mul_inv_cancel, embGL_one]

theorem detNorm_pos_of_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ autGL E j Λ) :
    0 < detNorm E j x := by
  obtain ⟨y, -, h, -⟩ := exists_inv_mem_autGL hx
  have h1 := detNorm_mul y x
  rw [h, detNorm_oneInf] at h1
  refine (detNorm_nonneg x).lt_of_ne' fun h0 => ?_
  rw [h0, mul_zero] at h1
  exact one_ne_zero h1

theorem covol_eq_of_aedisjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X) (A D : Set X)
    (hS : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x) (hμ : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hinv : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hD : MeasurableSet D) (hDA : D ⊆ A) (hcov : ∀ x ∈ A, ∃ γ ∈ S, γ * x ∈ D)
    (hdis : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → μ {x | γ * x ∈ D ∧ δ * x ∈ D} = 0) : covol S μ A = μ D := by
  apply le_antisymm
  · unfold covol
    exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le hcov le_rfl))
  unfold covol
  refine le_iInf fun C => le_iInf fun hC => le_iInf fun hCc => ?_
  have : Countable S := hS.to_subtype
  choose inv hinvS hl hr using hinv
  have h1 : D ⊆ ⋃ δ : S, (fun x => inv δ δ.2 * x) ⁻¹' (C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hCc x (hDA hx)
    refine Set.mem_iUnion.2 ⟨⟨inv γ hγ, hinvS γ hγ⟩, ?_, ?_⟩
    · have e : inv (inv γ hγ) (hinvS γ hγ) * x = γ * x := by
        conv_lhs => rw [← hl γ hγ x, hl]
      show inv (inv γ hγ) (hinvS γ hγ) * x ∈ C
      rw [e]; exact hγx
    · show inv γ hγ * (inv (inv γ hγ) (hinvS γ hγ) * x) ∈ D
      rw [hr]; exact hx
  have hmeas : ∀ δ : S, MeasurableSet (C ∩ (fun x => δ.1 * x) ⁻¹' D) := fun δ => hC.inter (hm δ δ.2 hD)
  calc μ D ≤ ∑' δ : S, μ ((fun x => inv δ δ.2 * x) ⁻¹' (C ∩ (fun x => δ.1 * x) ⁻¹' D)) :=
        (measure_mono h1).trans (measure_iUnion_le _)
    _ = ∑' δ : S, μ (C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
        refine tsum_congr fun δ => ?_
        rw [← Measure.map_apply (hm _ (hinvS δ δ.2)) (hmeas δ), hμ _ (hinvS δ δ.2)]
    _ = μ (⋃ δ : S, C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
        refine (measure_iUnion₀ (fun γ δ hne => ?_) fun δ => (hmeas δ).nullMeasurableSet).symm
        refine measure_mono_null (fun x hx => ?_) (hdis γ γ.2 δ δ.2 fun h => hne (Subtype.ext h))
        exact ⟨hx.1.2, hx.2.2⟩
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun δ => Set.inter_subset_left)

end GlobalTheory.OrbitTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularOfContracted
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped NNReal ENNReal

namespace GlobalTheory.ModularAutomorphism

section Group

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem smul_haar_cancel (ρ : Measure H) [ρ.IsHaarMeasure] {c d : ℝ≥0} (h : c • ρ = d • ρ) : c = d := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hK1).ne'
  have h1 : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have h2 : (c : ℝ≥0∞) * ρ K = (d : ℝ≥0∞) * ρ K := by
    have := congrArg (fun τ : Measure H => τ K) h
    exact this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 h2)

theorem map_right_eq (ρ : Measure H) [ρ.IsHaarMeasure] (g : H) :
    ρ.map (· * g) = modularCharacterFun g • ρ := by
  rw [modularCharacterFun_eq_haarScalarFactor ρ g]
  exact isMulLeftInvariant_eq_smul _ ρ

theorem modular_aut (φ : H ≃ₜ* H) (g : H) : modularCharacterFun (φ g) = modularCharacterFun g := by
  let ρ : Measure H := Measure.haar
  have hφ : Measurable φ := φ.continuous.measurable
  haveI : (ρ.map φ).IsHaarMeasure := φ.toMulEquiv.isHaarMeasure_map ρ φ.continuous φ.symm.continuous
  apply smul_haar_cancel (ρ.map φ)
  rw [← map_right_eq, ← Measure.map_smul, ← map_right_eq, map_map (measurable_mul_const _) hφ,
    map_map hφ (measurable_mul_const _)]
  · congr 1
    funext x
    simp
  · exact hφ.aemeasurable

theorem continuous_modular : Continuous fun g : H => (modularCharacterFun g : ℝ) := by
  let ρ : Measure H := Measure.haar
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : H)
  have hI : ∫ x, f x ∂ρ ≠ 0 :=
    ne_of_gt (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1)
  have hc : Continuous fun x : H => ∫ y, f (y⁻¹ * x) ∂ρ.inv :=
    continuous_integral_apply_inv_mul f.continuous hfc
  have he : ∀ g : H, (modularCharacterFun g : ℝ) = (∫ y, f (y⁻¹ * g) ∂ρ.inv) / ∫ x, f x ∂ρ := by
    intro g
    rw [modularCharacterFun_eq_haarScalarFactor ρ g,
      haarScalarFactor_eq_integral_div _ _ f.continuous hfc hI,
      integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      Measure.inv_def, integral_map measurable_inv.aemeasurable
        (by fun_prop : Continuous fun y : H => f (y⁻¹ * g)).aestronglyMeasurable]
    simp
  simp_rw [he]
  exact hc.div_const _

theorem map_inv_eq (ρ : Measure H) [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant] : ρ.inv = ρ := by
  have h : ρ.inv = haarScalarFactor ρ.inv ρ • ρ := isMulLeftInvariant_eq_smul _ ρ
  set c := haarScalarFactor ρ.inv ρ
  have h2 : (c * c) • ρ = (1 : ℝ≥0) • ρ := by
    have h3 : ρ.inv.inv = c • ρ.inv := by
      conv_lhs => rw [h]
      rw [Measure.inv_def, Measure.map_smul, ← Measure.inv_def]
      exact measurable_inv.aemeasurable
    rw [Measure.inv_inv, h, smul_smul] at h3
    rw [one_smul]
    exact h3.symm
  have h4 : c * c = 1 := smul_haar_cancel ρ h2
  have h5 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast h4
    have h0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [h, h5, one_smul]

end Group

def conjAut {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G) (b : G)
    (h1 : ∀ m ∈ N, b * m * b⁻¹ ∈ N) (h2 : ∀ m ∈ N, b⁻¹ * m * b ∈ N) : N ≃ₜ* N where
  toFun m := ⟨b * m * b⁻¹, h1 m m.2⟩
  invFun m := ⟨b⁻¹ * m * b, h2 m m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' m n := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

theorem unimodular_of_contracted {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G} (hν : GlobalTheory.Dec.IsHaarSub (N : Set G) ν)
    (a : ℝ → G) (h1 : ∀ s : ℝ, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s : ℝ, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Tendsto (fun s : ℝ => a s * m * (a s)⁻¹) atBot (nhds (1 : G))) :
    (∀ m ∈ N, ν.map (fun x : G => x * m) = ν) ∧ ν.map (fun x : G => x⁻¹) = ν := by
  obtain ⟨hne, hfin, hcar, hleft⟩ := hν
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hE : MeasurableEmbedding (Subtype.val : N → G) := MeasurableEmbedding.subtype_coe hN.measurableSet
  have hv : Measurable (Subtype.val : N → G) := hE.measurable
  let μ : Measure N := ν.comap Subtype.val
  have hμ : μ.map Subtype.val = ν := by
    rw [hE.map_comap, Subtype.range_coe_subtype]
    exact Measure.restrict_eq_self_of_ae_mem hcar
  haveI : μ.IsMulLeftInvariant := ⟨fun g => by
    apply hE.map_injective
    change (μ.map (g * ·)).map Subtype.val = μ.map Subtype.val
    have : (Subtype.val : N → G) ∘ (g * ·) = (fun x : G => (g : G) * x) ∘ Subtype.val := rfl
    rw [map_map hv (measurable_const_mul g), this, ← map_map (measurable_const_mul _) hv, hμ, hleft g g.2]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [hE.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top⟩
  haveI : NeZero μ := ⟨fun h => hne (by rw [← hμ, h, Measure.map_zero])⟩
  haveI : TopologicalSpace.PseudoMetrizableSpace N := inferInstance
  haveI : μ.Regular := inferInstance
  haveI : μ.IsHaarMeasure := {}
  have hmod : ∀ g : N, modularCharacterFun g = 1 := by
    intro g
    have t1 : Tendsto (fun s : ℝ => conjAut N (a s) (h1 s) (h2 s) g) atBot (nhds (1 : N)) :=
      tendsto_subtype_rng.2 (h3 g g.2)
    have t2 := ((continuous_modular (H := N)).tendsto 1).comp t1
    simp only [Function.comp_def, modular_aut, modularCharacterFun_map_one] at t2
    exact_mod_cast tendsto_const_nhds_iff.1 t2
  have hr : ∀ g : N, μ.map (· * g) = μ := fun g => by rw [map_right_eq, hmod, one_smul]
  haveI : μ.IsMulRightInvariant := ⟨hr⟩
  refine ⟨fun m hm => ?_, ?_⟩
  · have : (fun x : G => x * m) ∘ (Subtype.val : N → G) = Subtype.val ∘ (· * (⟨m, hm⟩ : N)) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map (measurable_mul_const m) hv, this, ← map_map hv (measurable_mul_const _), hr, hμ]
  · have : (fun x : G => x⁻¹) ∘ (Subtype.val : N → G) = Subtype.val ∘ (Inv.inv : N → N) := rfl
    conv_lhs => rw [← hμ]
    rw [map_map measurable_inv hv, this, ← map_map hv measurable_inv, ← Measure.inv_def, map_inv_eq, hμ]

end GlobalTheory.ModularAutomorphism
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.UnipUnimod

section General

open scoped Pointwise NNReal ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem unimod_of_contract (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G}
    (h : IsHaarSub (N : Set G) ν) (a : ℝ → G) (h1 : ∀ s, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) :
    (∀ m ∈ N, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first
  | exact @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | (apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted ..)

end General

theorem unimodular_NW : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  intro n ε W ν hW hν
  obtain ⟨a, Hm, -, ha, -, h1, h3, -⟩ := GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup n ε W hW
  have hinv : ∀ s, a (-s) = (a s)⁻¹ := fun s => by
    refine eq_inv_of_mul_eq_one_left (Subtype.ext (Units.ext ?_))
    change umat (a (-s)) * umat (a s) = 1
    rw [ha, ha, Complex.ofReal_neg, neg_smul,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl ((s : ℂ) • Hm)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  refine unimod_of_contract (nwSub ε W) (isClosed_NW ε W) hν a (fun s m hm => (h1 s m hm).1)
    (fun s m hm => ?_) h3
  have := (h1 (-s) m hm).1
  rwa [hinv, inv_inv] at this

end GlobalTheory.UnipUnimod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariantStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_subgroup_bi_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first | exact @GlobalTheory.UnipUnimod.unimodular_NW | exact GlobalTheory.UnipUnimod.unimodular_NW | (intros; apply GlobalTheory.UnipUnimod.unimodular_NW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtBoundOfDecGap
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

theorem ptBound_of_decGap : GlobalTheory.DSId.DecGap → GlobalTheory.Deep.PtBound := by
  intro hD B d p q h hDS hsig hgap hh
  obtain ⟨him, hre, hle, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hrk : ∀ v, rkR (B.I.ε v) = min p q := fun v => by
    rw [← (hsig v).1, ← (hsig v).2]; rfl
  have hw : ∀ v, ‖B.w v‖ = 1 := fun v => (hDS v).2.2.1.1
  have hdec := fun v (g : UJ (B.I.ε v)) =>
    hD B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) (hDS v).1 (hDS v).2.1 h (hgap v)
      (by rw [hrk v]; exact hh) (uMat g) g.2 (B.w v) (hDS v).2.2.1.2 (B.w v) (hDS v).2.2.1.2
  have hd : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hDS v).2.2.2.1.le
  have key : ∀ (y : B.I.GA) (c : InfinitePlace B.I.F → ℝ),
      (∀ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ c v) →
      ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re * ∏ v, c v := by
    intro y c hc
    have h1 : ∏ v, ‖⟪B.w v, B.σ v (uMat (y.1 v)) (B.w v)⟫_ℂ‖ ≤ ∏ v, c v :=
      Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hc v
    have h0 : 0 ≤ ∏ v, c v := (Finset.prod_nonneg fun v _ => norm_nonneg _).trans h1
    unfold phe ph
    rw [norm_mul, norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hd, mul_right_comm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hle _) hd) h1
      (Finset.prod_nonneg fun v _ => norm_nonneg _) (mul_nonneg hd hre)
  refine ⟨fun _ y => key y _ fun v => ?_, fun y => ?_, ?_, him, hre, fun y hy => ?_, fun v g => ?_⟩
  · have := (hdec v (y.1 v)).1
    rw [hw, mul_one, mul_one, hrk] at this
    exact this
  · have := key y (fun _ => 1) fun v => by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [(hDS v).2.1.2.2.1.2.1 _ (y.1 v).2, hw, mul_one]
    simpa using this
  · have h1 : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.GA).1 v)) (B.w v)⟫_ℂ = 1 := fun v => by
      have e : uMat ((1 : B.I.GA).1 v) = 1 := rfl
      rw [e, (hDS v).2.1.2.2.1.1.1]
      simp [inner_self_eq_norm_sq_to_K, hw]
    unfold phe ph
    simp only [h1, Finset.prod_const_one, star_one, mul_one]
    rfl
  · exact B.e_adm.2.2.2.2.1 _ (right_ne_zero_of_mul hy)
  · have := (hdec v g).2
    rwa [hw, mul_one, mul_one] at this

end GlobalTheory.Deep
end
