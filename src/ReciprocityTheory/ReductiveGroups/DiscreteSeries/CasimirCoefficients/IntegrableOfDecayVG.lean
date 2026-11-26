module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.SignedIdentityColumns
noncomputable section

open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev SgIxV (ε : Fin n → Bool) (s : Bool) : Type := {a : Fin n // ε a = s}

lemma hs_contVG : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2

lemma hs_nonnegVG (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A := by
  unfold hs
  positivity

lemma hs_entry_leVG (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs g := by
  unfold hs
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

lemma hs_oneVG (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp [hs, Matrix.one_apply, apply_ite]

lemma toM_mulVG {ε : Fin n → Bool} (g h : UJ ε) : toM (g * h) = toM g * toM h := rfl

lemma toM_mul_invVG {ε : Fin n → Bool} (g : UJ ε) : toM g * toM g⁻¹ = 1 := by
  unfold toM
  rw [Subgroup.coe_inv, Units.mul_inv]

private lemma Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

lemma gJgH_VG {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * Jm ε * gᴴ = Jm ε := by
  have hJ := Jm_mul_self_eq_one' ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJ]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]

lemma normSq_detVG {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Complex.normSq g.det = 1 := by
  have hJ := Jm_mul_self_eq_one' ε
  have hJ0 : (Jm ε).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJ
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hdet := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hdet
  have h2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hJ0
    calc star g.det * g.det * (Jm ε).det = star g.det * (Jm ε).det * g.det := by ring
      _ = (Jm ε).det := hdet
      _ = 1 * (Jm ε).det := by ring
  have h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

section supnorm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma ballFiniteVG (ε : Fin n → Bool) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (R : ℝ) :
    ν {g | hs (toM g) ≤ R} < ⊤ := by
  classical
  have hJ := Jm_mul_self_eq_one' ε
  let K : Set (Matrix (Fin n) (Fin n) ℂ) := {M | inUJ ε M ∧ hs M ≤ R}
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · change IsClosed ({M : Matrix (Fin n) (Fin n) ℂ | Mᴴ * Jm ε * M = Jm ε} ∩
        {M : Matrix (Fin n) (Fin n) ℂ | hs M ≤ R})
      apply IsClosed.inter
      · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
          continuous_id) continuous_const
      · exact isClosed_le hs_contVG continuous_const
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨max 1 R, fun M hM => ?_⟩
      rw [Matrix.norm_le_iff (le_trans zero_le_one (le_max_left _ _))]
      intro i j
      have h1 := le_trans (hs_entry_leVG M i j) hM.2
      have h0 := norm_nonneg (M i j)
      by_cases hc : ‖M i j‖ ≤ 1
      · exact le_trans hc (le_max_left _ _)
      · push_neg at hc
        have : ‖M i j‖ ≤ ‖M i j‖ ^ 2 := by nlinarith
        exact le_trans (le_trans this h1) (le_max_right _ _)
  let e : UJ ε → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun g => Units.embedProduct _ (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have he : Topology.IsInducing e :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  let ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))
  have hψ : Continuous ψ :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hinv : ∀ M : Matrix (Fin n) (Fin n) ℂ, inUJ ε M →
      (Jm ε * Mᴴ * Jm ε) * M = 1 ∧ M * (Jm ε * Mᴴ * Jm ε) = 1 := by
    intro M hM
    have hM' : Mᴴ * Jm ε * M = Jm ε := hM
    have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', hJ]
    exact ⟨h1, mul_eq_one_comm.mp h1⟩
  have himg : e '' {g | hs (toM g) ≤ R} = ψ '' K := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨toM g, ⟨g.2, hg⟩, ?_⟩
      have hinvg : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
          Matrix (Fin n) (Fin n) ℂ) = Jm ε * (toM g)ᴴ * Jm ε :=
        Units.inv_eq_of_mul_eq_one_right (hinv (toM g) g.2).2
      simp only [ψ, e, Units.embedProduct_apply, hinvg]
    · rintro ⟨M, ⟨hM, hR⟩, rfl⟩
      let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Jm ε * Mᴴ * Jm ε, (hinv M hM).2, (hinv M hM).1⟩
      refine ⟨⟨u, hM⟩, hR, ?_⟩
      simp only [ψ, e, Units.embedProduct_apply]
      rfl
  have hS : IsCompact {g : UJ ε | hs (toM g) ≤ R} := by
    rw [he.isCompact_iff, himg]
    exact hKc.image hψ
  exact hS.measure_lt_top

end supnorm

def hsRV {Q : Type} [Fintype Q] (x : Matrix (Fin n) Q ℂ) : ℝ := ∑ i, ∑ j, ‖x i j‖ ^ 2

def signedIdentityColumns (ε : Fin n → Bool) (s : Bool) : Matrix (Fin n) (SgIxV ε s) ℂ := fun a b => if a = b.1 then 1 else 0

lemma hsRV_cont {Q : Type} [Fintype Q] : Continuous (hsRV : Matrix (Fin n) Q ℂ → ℝ) := by
  unfold hsRV
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2

lemma hsRV_entry_le {Q : Type} [Fintype Q] (g : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) : ‖g i j‖ ^ 2 ≤ hsRV g := by
  unfold hsRV
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

lemma mul_P0V_apply (ε : Fin n → Bool) (s : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (b : SgIxV ε s) :
    (g * signedIdentityColumns ε s) i b = g i b.1 := by
  simp [Matrix.mul_apply, signedIdentityColumns]

lemma sum_SgIxV (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℝ) :
    ∑ b : SgIxV ε s, f b.1 = ∑ j, if ε j = s then f j else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun j => ε j = s) (fun x => by simp) f).symm

lemma hsRV_P0V_le (ε : Fin n → Bool) (s : Bool) : hsRV (signedIdentityColumns ε s) ≤ n := by
  have h1 : hsRV (signedIdentityColumns ε s) = Fintype.card (SgIxV ε s) := by
    unfold hsRV signedIdentityColumns
    rw [Finset.sum_comm]
    simp [apply_ite]
  rw [h1]
  have h2 := Fintype.card_subtype_le (fun a : Fin n => ε a = s)
  have h3 : ((Fintype.card (SgIxV ε s) : ℕ) : ℝ) ≤ ((Fintype.card (Fin n) : ℕ) : ℝ) := by
    exact_mod_cast h2
  simpa using h3

lemma hs_le_colsV {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    hs g ≤ n + 2 * hsRV (g * signedIdentityColumns ε s) := by
  have h := gJgH_VG hg
  let σ : Fin n → ℝ := fun a => if ε a then 1 else -1
  have hJσ : Jm ε = Matrix.diagonal fun a => ((σ a : ℝ) : ℂ) := by
    unfold Jm
    congr 1
    funext a
    by_cases ha : ε a = true <;> simp [σ, ha]
  have hterm : ∀ i j, g i j * ((σ j : ℝ) : ℂ) * star (g i j) = ((σ j * ‖g i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i j
    rw [mul_comm (g i j), mul_assoc, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  have hrow : ∀ i, ∑ j, σ j * ‖g i j‖ ^ 2 = σ i := by
    intro i
    have h1 := congrFun (congrFun h i) i
    rw [hJσ, Matrix.mul_apply] at h1
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, hterm] at h1
    exact_mod_cast h1
  have hcols : hsRV (g * signedIdentityColumns ε s) = ∑ i, ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0 := by
    unfold hsRV
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_P0V_apply]
    exact sum_SgIxV ε s (fun j => ‖g i j‖ ^ 2)
  have hpt : ∀ i j, ‖g i j‖ ^ 2 = (if s then -1 else 1) * (σ j * ‖g i j‖ ^ 2) +
      2 * (if ε j = s then ‖g i j‖ ^ 2 else 0) := by
    intro i j
    by_cases h1 : ε j = true <;> cases s <;> simp [σ, h1] <;> ring
  have hσ : ∀ i, (if s then (-1:ℝ) else 1) * σ i ≤ 1 := by
    intro i
    by_cases h1 : ε i = true <;> cases s <;> simp [σ, h1]
  unfold hs
  rw [hcols]
  calc ∑ i, ∑ j, ‖g i j‖ ^ 2
      = ∑ i, ((if s then -1 else 1) * σ i + 2 * ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun j _ => hpt i j, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hrow i]
    _ ≤ ∑ i : Fin n, (1 + 2 * ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ => by linarith [hσ i]
    _ = n + 2 * ∑ i, ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp

def LcV {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) Q ℂ →ₗ[ℂ] Matrix (Fin n) Q ℂ where
  toFun x := g * x
  map_add' := Matrix.mul_add g
  map_smul' c x := by simp

lemma stdBasis_reprV {Q : Type} [Fintype Q] [DecidableEq Q] (x : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) :
    (Matrix.stdBasis ℂ (Fin n) Q).repr x (i, j) = x i j := by
  first
    | rfl
    | (simp [Matrix.stdBasis]; done)
    | (simp [Matrix.stdBasis, Basis.reindex_repr, Pi.basis_repr]; done)

lemma LcV_det {Q : Type} [Fintype Q] [DecidableEq Q] (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (LcV (Q := Q) g) = g.det ^ Fintype.card Q := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) Q)]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) Q) (Matrix.stdBasis ℂ (Fin n) Q) (LcV (Q := Q) g) =
      Matrix.kroneckerMap (fun x1 x2 => x1 * x2) g (1 : Matrix Q Q ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_reprV, Matrix.stdBasis_eq_single]
    simp [LcV, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Ne.symm hlj]
  rw [h, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]

abbrev REV (n : ℕ) (Q : Type) := Fin n → Q → ℂ

def ReV (n : ℕ) (Q : Type) : REV n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ := Matrix.ofLinearEquiv ℝ

def RLV {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : REV n Q →ₗ[ℝ] REV n Q :=
  ((ReV n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] REV n Q) ∘ₗ ((LcV (Q := Q) g).restrictScalars ℝ) ∘ₗ
    ((ReV n Q : REV n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ) : REV n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ)

lemma RLV_apply {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) (x : REV n Q) :
    RLV g x = Matrix.of.symm (g * Matrix.of x) := rfl

lemma of_RLV {Q : Type} [Fintype Q] (A : Matrix (Fin n) (Fin n) ℂ) (x : REV n Q) :
    Matrix.of (RLV A x) = A * Matrix.of x := by
  rw [RLV_apply]
  exact Matrix.of.apply_symm_apply _

lemma RLV_det {Q : Type} [Fintype Q] [DecidableEq Q] {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : LinearMap.det (RLV (Q := Q) g) = 1 := by
  have h1 : RLV (Q := Q) g = ((ReV n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] REV n Q) ∘ₗ
      ((LcV (Q := Q) g).restrictScalars ℝ) ∘ₗ
      (((ReV n Q).symm).symm : REV n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ) := rfl
  rw [h1, LinearMap.det_conj, LinearMap.det_restrictScalars, LcV_det, Algebra.norm_complex_apply, map_pow,
    normSq_detVG hg, one_pow]

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma hs_eq_frobVG (A : Matrix (Fin n) (Fin n) ℂ) : hs A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  unfold hs
  simp only [Real.rpow_two]

lemma hsRV_eq {Q : Type} [Fintype Q] (A : Matrix (Fin n) Q ℂ) : hsRV A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  unfold hsRV
  simp only [Real.rpow_two]

lemma norm_P0V_le (ε : Fin n → Bool) (s : Bool) : ‖signedIdentityColumns ε s‖ ≤ Real.sqrt n := by
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (by rw [← hsRV_eq]; exact hsRV_P0V_le ε s))

lemma normRV_lt {Q : Type} [Fintype Q] {u : Matrix (Fin n) Q ℂ} (hu : hsRV u < 1 / 16) : ‖u‖ < 1 / 4 := by
  rw [hsRV_eq] at hu
  nlinarith [norm_nonneg u]

lemma normRV_u {ε : Fin n → Bool} {s : Bool} {u : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) :
    ‖u‖ ≤ Real.sqrt n + 1 / 4 := by
  have h1 := normRV_lt hu
  have h2 := norm_P0V_le ε s
  calc ‖u‖ = ‖signedIdentityColumns ε s + (u - signedIdentityColumns ε s)‖ := by rw [add_sub_cancel]
    _ ≤ ‖signedIdentityColumns ε s‖ + ‖u - signedIdentityColumns ε s‖ := norm_add_le _ _
    _ ≤ Real.sqrt n + 1 / 4 := by linarith

lemma smallRV {ε : Fin n → Bool} {s : Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {u v : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (hv : hsRV (v - signedIdentityColumns ε s) < 1 / 16)
    (h : k * u = v) : hs k ≤ n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := by
  have hk' := hs_le_colsV s hk
  have hw := normRV_lt hu
  have hvn := normRV_u hv
  have hr0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hr2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have e1 : k * signedIdentityColumns ε s = v - k * (u - signedIdentityColumns ε s) := by
    rw [Matrix.mul_sub, h]
    abel
  have ha : ‖k * signedIdentityColumns ε s‖ ≤ ‖v‖ + ‖k‖ * ‖u - signedIdentityColumns ε s‖ := by
    have m1 : ‖k * (u - signedIdentityColumns ε s)‖ ≤ ‖k‖ * ‖u - signedIdentityColumns ε s‖ := Matrix.frobenius_norm_mul k (u - signedIdentityColumns ε s)
    have m2 := norm_sub_le v (k * (u - signedIdentityColumns ε s))
    rw [e1]
    linarith
  have hK : ‖k‖ ^ 2 ≤ n + 2 * ‖k * signedIdentityColumns ε s‖ ^ 2 := by
    have h0 := hk'
    rw [hs_eq_frobVG k, hsRV_eq (k * signedIdentityColumns ε s)] at h0
    exact h0
  have hKn := norm_nonneg k
  have han := norm_nonneg (k * signedIdentityColumns ε s)
  have hKw : ‖k‖ * ‖u - signedIdentityColumns ε s‖ ≤ ‖k‖ * (1 / 4) := mul_le_mul_of_nonneg_left hw.le hKn
  have hb : ‖k * signedIdentityColumns ε s‖ ≤ 5 / 2 * Real.sqrt n + 1 / 2 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k * signedIdentityColumns ε s‖ ≤ Real.sqrt n + 1 / 4 + ‖k‖ / 4 := by linarith
    have h4 : 0 ≤ 4 * (‖k * signedIdentityColumns ε s‖ - (Real.sqrt n + 1 / 4)) := by linarith
    have h5 : 4 * (‖k * signedIdentityColumns ε s‖ - (Real.sqrt n + 1 / 4)) ≤ ‖k‖ := by linarith
    have h16 := mul_le_mul h5 h5 h4 hKn
    have hd : 0 ≤ ‖k * signedIdentityColumns ε s‖ - (5 / 2 * Real.sqrt n + 1 / 2) := by linarith
    nlinarith [sq_nonneg (‖k * signedIdentityColumns ε s‖ - (5 / 2 * Real.sqrt n + 1 / 2)), mul_nonneg hd hr0, sq_nonneg (Real.sqrt n)]
  rw [hsRV_eq (k * signedIdentityColumns ε s)] at hk'
  have hb2 : ‖k * signedIdentityColumns ε s‖ ^ 2 ≤ (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := pow_le_pow_left₀ han hb 2
  linarith

lemma entryRV {ε : Fin n → Bool} {s : Bool} {g : Matrix (Fin n) (Fin n) ℂ} {u : Matrix (Fin n) (SgIxV ε s) ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2) (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (i : Fin n) (j : SgIxV ε s) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hw := normRV_u hu
  have hg' : ‖g‖ ≤ R := by
    rw [hs_eq_frobVG] at hg
    exact le_of_pow_le_pow_left₀ two_ne_zero hR hg
  have h1 : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have h0 := hsRV_entry_le (g * u) i j
    rw [hsRV_eq] at h0
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h0
  have h2 : ‖g * u‖ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
  have h3 : ‖g‖ * ‖u‖ ≤ R * (Real.sqrt n + 1) := mul_le_mul hg' (by linarith) (norm_nonneg _) hR
  linarith

end frob

lemma O_bddRV {ε : Fin n → Bool} {s : Bool} {x : REV n (SgIxV ε s)} (hx : hsRV (Matrix.of x - signedIdentityColumns ε s) < 1 / 16) :
    x ∈ closedBall (0 : REV n (SgIxV ε s)) 2 := by
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
  have h1 := hsRV_entry_le (Matrix.of x - signedIdentityColumns ε s) i j
  have h2 : ‖(Matrix.of x - signedIdentityColumns ε s) i j‖ < 1 / 4 := by
    nlinarith [norm_nonneg ((Matrix.of x - signedIdentityColumns ε s) i j)]
  have h3 : ‖signedIdentityColumns ε s i j‖ ≤ 1 := by
    simp only [signedIdentityColumns]
    split_ifs <;> simp
  have e : x i j = (Matrix.of x - signedIdentityColumns ε s) i j + signedIdentityColumns ε s i j := by simp
  rw [e]
  linarith [norm_add_le ((Matrix.of x - signedIdentityColumns ε s) i j) (signedIdentityColumns ε s i j)]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

noncomputable section

open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem volGrowthVG (ε : Fin n → Bool) (s : Bool) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ν {g | hs (toM g) ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * (n * Fintype.card (SgIxV ε s)))) := by
  classical
  let Q := SgIxV ε s
  let lam : Measure (REV n Q) := Measure.addHaar
  let O : Set (REV n Q) := {x | hsRV (Matrix.of x - signedIdentityColumns ε s) < 1 / 16}
  let r0 : ℝ := n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2
  let W : Set (UJ ε) := {k | hs (toM k) ≤ r0}
  let N : ℕ := 2 * (n * Fintype.card Q)
  have hof : Continuous (fun x : REV n Q => (Matrix.of x : Matrix (Fin n) Q ℂ)) := continuous_id
  have hofs : Continuous (fun x : Matrix (Fin n) Q ℂ => (Matrix.of.symm x : REV n Q)) := continuous_id
  have hO_open : IsOpen O :=
    isOpen_lt (hsRV_cont.comp (hof.sub continuous_const)) continuous_const
  have hO_pos : 0 < lam O := hO_open.measure_pos lam ⟨Matrix.of.symm (signedIdentityColumns ε s), by simp [O, hsRV]⟩
  have hO_fin : lam O < ⊤ :=
    (measure_mono (fun x hx => O_bddRV hx)).trans_lt measure_closedBall_lt_top
  have hW_fin : ν W < ⊤ := ballFiniteVG ε ν r0
  have hB_fin : lam (ball 0 1) < ⊤ := measure_ball_lt_top
  set K : ENNReal := ν W * lam (ball 0 1) / lam O with hK
  have hK_fin : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hW_fin.ne hB_fin.ne) hO_pos.ne'
  refine ⟨K.toReal * (Real.sqrt n + 1) ^ N, by positivity, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  set ρ : ℝ := R * (Real.sqrt n + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set S : Set (UJ ε) := {g | hs (toM g) ≤ R ^ 2} with hS
  have hS_meas : MeasurableSet S :=
    (isClosed_le (hs_contVG.comp (continuous_toM ε)) continuous_const).measurableSet
  let Φ : UJ ε × REV n Q → REV n Q := fun p => RLV (toM p.1⁻¹) p.2
  have hΦ : Continuous Φ := by
    show Continuous fun p : UJ ε × REV n Q =>
      (Matrix.of.symm (toM p.1⁻¹ * Matrix.of p.2) : REV n Q)
    exact hofs.comp (((continuous_toM ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd))
  let T : Set (UJ ε × REV n Q) := {p | hs (toM p.1) ≤ R ^ 2} ∩ Φ ⁻¹' O
  have hT : MeasurableSet T :=
    (isClosed_le ((hs_contVG.comp (continuous_toM ε)).comp continuous_fst)
      continuous_const).measurableSet.inter (hO_open.preimage hΦ).measurableSet
  have h1 : (ν.prod lam) T = ν S * lam O := by
    rw [Measure.prod_apply hT]
    have : ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hdet : LinearMap.det (RLV (Q := Q) (toM g⁻¹)) = 1 := RLV_det (g⁻¹).2
        have e : Prod.mk g ⁻¹' T = RLV (Q := Q) (toM g⁻¹) ⁻¹' O := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]
          exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
        rw [e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
        simp
      · rw [Set.indicator_of_notMem hg]
        have e : Prod.mk g ⁻¹' T = ∅ := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [e, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator_const hS_meas, mul_comm]
  have h2 : (ν.prod lam) T ≤ ν W * lam (closedBall 0 ρ) := by
    rw [Measure.prod_apply_symm hT]
    calc ∫⁻ x, ν ((fun g => (g, x)) ⁻¹' T) ∂lam
        ≤ ∫⁻ x, (closedBall (0 : REV n Q) ρ).indicator (fun _ => ν W) x ∂lam := by
          refine lintegral_mono fun x => ?_
          by_cases hne : ((fun g => (g, x)) ⁻¹' T).Nonempty
          · obtain ⟨h, hh⟩ := hne
            have hh1 : hs (toM h) ≤ R ^ 2 := hh.1
            have hh2 : hsRV (Matrix.of (RLV (toM h⁻¹) x) - signedIdentityColumns ε s) < 1 / 16 := hh.2
            rw [of_RLV] at hh2
            have hx : x ∈ closedBall (0 : REV n Q) ρ := by
              rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]
              intro i
              rw [pi_norm_le_iff_of_nonneg hρ0]
              intro j
              have := entryRV (g := toM h) hR0 hh1 hh2 i j
              rw [← Matrix.mul_assoc, toM_mul_invVG, Matrix.one_mul] at this
              exact this
            rw [Set.indicator_of_mem hx]
            calc ν ((fun g => (g, x)) ⁻¹' T) ≤ ν ((fun g => h⁻¹ * g) ⁻¹' W) := by
                  refine measure_mono fun g hg => ?_
                  have hg2 : hsRV (Matrix.of (RLV (toM g⁻¹) x) - signedIdentityColumns ε s) < 1 / 16 := hg.2
                  rw [of_RLV] at hg2
                  show hs (toM (h⁻¹ * g)) ≤ r0
                  refine smallRV (h⁻¹ * g).2 hg2 hh2 ?_
                  rw [toM_mulVG, ← Matrix.mul_assoc, Matrix.mul_assoc (toM h⁻¹),
                    toM_mul_invVG, Matrix.mul_one]
              _ = ν W := measure_preimage_mul ν h⁻¹ W
          · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
            exact bot_le
      _ = ν W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _
  have hfr : Module.finrank ℝ (REV n Q) = N := by
    simp [REV, N, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ N) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hρ0, hfr]
  have h4 : ν S * lam O ≤ K * ENNReal.ofReal (ρ ^ N) * lam O := by
    rw [← h1]
    refine h2.trans (le_of_eq ?_)
    rw [h3, hK, div_eq_mul_inv]
    have : (lam O)⁻¹ * lam O = 1 := ENNReal.inv_mul_cancel hO_pos.ne' hO_fin.ne
    calc ν W * (ENNReal.ofReal (ρ ^ N) * lam (ball 0 1))
        = ν W * (ENNReal.ofReal (ρ ^ N) * lam (ball 0 1)) * ((lam O)⁻¹ * lam O) := by
          rw [this, mul_one]
      _ = _ := by ring
  have h5 : ν S ≤ K * ENNReal.ofReal (ρ ^ N) :=
    (ENNReal.mul_le_mul_iff_left hO_pos.ne' hO_fin.ne).1 h4
  refine h5.trans (le_of_eq ?_)
  rw [hρ, mul_pow, ← ENNReal.ofReal_toReal hK_fin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  ring

theorem integrable_of_decayVG {E : Type*} [NormedAddCommGroup E] (ε : Fin n → Bool) (s : Bool)
    (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (f : UJ ε → E) (hf : AEStronglyMeasurable f ν) (M : ℝ)
    (hM : ∀ g, hs (toM g) ≤ (n : ℝ) * Real.exp 2 + 1 → ‖f g‖ ≤ M) (a : ℝ)
    (ha : ((2 * (n * Fintype.card (SgIxV ε s)) : ℕ) : ℝ) < a)
    (hdec : ∀ g, (n : ℝ) * Real.exp 2 + 1 < hs (toM g) →
      ∃ t : ℝ, hs (toM g) ≤ n * Real.exp (2 * t) ∧ ‖f g‖ ≤ M * Real.exp (-(a * t))) :
    Integrable f ν := by
  obtain ⟨C, hC0, hC⟩ := volGrowthVG ε s ν
  set N : ℕ := 2 * (n * Fintype.card (SgIxV ε s)) with hN
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg N) ha
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hM0 : 0 ≤ M := by
    refine (norm_nonneg _).trans (hM 1 ?_)
    have e1 : hs (toM (1 : UJ ε)) = n := hs_oneVG n
    have e2 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    rw [e1]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  let A0 : ℝ := Real.exp (a * Real.log n / 2)
  let y : ℝ := Real.exp (-(a * Real.log 2))
  let r : ℝ := 2 ^ N * y
  have hy0 : 0 < y := Real.exp_pos _
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have e : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    show 2 ^ N * Real.exp (-(a * Real.log 2)) < 1
    rw [e, ← Real.exp_add, Real.exp_lt_one_iff]
    nlinarith
  let B0 : Set (UJ ε) := {g | hs (toM g) ≤ (n : ℝ) * Real.exp 2 + 1}
  let S : ℕ → Set (UJ ε) := fun j => {g | hs (toM g) ≤ ((2 : ℝ) ^ j) ^ 2}
  have hcont : Continuous (fun g : UJ ε => hs (toM g)) := hs_contVG.comp (continuous_toM ε)
  have hB0m : MeasurableSet B0 := (isClosed_le hcont continuous_const).measurableSet
  have hSm : ∀ j, MeasurableSet (S j) := fun j => (isClosed_le hcont continuous_const).measurableSet
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (M * (A0 * y ^ j))
  let F : UJ ε → ℝ≥0∞ := fun g =>
    B0.indicator (fun _ => ENNReal.ofReal M) g + ∑' j, (S (j + 1)).indicator (fun _ => c j) g
  have hpt : ∀ g, ‖f g‖ₑ ≤ F g := by
    intro g
    by_cases hg : g ∈ B0
    · calc ‖f g‖ₑ ≤ ENNReal.ofReal M := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM g hg)
        _ = B0.indicator (fun _ => ENNReal.ofReal M) g :=
            (Set.indicator_of_mem hg (fun _ => ENNReal.ofReal M)).symm
        _ ≤ F g := le_self_add
    · have hg' : (n : ℝ) * Real.exp 2 + 1 < hs (toM g) := not_le.1 hg
      obtain ⟨t, ht1, ht2⟩ := hdec g hg'
      have hpos : (1 : ℝ) ≤ hs (toM g) := by
        have : 0 ≤ (n : ℝ) * Real.exp 2 := by positivity
        linarith
      obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hpos (show (1 : ℝ) < 4 by norm_num)
      have hn0 : (0 : ℝ) < n := by
        by_contra hcon
        have : (n : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg n)
        rw [this, zero_mul] at ht1
        linarith
      have hmem : g ∈ S (j + 1) := by
        show hs (toM g) ≤ ((2 : ℝ) ^ (j + 1)) ^ 2
        have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 ^ (j + 1) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]; exact hj2.le
      have hlog : (j : ℝ) * Real.log 2 - Real.log n / 2 ≤ t := by
        have h4 : (4 : ℝ) ^ j ≤ n * Real.exp (2 * t) := hj1.trans ht1
        have h5 := Real.log_le_log (by positivity) h4
        rw [Real.log_pow, Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at h5
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [h6] at h5
        linarith
      have hexp : Real.exp (-(a * t)) ≤ A0 * y ^ j := by
        show Real.exp (-(a * t)) ≤ Real.exp (a * Real.log n / 2) * Real.exp (-(a * Real.log 2)) ^ j
        rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
        nlinarith
      have hb : ‖f g‖ ≤ M * (A0 * y ^ j) := ht2.trans (mul_le_mul_of_nonneg_left hexp hM0)
      calc ‖f g‖ₑ ≤ c j := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hb
        _ = (S (j + 1)).indicator (fun _ => c j) g := (Set.indicator_of_mem hmem (fun _ => c j)).symm
        _ ≤ ∑' j, (S (j + 1)).indicator (fun _ => c j) g :=
            ENNReal.le_tsum (f := fun j => (S (j + 1)).indicator (fun _ => c j) g) j
        _ ≤ F g := le_add_self
  have hterm : ∀ j, c j * ν (S (j + 1)) ≤ ENNReal.ofReal (M * A0 * C * 2 ^ N * r ^ j) := by
    intro j
    have h2 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    calc c j * ν (S (j + 1)) ≤ c j * ENNReal.ofReal (C * (2 ^ (j + 1)) ^ N) := by
          gcongr
          exact hC _ h2
      _ = ENNReal.ofReal (M * (A0 * y ^ j) * (C * (2 ^ (j + 1)) ^ N)) :=
          (ENNReal.ofReal_mul (mul_nonneg hM0 (by positivity))).symm
      _ = ENNReal.ofReal (M * A0 * C * 2 ^ N * r ^ j) := by
          congr 1
          show M * (A0 * y ^ j) * (C * (2 ^ (j + 1)) ^ N) = M * A0 * C * 2 ^ N * (2 ^ N * y) ^ j
          rw [mul_pow]
          ring
  have hFint : ∫⁻ g, F g ∂ν < ⊤ := by
    have e1 : ∫⁻ g, F g ∂ν = ENNReal.ofReal M * ν B0 + ∑' j, c j * ν (S (j + 1)) := by
      show ∫⁻ g, (B0.indicator (fun _ => ENNReal.ofReal M) g +
        ∑' j, (S (j + 1)).indicator (fun _ => c j) g) ∂ν = _
      rw [lintegral_add_left (measurable_const.indicator hB0m), lintegral_indicator_const hB0m,
        lintegral_tsum (fun j => (measurable_const.indicator (hSm (j + 1))).aemeasurable)]
      congr 1
      exact tsum_congr fun j => lintegral_indicator_const (hSm (j + 1)) _
    rw [e1]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ballFiniteVG ε ν _), ?_⟩
    have hsum : Summable fun j : ℕ => M * A0 * C * 2 ^ N * r ^ j :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    calc ∑' j, c j * ν (S (j + 1)) ≤ ∑' j, ENNReal.ofReal (M * A0 * C * 2 ^ N * r ^ j) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' j, M * A0 * C * 2 ^ N * r ^ j) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => by
            have := mul_nonneg hM0 (by positivity : (0 : ℝ) ≤ A0 * C * 2 ^ N * r ^ j)
            simpa only [mul_assoc] using this) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨hf, lt_of_le_of_lt (lintegral_mono hpt) hFint⟩

section ExpB

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

lemma sqrt_hs_frobVG (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [hs_eq_frobVG, Real.sqrt_sq (norm_nonneg _)]

lemma norm_exp_frobVG (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : NormedSpace.exp X = 0 := Subsingleton.elim _ _
    rw [this]; simp
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hsum := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) X
  have hr : Summable fun k : ℕ => Real.sqrt n * (‖X‖ ^ k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial ‖X‖).mul_left _
  rw [NormedSpace.exp_eq_tsum ℂ]
  calc ‖∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ ∑' k : ℕ, ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k : ℕ, Real.sqrt n * (‖X‖ ^ k / (k.factorial : ℝ)) := by
        refine hsum.tsum_le_tsum (fun k => ?_) hr
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        have hk : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, pow_zero, mul_one, ← sqrt_hs_frobVG, hs_oneVG]
          · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
              _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) h1
        calc ((k.factorial : ℝ))⁻¹ * ‖X ^ k‖ ≤ ((k.factorial : ℝ))⁻¹ * (Real.sqrt n * ‖X‖ ^ k) := by gcongr
          _ = _ := by ring
    _ = Real.sqrt n * Real.exp ‖X‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

end ExpB

theorem hs_exp_leVG (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (NormedSpace.exp X) ≤ n * Real.exp (2 * Real.sqrt (hs X)) := by
  have h := norm_exp_frobVG X
  rw [← sqrt_hs_frobVG, ← sqrt_hs_frobVG] at h
  have h0 : 0 ≤ hs (NormedSpace.exp X) := hs_nonnegVG _
  calc hs (NormedSpace.exp X) = Real.sqrt (hs (NormedSpace.exp X)) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ (Real.sqrt n * Real.exp (Real.sqrt (hs X))) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← Real.exp_nat_mul]
        norm_num

lemma hs_eq_traceVG (A : Matrix (Fin n) (Fin n) ℂ) : ((Aᴴ * A).trace).re = hs A := by
  have key : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, hs,
    key]
  exact Finset.sum_comm

theorem hs_kmulVG {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) : hs (toMK k * A) = hs A := by
  have hk : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp (k.2 : toMK k ∈ Kset ε).1
  rw [← hs_eq_traceVG, ← hs_eq_traceVG, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (toMK k)ᴴ, hk, Matrix.one_mul]

end ReciprocityTheory.ChartRestriction.DS.S7
