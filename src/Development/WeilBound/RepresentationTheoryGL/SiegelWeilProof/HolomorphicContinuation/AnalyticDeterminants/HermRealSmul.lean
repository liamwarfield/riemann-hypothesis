module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.HermRealSmul
noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem inG_mul {a b : M2 n} (ha : InG a) (hb : InG b) : InG (a * b) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [ha, hb]

theorem inG_upper {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (fromBlocks 1 b 0 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hb]

theorem inG_lower {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hc]

theorem inG_scalar {c : ℂ} (hc : star c * c = 1) : InG (c • (1 : M2 n)) := by
  show (c • (1 : M2 n))ᴴ * JJ n * (c • (1 : M2 n)) = JJ n
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hc, one_smul]

theorem upper_line (y : M2 n) (b : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 b 0 0) = y * fromBlocks 1 (t • b) 0 1 := by
  have e : (fromBlocks 1 (t • b) 0 1 : M2 n) = 1 + t • fromBlocks 0 b 0 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem lower_line (y : M2 n) (c : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 0 c 0) = y * fromBlocks 1 0 (t • c) 1 := by
  have e : (fromBlocks 1 0 (t • c) 1 : M2 n) = 1 + t • fromBlocks 0 0 c 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem herm_real_smul {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) (t : ℝ) : ((t : ℂ) • b)ᴴ = (t : ℂ) • b := by
  rw [conjTranspose_smul, hb]
  simp

private theorem fderiv_apply_eq_zero_of_const_on_real_line {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : E → W} {y v : E}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const v).const_add y
    convert h0 using 1
    · rfl
    · rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
  have h1 : HasFDerivAt f ((fderiv ℂ f y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hc := h1.comp_hasDerivAt (0 : ℝ) hl
  have hk : (f ∘ fun t : ℝ => y + (t : ℂ) • v) = fun _ => f y := funext h
  rw [hk] at hc
  exact ((hasDerivAt_const (0 : ℝ) (f y)).unique hc).symm

theorem fderiv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {f : M2 n → W} {y v : M2 n}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  exact fderiv_apply_eq_zero_of_const_on_real_line hf h

end PositivityTheory.Rg.Sw.LVs.HolB
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Cmi (n : ℕ) : M2 n :=
  fromBlocks ((-Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1) ((Complex.I / 2) • 1) ((1 / 2 : ℂ) • 1)

theorem cm_mul_cmi : Cm n * Cmi n = 1 := by
  rw [Cm, Cmi, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> by_cases h : i = j <;>
    simp [Matrix.one_apply, h, Matrix.add_apply, Matrix.smul_apply] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring_nf

theorem cm_inv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_right_inv cm_mul_cmi

theorem toBlocks₂₁_mul (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem toBlocks₂₂_mul (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem mul_cm₂₁ (x : M2 n) : (x * Cm n).toBlocks₂₁ = u1 x := by
  rw [toBlocks₂₁_mul, u1, Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_one]

theorem mul_cm₂₂ (x : M2 n) : (x * Cm n).toBlocks₂₂ = u2 x := by
  rw [toBlocks₂₂_mul, u2, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one]

theorem first_cayley_block_mul_inverse_cayley (y : M2 n) : u1 (y * Cmi n) = y.toBlocks₂₁ := by
  rw [u1, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem second_cayley_block_mul_inverse_cayley (y : M2 n) : u2 (y * Cmi n) = y.toBlocks₂₂ := by
  rw [u2, toBlocks₂₁_mul, toBlocks₂₂_mul, Cmi]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring_nf

theorem uAct : UAct := by
  intro n x P Q R S
  simp only [mX, cm_inv, ← Matrix.mul_assoc]
  rw [first_cayley_block_mul_inverse_cayley, second_cayley_block_mul_inverse_cayley, toBlocks₂₁_mul (x * Cm n) (fromBlocks P Q R S),
    toBlocks₂₂_mul (x * Cm n) (fromBlocks P Q R S), mul_cm₂₁, mul_cm₂₂]
  simp

def incl (s : Finset (Fin n)) : Matrix (Fin n) s ℂ := Matrix.of fun c i => if c = (i : Fin n) then 1 else 0

def subOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix s s ℂ :=
  M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))

theorem minorOn_eq (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : minorOn s M = (subOn s M).det := rfl

theorem sum_incl (s : Finset (Fin n)) (a : Fin n) (f : s → ℂ) :
    ∑ i : s, (if a = (i : Fin n) then (1 : ℂ) else 0) * f i = if h : a ∈ s then f ⟨a, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro i _ hi
      have : a ≠ (i : Fin n) := fun e => hi (Subtype.ext e.symm)
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : a ≠ (i : Fin n) := fun e => h (e ▸ i.2)
    simp [this]

theorem embOn_eq (s : Finset (Fin n)) (T : Matrix s s ℂ) : embOn s T = incl s * T * (incl s)ᵀ := by
  ext a b
  simp only [Matrix.mul_apply, incl, Matrix.of_apply, Matrix.transpose_apply]
  simp only [sum_incl]
  simp only [mul_comm _ (ite (b = _) _ _)]
  rw [sum_incl]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;> simp [embOn, ha, hb]

theorem incl_mul (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) : (incl s)ᵀ * M * incl s = subOn s M := by
  ext i j
  simp [Matrix.mul_apply, incl, subOn, Matrix.transpose_apply]

theorem det_one_add_mul_embOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det = (1 + subOn s M * T).det := by
  rw [embOn_eq]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.det_one_add_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [incl_mul]

theorem detD_const_mul {ι : Type} [Fintype ι] [DecidableEq ι] (c : ℂ) (F : Matrix ι ι ℂ → ℂ) :
    detD (fun S => c * F S) = c * detD F := by
  by_cases hc : c = 0
  · subst hc
    simp [detD]
  · let g : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc)
    have hfun : (fun S => c * F S) = g ∘ F := by
      funext S
      simp [g, mul_comm]
    unfold detD
    rw [hfun, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
    (simp [g]) <;> ring

theorem card_blkA {j : ℕ} (hj : j ≤ n) : Fintype.card (blkA (n := n) j) = j := by
  rw [Fintype.card_coe, blkA, Fin.card_filter_val_lt, min_eq_right hj]

theorem card_blkB {j : ℕ} (hj : j ≤ n) : Fintype.card (blkB (n := n) j) = n - j := by
  rw [Fintype.card_coe, blkB, Finset.card_compl, Fintype.card_fin, ← Fintype.card_coe, card_blkA hj]

theorem scalar_section_mul_block_unipotent {p q : ℤ} {j : ℕ} {x : M2 n} (h1 : (u1 x).det ≠ 0) (h2 : (u2 x).det ≠ 0)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (f0 p q x * (1 + subOn (blkA j) (wM x) * T).det ^ (-q)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ (-p) := by
  have hd1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hd2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have k1 : u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u1 x * (1 + (wM x)⁻¹ * embOn (blkB j) S) := by
    rw [(uAct n x _ _ _ _).1, wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd2]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd1, Matrix.one_mul,
      Matrix.mul_one]
  have k2 : u2 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      u2 x * (1 + wM x * embOn (blkA j) T) := by
    rw [(uAct n x _ _ _ _).2, wM]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd2, Matrix.one_mul,
      Matrix.mul_one]
    abel
  rw [f0, f0, k1, k2, Matrix.det_mul, Matrix.det_mul, det_one_add_mul_embOn, det_one_add_mul_embOn,
    mul_zpow, mul_zpow]
  ring

theorem djSec_of (hC : Cayley) : DjSec := by
  intro n j p q x hj h1 h2
  have hin : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        f0 p q (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
      (f0 p q x * (∏ i ∈ Finset.range (n - j), (-(p : ℂ) + i)) * minorOn (blkB j) (wM x)⁻¹) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-q) := by
    intro T
    simp_rw [scalar_section_mul_block_unipotent h1 h2 T]
    rw [detD_const_mul, hC, card_blkB hj, minorOn_eq]
    push_cast
    ring
  simp_rw [hin]
  rw [detD_const_mul, hC, card_blkA hj]
  simp only [minorOn_eq]
  push_cast
  ring

end PositivityTheory.Rg.Sw.LVs
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyA
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Equivar : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℂ → ℂ) (A : Matrix ι ι ℂ), AnalyticAt ℂ F 0 →
    detD (fun T => F (A * T)) = A.det * detD F

def Reindex : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (F : Matrix κ κ ℂ → ℂ),
    AnalyticAt ℂ F 0 → detD (fun T : Matrix ι ι ℂ => F (T.reindex e e)) = detD F

def KappaFin : Prop :=
  ∀ (N : ℕ) (t : ℤ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) =
    ∏ i ∈ Finset.range N, ((t : ℂ) + i)

end PositivityTheory.Rg.Sw.LVs
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IterAffine : Prop :=
  ∀ (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω → ∀ c ∈ Ω, ∀ (L : W →L[ℂ] V) (k : ℕ),
      iteratedFDeriv ℂ k (fun w => F (c + L w)) 0 = (iteratedFDeriv ℂ k F c).compContinuousLinearMap (fun _ => L)

def IterSymm : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω →
    ∀ c ∈ Ω, ∀ (k : ℕ) (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v

def IterNested : Prop :=
  ∀ (V W1 W2 : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W1] [NormedSpace ℂ W1]
    [NormedAddCommGroup W2] [NormedSpace ℂ W2] (F : V → ℂ) (Ω : Set V), IsOpen Ω → ContDiffOn ℂ ∞ F Ω → ∀ c ∈ Ω,
    ∀ (L1 : W1 →L[ℂ] V) (L2 : W2 →L[ℂ] V) (a b : ℕ) (u : Fin a → W1) (w : Fin b → W2),
      iteratedFDeriv ℂ a (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) 0 u =
        iteratedFDeriv ℂ (a + b) F c (Fin.append (fun i => L1 (u i)) (fun i => L2 (w i)))

variable {n : ℕ}

def bdiag (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ blkA j ∧ b ∈ blkA j then c * t a b else if a ∈ blkB j ∧ b ∈ blkB j then c' * t a b else 0

def DetDBlock : Prop :=
  ∀ (n j : ℕ) (c c' : ℂ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ) (Ω : Set (Matrix (Fin n) (Fin n) ℂ)), IsOpen Ω → 0 ∈ Ω →
    ContDiffOn ℂ ∞ ψ Ω →
    detD (fun t => ψ (bdiag j c c' t)) =
      c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card *
        detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          ψ (embOn (blkA j) T + embOn (blkB j) S)))

def CmI (n : ℕ) : M2 n := ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks 1 (Complex.I • 1) (-1) (Complex.I • 1)

def rot (j : ℕ) (θ : ℝ) : M2 n :=
  Cm n * fromBlocks (diagonal fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)) 0 0
    (diagonal fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)) * CmI n

def zTop (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then fromBlocks 0 (single r s 1) 0 0
     else if r ∈ blkB j ∧ s ∈ blkB j then -fromBlocks 0 0 (single r s 1) 0
     else if r ∈ blkA j then fromBlocks (single r s 1) 0 0 0 else -fromBlocks 0 0 0 (single r s 1))

def zMid (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then fromBlocks (single r s 1) 0 0 (-single r s 1)
     else if r ∈ blkB j ∧ s ∈ blkB j then fromBlocks (single r s 1) 0 0 (-single r s 1)
     else if r ∈ blkA j then fromBlocks 0 (single r s 1) (-single r s 1) 0 else fromBlocks 0 (single r s 1) (-single r s 1) 0)

def zLow (j : ℕ) (r s : Fin n) : M2 n :=
  ((2 * Complex.I)⁻¹ : ℂ) •
    (if r ∈ blkA j ∧ s ∈ blkA j then -fromBlocks 0 0 (single r s 1) 0
     else if r ∈ blkB j ∧ s ∈ blkB j then fromBlocks 0 (single r s 1) 0 0
     else if r ∈ blkA j then -fromBlocks 0 0 0 (single r s 1) else fromBlocks (single r s 1) 0 0 0)

end PositivityTheory.Rg.Sw.LVs.TC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInvA
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def reK (e : M2 n) : M2 n := (1 / 2 : ℂ) • (e - eᴴ)

def imK (e : M2 n) : M2 n := (-Complex.I / 2) • (e + eᴴ)

def dK (F : M2 n → ℂ) (x e : M2 n) : ℂ := fderiv ℝ F x (reK e * x) + Complex.I * fderiv ℝ F x (imK e * x)

def KSet (n : ℕ) : Set (M2 n) := {g | InK g}

def LeftDeriv : Prop :=
  ∀ (n : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
    ∀ (F : M2 n → ℂ) (U : Set (M2 n)), IsOpen U → KSet n ⊆ U → ContDiffOn ℝ 1 F U →
    ∀ e : M2 n, e * JJ n = JJ n * e →
      Integrable (fun k => dK F (ι k) e) μ ∧ ∫ k, dK F (ι k) e ∂μ = 0

def LawDeriv : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → {g | InG g} ⊆ Ω → DifferentiableOn ℂ Θ Ω →
    (∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x) →
    ∀ x, InG x → ∀ Y : M2 n, Y.toBlocks₂₁ = 0 →
      fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x

def eA (a b : Fin n) : M2 n := fromBlocks (Matrix.single a b 1) 0 0 (Matrix.single a b 1)

def eB (a b : Fin n) : M2 n := fromBlocks 0 (Matrix.single a b 1) (-Matrix.single a b 1) 0

def cA (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := (x * Z * xᴴ).toBlocks₂₂ a b

def cB (Z : M2 n) (a b : Fin n) (x : M2 n) : ℂ := -(x * Z * xᴴ).toBlocks₂₁ a b

def PtId : Prop :=
  ∀ (n : ℕ) (Θ : M2 n → ℂ) (x Z : M2 n), InK x → ContDiffAt ℂ 1 Θ x →
    (∀ Y : M2 n, Y.toBlocks₂₁ = 0 → fderiv ℂ Θ x (Y * x) = (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace) * Θ x) →
    fderiv ℂ Θ x (x * Z) =
      ∑ a, ∑ b, (dK (fun y => cA Z a b y * Θ y) x (eA a b) + dK (fun y => cB Z a b y * Θ y) x (eB a b))

def CDiff : Prop := ∀ (n : ℕ) (Z : M2 n) (a b : Fin n), ContDiff ℝ ∞ (cA Z a b) ∧ ContDiff ℝ ∞ (cB Z a b)

end PositivityTheory.Rg.Sw.LVs.II
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulConjTransposeEq
noncomputable section

set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem isUnit_det_of_inG' {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose] at h
  have hJ : (JJ n).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [det_mul, h0, zero_mul, det_neg, det_one] at this
    simp at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at h
  exact h.symm

theorem mul_JJ_conjTranspose {g : M2 n} (hg : InG g) : g * JJ n * gᴴ = JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n := by rw [h2, Matrix.one_mul]
  have h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ := by
    simp only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]
  rw [← h4, h3]

theorem lower_rel {g : M2 n} (hg : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_conjTranspose hg)
  rw [← fromBlocks_toBlocks g] at h
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
  simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_one, add_zero] at h
  have : -(g.toBlocks₂₂ * g.toBlocks₂₁ᴴ) + g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = 0 := by
    rw [← h]; simp
  rw [neg_add_eq_zero] at this
  exact this.symm

theorem first_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u1, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem second_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u2 g * (u2 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

theorem inv_eq_of_inG {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  exact Matrix.inv_eq_left_inv h1

theorem inverse_first_block_eq_of_group {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by
  rw [ub1, inv_eq_of_inG hg, u1]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  module

theorem posDef_lower {g : M2 n} (hg : InG g) :
    (g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ).PosDef := by
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]
    exact (isUnit_det_of_inG' hg).star
  have hP : (gᴴᴴ * gᴴ).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [conjTranspose_conjTranspose] at hP
  have h2 := hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective
  convert h2 using 1
  conv_rhs => rw [← fromBlocks_toBlocks g]
  ext i j
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]

theorem det_first_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u1 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (first_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem det_second_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u2 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

theorem automorphy_first_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul]

theorem automorphy_second_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u2 (P * x) = P.toBlocks₂₂ * u2 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem det_par {P : M2 n} (hP : P.toBlocks₂₁ = 0) : P.det = P.toBlocks₁₁.det * P.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks P, hP]
  exact det_fromBlocks_zero₂₁ _ _ _

theorem par_rel {P : M2 n} (hG : InG P) (hP : P.toBlocks₂₁ = 0) : P.toBlocks₁₁ᴴ * P.toBlocks₂₂ = 1 := by
  have h := congrArg Matrix.toBlocks₁₂ hG
  rw [← fromBlocks_toBlocks P, hP] at h
  simpa [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] using h

theorem inverse_first_block_mul_parabolic {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by
  have hA : IsUnit P.toBlocks₁₁.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_left hPu
  have hD : IsUnit P.toBlocks₂₂.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_right hPu
  have hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0
      (P.toBlocks₂₂)⁻¹ := by
    conv_lhs => rw [← fromBlocks_toBlocks P, hP]
    refine Matrix.inv_eq_right_inv ?_
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg,
      Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
    rw [← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
  rw [ub1, ub1, Matrix.mul_inv_rev, hinv]
  conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.smul_mul]

theorem lower_mul_conjTranspose (g : M2 n) :
    (g * gᴴ).toBlocks₂₂ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem first_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u1 k * (u1 k)ᴴ = 1 := by
  rw [first_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

theorem second_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u2 k * (u2 k)ᴴ = 1 := by
  rw [second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

end PositivityTheory.Rg.Sw.LVs
end
end
