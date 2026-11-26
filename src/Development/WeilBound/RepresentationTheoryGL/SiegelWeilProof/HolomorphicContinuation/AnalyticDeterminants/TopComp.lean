module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlock

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompC
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.StarExpNegI
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatC
noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem diag_single_diag (u v : Fin n → ℂ) (r s : Fin n) (c : ℂ) :
    diagonal u * single r s c * diagonal v = single r s (u r * c * v s) := by
  ext i k
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · simp

theorem inG_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, star (d1 a) * d1 a = 1) (h2 : ∀ a, star (d2 a) * d2 a = 1) :
    InG (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n) := by
  unfold InG
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  have hK : Dᴴ * fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) * D =
      fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) := by
    rw [hD, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [diagonal_conjTranspose]
    exact ⟨funext fun a => h1 a, funext fun a => h2 a⟩
  calc (Cm n * D * CmI n)ᴴ * JJ n * (Cm n * D * CmI n)
      = (CmI n)ᴴ * (Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D) * CmI n := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (CmI n)ᴴ * ((Cm n)ᴴ * JJ n * Cm n) * CmI n := by rw [cmH_JJ_cm, hK]
    _ = (Cm n * CmI n)ᴴ * JJ n * (Cm n * CmI n) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [cm_mul_cmI, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem prod_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n *
      (Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n) = 1 := by
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', fromBlocks_multiply, ← fromBlocks_one]
    simp [diagonal_mul_diagonal, h1, h2]
    done
  calc Cm n * D * CmI n * (Cm n * D' * CmI n) = Cm n * D * (CmI n * Cm n) * D' * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = Cm n * (D * D') * CmI n := by
        rw [cmI_mul_cm, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, Matrix.mul_one, cm_mul_cmI]

theorem inv_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ =
      Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n := by
  exact Matrix.inv_eq_right_inv (prod_conjDiag d1 d2 h1 h2)

theorem cmI_N_cm (E : Matrix (Fin n) (Fin n) ℂ) :
    CmI n * fromBlocks 0 E 0 0 * Cm n = ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks E E (-E) (-E) := by
  rw [CmI, Cm, Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
  congr 1
  simp
  done

theorem conj_nU (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) (r s : Fin n) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n * nU (single r s 1) *
        (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ - 1 =
      Cm n * (((2 * Complex.I)⁻¹ : ℂ) • fromBlocks (single r s (d1 r * (d1 s)⁻¹)) (single r s (d1 r * (d2 s)⁻¹))
        (-single r s (d2 r * (d1 s)⁻¹)) (-single r s (d2 r * (d2 s)⁻¹))) * CmI n := by
  rw [inv_conjDiag d1 d2 h1 h2]
  have hn : nU (single r s (1 : ℂ)) = 1 + fromBlocks 0 (single r s 1) 0 0 := by
    rw [nU, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [hn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, prod_conjDiag d1 d2 h1 h2, add_sub_cancel_left]
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  calc Cm n * D * CmI n * fromBlocks 0 (single r s 1) 0 0 * (Cm n * D' * CmI n)
      = Cm n * (D * (CmI n * fromBlocks 0 (single r s 1) 0 0 * Cm n) * D') * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [cmI_N_cm]
        congr 2
        rw [Matrix.mul_smul, Matrix.smul_mul, hD, hD', fromBlocks_multiply, fromBlocks_multiply]
        simp [diag_single_diag]
        done

end PositivityTheory.Rg.Sw.LVs.TC
end
end

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem exp_neg_I (t : ℂ) : Complex.exp (-t * Complex.I) = (Complex.exp (t * Complex.I))⁻¹ := by
  rw [neg_mul, Complex.exp_neg]

theorem star_exp_I (θ : ℝ) : star (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem star_exp_negI (θ : ℝ) : star (Complex.exp (-θ * Complex.I)) * Complex.exp (-θ * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

def dA (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (θ * Complex.I) else Complex.exp (-θ * Complex.I)

def dB (j : ℕ) (θ : ℝ) : Fin n → ℂ := fun a => if a ∈ blkA j then Complex.exp (-θ * Complex.I) else Complex.exp (θ * Complex.I)

theorem rot_eq (j : ℕ) (θ : ℝ) : rot (n := n) j θ = Cm n * fromBlocks (diagonal (dA j θ)) 0 0 (diagonal (dB j θ)) * CmI n := rfl

theorem dA_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dA j θ a ≠ 0 := by unfold dA; split_ifs <;> exact Complex.exp_ne_zero _

theorem dB_ne (j : ℕ) (θ : ℝ) (a : Fin n) : dB j θ a ≠ 0 := by unfold dB; split_ifs <;> exact Complex.exp_ne_zero _

theorem rot_inG (j : ℕ) (θ : ℝ) : InG (rot (n := n) j θ) := by
  rw [rot_eq]
  refine inG_conjDiag _ _ (fun a => ?_) (fun a => ?_)
  · unfold dA; split_ifs
    · exact star_exp_I θ
    · exact star_exp_negI θ
  · unfold dB; split_ifs
    · exact star_exp_negI θ
    · exact star_exp_I θ

theorem smul_conjCm (c : ℂ) (X : M2 n) : c • (Cm n * X * CmI n) = Cm n * (c • X) * CmI n := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem rot_conj (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • (rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1) =
      Cm n * (zLow j r s + Complex.exp (2 * θ * Complex.I) • zMid j r s +
        Complex.exp (2 * θ * Complex.I) ^ 2 • zTop j r s) * CmI n := by
  rw [rot_eq, conj_nU _ _ (dA_ne j θ) (dB_ne j θ), smul_conjCm]
  congr 2
  have he : Complex.exp (2 * θ * Complex.I) = Complex.exp (θ * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu0 : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [he]
  simp only [dA, dB, zLow, zMid, zTop, blkB, Finset.mem_compl, exp_neg_I]
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, fromBlocks_smul, fromBlocks_add, fromBlocks_neg, smul_single, fromBlocks_inj]
  all_goals constructor <;> congr 1 <;> field_simp <;> ring

end PositivityTheory.Rg.Sw.LVs.TC
end
end

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def matrixBlockRestriction (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a ∈ s ∧ b ∈ t then x a b else 0

def matrixBlockRestrictionLinear (s t : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixBlockRestriction s t
      map_add' := fun x y => by ext a b; simp only [matrixBlockRestriction, Matrix.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by
        ext a b; simp only [matrixBlockRestriction, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp }

@[simp] theorem block_part_linear_apply (s t : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ) : matrixBlockRestrictionLinear s t x = matrixBlockRestriction s t x := rfl

def conjL (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n)
      map_add' := fun x y => by
        simp only [map_add (f := _), ← fromBlocks_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        simp only [map_smul, RingHom.id_apply, ← fromBlocks_smul, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem conjL_apply (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (x : Matrix (Fin n) (Fin n) ℂ) : conjL g P Q R S x = g * (Cm n * fromBlocks (P x) (Q x) (R x) (S x) * CmI n) := rfl

def rotL (g : M2 n) (j : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun H => g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹)
      map_add' := fun x y => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (x + y) 0 0 = fromBlocks 0 x 0 0 + fromBlocks 0 y 0 0 by
          rw [fromBlocks_add]; simp]
        simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        rw [show fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) (c • x) 0 0 = c • fromBlocks 0 x 0 0 by
          rw [fromBlocks_smul]; simp]
        simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }

@[simp] theorem rotL_apply (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    rotL g j θ H = g * (rot j θ * fromBlocks 0 H 0 0 * (rot j θ)⁻¹) := rfl

theorem nU_eq (H : Matrix (Fin n) (Fin n) ℂ) : nU H = 1 + fromBlocks 0 H 0 0 := by
  rw [nU, ← fromBlocks_one, fromBlocks_add]; simp

theorem rot_mul_inv (j : ℕ) (θ : ℝ) : rot (n := n) j θ * (rot j θ)⁻¹ = 1 := inG_mul_inv (rot_inG j θ)

theorem rot_nU (g : M2 n) (j : ℕ) (θ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) :
    g * rot j θ * nU H * (rot j θ)⁻¹ = g + rotL g j θ H := by
  simp only [nU_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc, rot_mul_inv, rotL_apply]

theorem rotL_single (g : M2 n) (j : ℕ) (θ : ℝ) (r s : Fin n) :
    Complex.exp (2 * θ * Complex.I) • rotL g j θ (single r s 1) =
      g * (Cm n * zLow j r s * CmI n) + Complex.exp (2 * θ * Complex.I) • (g * (Cm n * zMid j r s * CmI n)) +
        Complex.exp (2 * θ * Complex.I) ^ 2 • (g * (Cm n * zTop j r s * CmI n)) := by
  have hX : rot (n := n) j θ * fromBlocks 0 (single r s 1) 0 0 * (rot j θ)⁻¹ =
      rot j θ * nU (single r s 1) * (rot j θ)⁻¹ - 1 := by
    have h := rot_nU (1 : M2 n) j θ (single r s 1)
    simp only [Matrix.one_mul, rotL_apply] at h
    rw [h]
    abel
  rw [rotL_apply, hX, ← Matrix.mul_smul, rot_conj]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem block_part_single (s t : Finset (Fin n)) (r u : Fin n) :
    matrixBlockRestriction s t (single r u (1 : ℂ)) = if r ∈ s ∧ u ∈ t then single r u 1 else 0 := by
  ext a b
  by_cases h : r ∈ s ∧ u ∈ t
  · rw [if_pos h]
    simp only [matrixBlockRestriction, Matrix.single_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]
  · rw [if_neg h]
    simp only [matrixBlockRestriction, Matrix.single_apply, Matrix.zero_apply]
    by_cases hab : r = a ∧ u = b
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h]
    · simp [hab]

theorem memB {j : ℕ} {a : Fin n} : a ∈ blkB j ↔ a ∉ blkA j := by simp [blkB]

def topL (g : M2 n) (j : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n :=
  conjL g (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkB j)) (((2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkA j) (blkA j))
    ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkB j)) ((-(2 * Complex.I)⁻¹ : ℂ) • matrixBlockRestrictionLinear (blkB j) (blkA j))

theorem topL_single (g : M2 n) (j : ℕ) (r s : Fin n) : topL g j (single r s 1) = g * (Cm n * zTop j r s * CmI n) := by
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, block_part_linear_apply, block_part_single, zTop]
  congr 2
  by_cases hr : r ∈ blkA j <;> by_cases hs : s ∈ blkA j <;>
    simp [hr, hs, memB, fromBlocks_smul, fromBlocks_neg]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCCalc
noncomputable section

open scoped ContDiff
open Set Filter Topology

namespace PositivityTheory.Rg.Sw.LVs.TC

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma iter_smooth {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) :
    ContDiffOn ℂ ∞ (iteratedFDeriv ℂ i F) Ω := by
  intro y hy
  have hle : (∞ : WithTop ℕ∞) + i ≤ ∞ := by
    exact_mod_cast (le_top : (⊤ : ℕ∞) + i ≤ ⊤)
  exact ((hF.contDiffAt (hΩ.mem_nhds hy)).iteratedFDeriv_right hle).contDiffWithinAt

lemma iter_diffAt {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) {y : V} (hy : y ∈ Ω) :
    DifferentiableAt ℂ (iteratedFDeriv ℂ i F) y := by
  exact ((iter_smooth hΩ hF i).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)

private lemma iter_cast' {F : V → ℂ} {c : V} {m m' : ℕ} (h : m = m') (v : Fin m → V) :
    iteratedFDeriv ℂ m F c v = iteratedFDeriv ℂ m' F c (v ∘ Fin.cast h.symm) := by
  subst h; rfl

end

theorem iterAffine : IterAffine := by
  intro V W _ _ _ _ F Ω hΩ hF c hc L k
  have hT : Continuous (fun y : V => c + y) := continuous_const.add continuous_id
  have hΩ1 : IsOpen ((fun y : V => c + y) ⁻¹' Ω) := hΩ.preimage hT
  have hΩ2 : IsOpen (L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω)) := hΩ1.preimage L.continuous
  have hG : ContDiffOn ℂ ∞ (fun y : V => F (c + y)) ((fun y : V => c + y) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
  have hm2 : (0 : W) ∈ L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω) := by simpa using hc
  have hm1 : L 0 ∈ (fun y : V => c + y) ⁻¹' Ω := by simpa using hc
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hG hΩ1.uniqueDiffOn
    hΩ2.uniqueDiffOn hm1 hk
  rw [iteratedFDerivWithin_of_isOpen k hΩ2 hm2, iteratedFDerivWithin_of_isOpen k hΩ1 hm1,
    iteratedFDeriv_comp_add_left] at h1
  simp only [map_zero, add_zero] at h1
  exact h1

def predPerm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) : Equiv.Perm (Fin k) where
  toFun i := (σ i.succ).pred (fun h => Fin.succ_ne_zero i (σ.injective (h.trans h0.symm)))
  invFun i := (σ⁻¹ i.succ).pred (fun h => by
    have : σ⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, h0]
    exact Fin.succ_ne_zero i ((σ⁻¹).injective (h.trans this.symm)))
  left_inv i := by simp
  right_inv i := by simp

lemma predPerm_succ {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (i : Fin k) :
    (predPerm σ h0 i).succ = σ i.succ := by
  simp [predPerm]

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma symm_fix {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    (ih : ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v)
    {c : V} (hc : c ∈ Ω) (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (v : Fin (k + 1) → V) :
    iteratedFDeriv ℂ (k + 1) F c (v ∘ σ) = iteratedFDeriv ℂ (k + 1) F c v := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k F) c := iter_diffAt hΩ hF k hc
  have ht : Fin.tail (v ∘ σ) = Fin.tail v ∘ predPerm σ h0 := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [predPerm_succ]
  have h0' : (v ∘ σ) 0 = v 0 := by simp [h0]
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, ht, h0',
    ← fderiv_continuousMultilinear_apply_const_apply hd,
    ← fderiv_continuousMultilinear_apply_const_apply hd]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hΩ.mem_nhds hc] with y hy
  exact ih y hy (Fin.tail v) (predPerm σ h0)

private theorem iteratedFDeriv_add_two_apply {F : V → ℂ} (k : ℕ) (c : V) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c v =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k F)) c (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
  simp [LinearIsometryEquiv.comp_fderiv, Fin.tail]

lemma symm_swap {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    {c : V} (hc : c ∈ Ω) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℂ (k + 2) F c v := by
  have hG : ContDiffAt ℂ ∞ (iteratedFDeriv ℂ k F) c :=
    (iter_smooth hΩ hF k).contDiffAt (hΩ.mem_nhds hc)
  have hmin : minSmoothness ℂ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hs := hG.isSymmSndFDerivAt hmin
  have htt : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [Fin.ext_iff]
  rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, htt]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hs (v 1) (v 0)]

end

theorem iterSymm : IterSymm := by
  intro V _ _ F Ω hΩ hF
  suffices h : ∀ k : ℕ, ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v from
    fun c hc k v σ => h k c hc v σ
  intro k
  induction k with
  | zero =>
    intro c hc v σ
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    intro c hc v σ
    have key : ∀ (j : Fin (k + 1)) (u : Fin (k + 1) → V),
        iteratedFDeriv ℂ (k + 1) F c (u ∘ Equiv.swap 0 j) = iteratedFDeriv ℂ (k + 1) F c u := by
      intro j u
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · cases k with
        | zero => exact absurd (Fin.fin_one_eq_zero j) hj0
        | succ m =>
          by_cases hj1 : j = 1
          · subst hj1
            exact symm_swap hΩ hF hc u
          · have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
            have hs : Equiv.swap (0 : Fin (m + 2)) j =
                Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j := by
              rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
            have hfix : ∀ w : Fin (m + 2) → V,
                iteratedFDeriv ℂ (m + 2) F c (w ∘ Equiv.swap 1 j) = iteratedFDeriv ℂ (m + 2) F c w :=
              fun w => symm_fix hΩ hF ih hc (Equiv.swap 1 j)
                (Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)) w
            have hcomp : u ∘ ⇑((Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j :
                Equiv.Perm (Fin (m + 2)))) =
                ((u ∘ Equiv.swap 1 j) ∘ Equiv.swap 0 1) ∘ Equiv.swap 1 j := by
              funext i
              simp [Equiv.Perm.mul_apply]
            rw [hs, hcomp, hfix, symm_swap hΩ hF hc, hfix]
    have h0 : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.Perm.mul_apply]
    have hv : v ∘ σ = (v ∘ Equiv.swap 0 (σ 0)) ∘ ⇑(Equiv.swap 0 (σ 0) * σ) := by
      funext i
      simp [Equiv.Perm.mul_apply]
    rw [hv, symm_fix hΩ hF ih hc _ h0, key]

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma eval_smooth {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω :=
  (ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => V) ℂ w).contDiff.comp_contDiffOn (iter_smooth hΩ hF b)

lemma iter_mixed {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ∀ (a : ℕ) {c : V}, c ∈ Ω → ∀ (u : Fin a → V),
      iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) c u = iteratedFDeriv ℂ (a + b) F c (Fin.append u w) := by
  intro a
  induction a with
  | zero =>
    intro c hc u
    rw [iteratedFDeriv_zero_apply, iter_cast' (zero_add b) (Fin.append u w),
      Fin.append_left_nil u w rfl]
    congr 1
  | succ a ih =>
    intro c hc u
    have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω := eval_smooth hΩ hF b w
    have hd1 := iter_diffAt hΩ hg a hc
    have hd2 := iter_diffAt hΩ hF (a + b) hc
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd1]
    have he : (fun y => iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) y (Fin.tail u))
        =ᶠ[𝓝 c] (fun y => iteratedFDeriv ℂ (a + b) F y (Fin.append (Fin.tail u) w)) := by
      filter_upwards [hΩ.mem_nhds hc] with y hy
      exact ih hy (Fin.tail u)
    rw [he.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply hd2]
    have hs := iteratedFDeriv_succ_apply_left (𝕜 := ℂ) (f := F) (x := c) (n := a + b)
      (Fin.cons (u 0) (Fin.append (Fin.tail u) w))
    rw [Fin.cons_zero, Fin.tail_cons] at hs
    rw [← hs, iter_cast' (show a + 1 + b = a + b + 1 by omega) (Fin.append u w)]
    congr 1
    conv_rhs => rw [← Fin.cons_self_tail u, Fin.append_cons]
    funext i
    simp

end

theorem iterNested : IterNested := by
  intro V W1 W2 _ _ _ _ _ _ F Ω hΩ hF c hc L1 L2 a b u w
  have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x (fun i => L2 (w i))) Ω :=
    eval_smooth hΩ hF b _
  have hU : ∀ᶠ t1 in 𝓝 (0 : W1), c + L1 t1 ∈ Ω := by
    have hcont : Continuous (fun t1 : W1 => c + L1 t1) := continuous_const.add L1.continuous
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hc
  have he : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    filter_upwards [hU] with t1 ht1
    rw [iterAffine V W2 F Ω hΩ hF (c + L1 t1) ht1 L2 b]
    rfl
  have he' : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝[univ] 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    rw [nhdsWithin_univ]
    exact he
  have hE := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℂ) he' he.eq_of_nhds a
  simp only [iteratedFDerivWithin_univ] at hE
  rw [hE, iterAffine V W1 _ Ω hΩ hg c hc L1 a]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact iter_mixed hΩ hF b _ a hc _

end PositivityTheory.Rg.Sw.LVs.TC
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompB
noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Sw.LVs.TC

theorem ml_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (Y : Fin k → Fin 3 → V) (z : ℂ) :
    A (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) =
      ∑ f : Fin k → Fin 3, z ^ (∑ i, (f i : ℕ)) * A (fun i => Y i (f i)) := by
  have h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w := by
    funext i; simp [Fin.sum_univ_three]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]

theorem sum_eq_top {k : ℕ} (f : Fin k → Fin 3) (h : ∑ i, (f i : ℕ) = 2 * k) : ∀ i, f i = 2 := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, (f x : ℕ) ≤ 2 := fun x => by omega
  have hlt : (f i : ℕ) < 2 := by
    rcases Nat.lt_or_ge (f i : ℕ) 2 with h' | h'
    · exact h'
    · exact absurd (Fin.ext (by simp; omega)) hi
  have : ∑ x, (f x : ℕ) < ∑ _x : Fin k, 2 :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this
  omega

theorem infinite_circle : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by
  have hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I) := by
    intro a b hab
    have hre := congrArg Complex.re hab
    simp only at hre
    have e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
      intro x
      rw [show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
    rw [e1, e1] at hre
    have ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (a + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        linarith [Real.pi_gt_three]
    have hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (b + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        linarith [Real.pi_gt_three]
    have := Real.injOn_cos ha hb hre
    have h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩

theorem top_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by
  set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ
  have heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2) := by
    intro z
    simp only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ml_expand]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ infinite_circle
    rintro _ ⟨θ, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]
  have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0
  simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.sum_eq_single (fun _ => 2)]
  · simp only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [if_pos (by ring), mul_one]
  · intro f _ hf
    rw [if_neg, mul_zero]
    intro h2
    exact hf (funext (sum_eq_top f h2.symm))
  · simp

end PositivityTheory.Rg.Sw.LVs.TC
end
end

noncomputable section

open Matrix
open scoped ContDiff Topology

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem detD_affine (hA : IterAffine) {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω)
    {g : M2 n} (hg : g ∈ Ω) (L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n) :
    detD (fun t => F (g + L t)) = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => L (single ((Fintype.equivFin (Fin n)).symm i)
        (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) := by
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [hA (M2 n) (Matrix (Fin n) (Fin n) ℂ) F Ω hΩ hF g hg L]
  rfl

theorem top_zero (hA : IterAffine) {j : ℕ} {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω)
    (hF : ContDiffOn ℂ ∞ F Ω) (hhyp : ∀ a b, InG a → InG b → detD (fun H => F (a * nU H * b)) = 0)
    {g : M2 n} (hg : InG g) : detD (fun t => F (g + topL g j t)) = 0 := by
  have hgΩ : g ∈ Ω := hG hg
  have key : ∀ θ : ℝ, ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
        (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) = 0 := by
    intro θ
    have h0 := hhyp (g * rot j θ) (rot j θ)⁻¹ (TC.inG_mul hg (rot_inG j θ)) (inG_inv (rot_inG j θ))
    simp only [rot_nU] at h0
    rwa [detD_affine hA hΩ hF hgΩ] at h0
  rw [detD_affine hA hΩ hF hgΩ]
  simp only [topL_single]
  have hv := top_vanish (iteratedFDeriv ℂ (Fintype.card (Fin n)) F g)
    (fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : ℂ))
    (fun σ i m => g * (Cm n * (![zLow j, zMid j, zTop j] m) ((Fintype.equivFin (Fin n)).symm i)
      (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)) ?_
  · simpa using hv
  intro θ
  have h1 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i =>
        g * (Cm n * zLow j ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)
        + Complex.exp (2 * ↑θ * Complex.I) • (g * (Cm n * zMid j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n))
        + Complex.exp (2 * ↑θ * Complex.I) ^ 2 • (g * (Cm n * zTop j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)))
      = Complex.exp (2 * ↑θ * Complex.I) ^ Fintype.card (Fin n) * ((Equiv.Perm.sign σ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
          (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1))) := by
    intro σ
    simp_rw [← rotL_single]
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  refine (Finset.sum_congr rfl fun σ _ => h1 σ).trans ?_
  rw [← Finset.mul_sum, key θ, mul_zero]

theorem block_part_embedding_first (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    matrixBlockRestriction (blkA j) (blkA j) (embOn (blkA j) T + embOn (blkB j) S) = embOn (blkA j) T := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, embOn, blkB, ha, hb]

theorem block_part_embedding_second (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    matrixBlockRestriction (blkB j) (blkB j) (embOn (blkA j) T + embOn (blkB j) S) = embOn (blkB j) S := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, embOn, blkB, ha, hb]

theorem block_part_diagonal_first (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) :
    matrixBlockRestriction (blkA j) (blkA j) (bdiag j c c' t) = c • matrixBlockRestriction (blkA j) (blkA j) t := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, bdiag, blkB, ha, hb]

theorem block_part_diagonal_second (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) :
    matrixBlockRestriction (blkB j) (blkB j) (bdiag j c c' t) = c' • matrixBlockRestriction (blkB j) (blkB j) t := by
  ext a b
  by_cases ha : a ∈ blkA j <;> by_cases hb : b ∈ blkA j <;>
    simp [matrixBlockRestriction, bdiag, blkB, ha, hb]

theorem g_mX (g : M2 n) (P Q R S : Matrix (Fin n) (Fin n) ℂ) :
    g * mX (1 + P) Q R (1 + S) = g + g * (Cm n * fromBlocks P Q R S * CmI n) := by
  have h : fromBlocks (1 + P) Q R (1 + S) = (1 : M2 n) + fromBlocks P Q R S := by
    rw [← fromBlocks_one, fromBlocks_add]
    simp
  simp only [mX, cm_inv, h, mul_add, add_mul, mul_one, cm_mul_cmI]

theorem supp_smul {s t : Finset (Fin n)} (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∀ a b, (c • matrixBlockRestriction s t x) a b ≠ 0 → a ∈ s ∧ b ∈ t := by
  intro a b h
  by_contra hn
  apply h
  simp only [Matrix.smul_apply, matrixBlockRestriction, if_neg hn, smul_zero]

private theorem eq_mul_mX_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + topL g j t = g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 *
      mX (1 + (2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkB j) t) 0 0
        (1 + (-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkA j) t) := by
  rw [mul_assoc, ← mX_factor j _ _ _ _ (supp_smul _ _) (supp_smul _ _) (supp_smul _ _) (supp_smul _ _), g_mX]
  simp only [topL, conjL_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, block_part_linear_apply,
    neg_smul]

private theorem conjL_bdiag_eq_mul_mX_blockEntries (g : M2 n) (j : ℕ) (t : Matrix (Fin n) (Fin n) ℂ) :
    g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
      (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) =
    g * mX 1 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
      ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 1 := by
  have h := g_mX g 0 ((2 * Complex.I)⁻¹ • matrixBlockRestriction (blkA j) (blkA j) t)
    ((-(2 * Complex.I)⁻¹) • matrixBlockRestriction (blkB j) (blkB j) t) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_diagonal_first, block_part_diagonal_second]

private theorem comp_blockEntries_eq (g : M2 n) (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ)
    (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    g * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1 =
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (embOn (blkA j) T + embOn (blkB j) S) := by
  have h := g_mX g 0 (embOn (blkA j) T) (embOn (blkB j) S) 0
  simp only [add_zero] at h
  rw [h, conjL_apply]
  simp only [ContinuousLinearMap.zero_apply, block_part_linear_apply, block_part_embedding_first, block_part_embedding_second]

set_option maxHeartbeats 800000 in
theorem topComp_of (hA : IterAffine) (hB : DetDBlock) : TopComp := by
  intro n j F Ω hΩ hG hF hinv hhyp g hg
  have hgΩ : g ∈ Ω := hG hg
  have hc : (2 * Complex.I)⁻¹ ≠ 0 := by simp [Complex.I_ne_zero]
  have hLc : Continuous fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t :=
    continuous_const.add (ContinuousLinearMap.continuous _)
  have hΩ' : IsOpen ((fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) := hΩ.preimage hLc
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω := by
    simp only [Set.mem_preimage, map_zero, add_zero]
    exact hgΩ
  have hψ : ContDiffOn ℂ ∞ (fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t))
      ((fun t : Matrix (Fin n) (Fin n) ℂ =>
        g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 t) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add (ContinuousLinearMap.contDiff _)).contDiffOn (fun t ht => ht)
  have hmain := hB n j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) _ _ hΩ' h0 hψ
  have hzero : (detD fun t : Matrix (Fin n) (Fin n) ℂ =>
      F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
        (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) = 0 := by
    refine Eq.trans ?_ (top_zero (j := j) hA hΩ hG hF hhyp hg)
    have hev : (fun t : Matrix (Fin n) (Fin n) ℂ =>
        F (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j)) (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0
          (bdiag j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t))) =ᶠ[𝓝 0]
        fun t => F (g + topL g j t) := by
      have e1 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + topL g j t ∈ Ω :=
        (continuous_const.add (topL g j).continuous).continuousAt.preimage_mem_nhds
          (by simpa using hΩ.mem_nhds hgΩ)
      have hc2 : Continuous fun t : Matrix (Fin n) (Fin n) ℂ => g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) :=
        continuous_const.add ((ContinuousLinearMap.continuous _).comp (ContinuousLinearMap.continuous _))
      have e2 : ∀ᶠ t in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
          (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) t) ∈ Ω := by
        have hm : Ω ∈ 𝓝 (g + conjL g 0 (matrixBlockRestrictionLinear (blkA j) (blkA j))
            (matrixBlockRestrictionLinear (blkB j) (blkB j)) 0 (bdL j (2 * Complex.I)⁻¹ (-(2 * Complex.I)⁻¹) 0)) := by
          rw [map_zero, map_zero, add_zero]
          exact hΩ.mem_nhds hgΩ
        exact hc2.continuousAt.preimage_mem_nhds hm
      filter_upwards [e1, e2] with t ht1 ht2
      rw [bdL_apply, conjL_bdiag_eq_mul_mX_blockEntries] at ht2
      rw [eq_mul_mX_mul_mX_blockEntries] at ht1
      rw [conjL_bdiag_eq_mul_mX_blockEntries, eq_mul_mX_mul_mX_blockEntries]
      exact (hinv _ _ _ ht1 ht2 (supp_smul _ _) (supp_smul _ _)).symm
    have hI := (hev.iteratedFDeriv ℂ (Fintype.card (Fin n))).eq_of_nhds
    unfold detD
    rw [hI]
  rw [hzero] at hmain
  have hX := (mul_eq_zero.mp hmain.symm).resolve_left
    (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ (neg_ne_zero.mpr hc)))
  simpa only [comp_blockEntries_eq] using hX

theorem topComp : TopComp := topComp_of iterAffine (detDBlock_of iterAffine iterSymm iterNested)

end PositivityTheory.Rg.Sw.LVs.TC

namespace PositivityTheory.Rg.Sw.LVs

theorem topComp : TopComp := TC.topComp

end PositivityTheory.Rg.Sw.LVs
