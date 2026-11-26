module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSUnique
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

theorem transS_unique {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.T.symplecticSiegelAction_mem_upperHalfSpace_and_cocycle ι σ hσ _ I_mem_siegel
  refine GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e1 := h _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e2 := h' _ I_mem_siegel fun k => ζ k ᵥ* spDen σ (I • 1)
  have e := e1.trans e2.symm
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.vecMul_one] using e

theorem val_trans_J : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ →
      TransS (Matrix.J ι ℚ) φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ),
        Ph u ∧ ψ y = u * haar (fun x => φ x * chr y' x) := by
  intro κ ι _ _ _ ⟨p, hp⟩ φ ψ ⟨R, hR, h⟩ hψ ht y
  have e := transS_unique (SymplecticGroup.J_mem ι ℚ) hψ
    ⟨R, hR, FourierJ.ft_level hR h _⟩ ht (FourierJ.trans_J hp hR h)
  refine ⟨I ^ (Fintype.card ι * p), y, ⟨4, by norm_num, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]; simp [Complex.I_pow_four]
  · rw [e]
    simp only [FourierJ.ft, FourierJ.pr, FourierJ.ech, chr]

end GlobalTheory.Phase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSIntertwines
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase GlobalTheory.SiegelAction
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Inter

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

def rowAct (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (y : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    Matrix κ ι ℚ × Matrix κ ι ℚ :=
  (y.2 * σ.toBlocks₁₂ + y.1 * σ.toBlocks₂₂, y.2 * σ.toBlocks₁₁ + y.1 * σ.toBlocks₂₁)

end GlobalTheory.Phase.Inter

namespace GlobalTheory.Phase

open Inter

section
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

private lemma symplectic_transpose_block_relations {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) :
    (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ + -(σ.toBlocks₁₁ * σ.toBlocks₁₂ᵀ) = 0 ∧
      σ.toBlocks₁₂ * σ.toBlocks₂₁ᵀ + -(σ.toBlocks₁₁ * σ.toBlocks₂₂ᵀ) = -1 ∧
      σ.toBlocks₂₂ * σ.toBlocks₁₁ᵀ + -(σ.toBlocks₂₁ * σ.toBlocks₁₂ᵀ) = 1 ∧
      σ.toBlocks₂₂ * σ.toBlocks₂₁ᵀ + -(σ.toBlocks₂₁ * σ.toBlocks₂₂ᵀ) = 0) ∧
    (σ.toBlocks₂₁ᵀ * σ.toBlocks₁₁ + -(σ.toBlocks₁₁ᵀ * σ.toBlocks₂₁) = 0 ∧
      σ.toBlocks₂₁ᵀ * σ.toBlocks₁₂ + -(σ.toBlocks₁₁ᵀ * σ.toBlocks₂₂) = -1 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₁ + -(σ.toBlocks₁₂ᵀ * σ.toBlocks₂₁) = 1 ∧
      σ.toBlocks₂₂ᵀ * σ.toBlocks₁₂ + -(σ.toBlocks₁₂ᵀ * σ.toBlocks₂₂) = 0) := by
  have h1 : σ * Matrix.J ι ℚ * σᵀ = Matrix.J ι ℚ := hσ
  have h2 : σᵀ * Matrix.J ι ℚ * σᵀᵀ = Matrix.J ι ℚ := SymplecticGroup.transpose_mem hσ
  rw [← Matrix.fromBlocks_toBlocks σ] at h1 h2
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.transpose_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h1 h2
  simp at h1 h2
  exact ⟨h1, h2⟩

private lemma inverse_block_combination_eq_fst (A B C D : Matrix ι ι ℚ) (a b : Matrix κ ι ℚ)
    (h : Cᵀ * B + -(Aᵀ * D) = -1) (h' : Dᵀ * B + -(Bᵀ * D) = 0) :
    (b * Dᵀ - a * Cᵀ) * B + (a * Aᵀ - b * Bᵀ) * D = a := by
  have e : (b * Dᵀ - a * Cᵀ) * B + (a * Aᵀ - b * Bᵀ) * D =
      b * (Dᵀ * B + -(Bᵀ * D)) - a * (Cᵀ * B + -(Aᵀ * D)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_assoc]; abel
  rw [e, h, h']; simp

private lemma inverse_block_combination_eq_snd (A B C D : Matrix ι ι ℚ) (a b : Matrix κ ι ℚ)
    (h : Dᵀ * A + -(Bᵀ * C) = 1) (h' : Cᵀ * A + -(Aᵀ * C) = 0) :
    (b * Dᵀ - a * Cᵀ) * A + (a * Aᵀ - b * Bᵀ) * C = b := by
  have e : (b * Dᵀ - a * Cᵀ) * A + (a * Aᵀ - b * Bᵀ) * C =
      b * (Dᵀ * A + -(Bᵀ * C)) - a * (Cᵀ * A + -(Aᵀ * C)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_assoc]; abel
  rw [e, h, h']; simp

private lemma block_combination_mul_transpose_sub_eq_fst (A B C D : Matrix ι ι ℚ) (a b : Matrix κ ι ℚ)
    (h : B * Aᵀ + -(A * Bᵀ) = 0) (h' : D * Aᵀ + -(C * Bᵀ) = 1) :
    (b * B + a * D) * Aᵀ - (b * A + a * C) * Bᵀ = a := by
  have e : (b * B + a * D) * Aᵀ - (b * A + a * C) * Bᵀ =
      b * (B * Aᵀ + -(A * Bᵀ)) + a * (D * Aᵀ + -(C * Bᵀ)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_assoc]; abel
  rw [e, h, h']; simp

private lemma block_combination_mul_transpose_sub_eq_snd (A B C D : Matrix ι ι ℚ) (a b : Matrix κ ι ℚ)
    (h : B * Cᵀ + -(A * Dᵀ) = -1) (h' : D * Cᵀ + -(C * Dᵀ) = 0) :
    (b * A + a * C) * Dᵀ - (b * B + a * D) * Cᵀ = b := by
  have e : (b * A + a * C) * Dᵀ - (b * B + a * D) * Cᵀ =
      -(b * (B * Cᵀ + -(A * Dᵀ))) - a * (D * Cᵀ + -(C * Dᵀ)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.mul_assoc]; abel
  rw [e, h, h']; simp

private lemma om_eq_trace (y y' : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    _root_.GlobalTheory.Phase.om y y' = (y.1 * y'.2ᵀ - y.2 * y'.1ᵀ).trace := by
  unfold _root_.GlobalTheory.Phase.om
  simp [Matrix.trace, Matrix.mul_apply, dotProduct, Finset.sum_sub_distrib, mul_comm]

private lemma inverse_block_pairing_eq (A B C D : Matrix ι ι ℚ) (a b a' b' : Matrix κ ι ℚ)
    (h1 : Cᵀ * A + -(Aᵀ * C) = 0) (h2 : Cᵀ * B + -(Aᵀ * D) = -1)
    (h3 : Dᵀ * A + -(Bᵀ * C) = 1) (h4 : Dᵀ * B + -(Bᵀ * D) = 0) :
    (a * Aᵀ - b * Bᵀ) * (b' * Dᵀ - a' * Cᵀ)ᵀ - (b * Dᵀ - a * Cᵀ) * (a' * Aᵀ - b' * Bᵀ)ᵀ =
      a * b'ᵀ - b * a'ᵀ := by
  have e : (a * Aᵀ - b * Bᵀ) * (b' * Dᵀ - a' * Cᵀ)ᵀ - (b * Dᵀ - a * Cᵀ) * (a' * Aᵀ - b' * Bᵀ)ᵀ =
      -(a * ((Cᵀ * B + -(Aᵀ * D)) * b'ᵀ)) + a * ((Cᵀ * A + -(Aᵀ * C)) * a'ᵀ) +
        b * ((Dᵀ * B + -(Bᵀ * D)) * b'ᵀ) - b * ((Dᵀ * A + -(Bᵀ * C)) * a'ᵀ) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc]; abel
  rw [e, h1, h2, h3, h4]; simp

private lemma qm_add_siegel_theta_transformation {α β : Type} (M N : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (M + N) = _root_.GlobalTheory.SW.qm M + _root_.GlobalTheory.SW.qm N := by
  ext i j; simp [_root_.GlobalTheory.SW.qm]

private lemma qm_neg_siegel_theta_transformation {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (-M) = -_root_.GlobalTheory.SW.qm M := by
  ext i j; simp [_root_.GlobalTheory.SW.qm]

private lemma qm_mul_siegel_theta_transformation' {α β γ : Type} [Fintype β] (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (M * N) = _root_.GlobalTheory.SW.qm M * _root_.GlobalTheory.SW.qm N := by
  ext i j; simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]

private lemma qm_transpose_siegel_theta_transformation {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm Mᵀ = (_root_.GlobalTheory.SW.qm M)ᵀ := by
  ext i j; simp [_root_.GlobalTheory.SW.qm]

private lemma qm_zero_siegel_theta_transformation {α β : Type} :
    _root_.GlobalTheory.SW.qm (0 : Matrix α β ℚ) = 0 := by
  ext i j; simp [_root_.GlobalTheory.SW.qm]

private lemma qm_one_siegel_theta_transformation : _root_.GlobalTheory.SW.qm (1 : Matrix ι ι ℚ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, Matrix.one_apply, h]

private lemma transpose_mobius_mul_sub_eq_of_block_relations (A B C D X Y : Matrix ι ι ℂ)
    (h1 : Cᵀ * A + -(Aᵀ * C) = 0) (h2 : Cᵀ * B + -(Aᵀ * D) = -1)
    (h3 : Dᵀ * A + -(Bᵀ * C) = 1) (h4 : Dᵀ * B + -(Bᵀ * D) = 0) :
    (A * X + B)ᵀ * (C * Y + D) - (C * X + D)ᵀ * (A * Y + B) = Xᵀ - Y := by
  have e : (A * X + B)ᵀ * (C * Y + D) - (C * X + D)ᵀ * (A * Y + B) =
      -(Xᵀ * (Cᵀ * A + -(Aᵀ * C)) * Y) - Xᵀ * (Cᵀ * B + -(Aᵀ * D)) -
        (Dᵀ * A + -(Bᵀ * C)) * Y - (Dᵀ * B + -(Bᵀ * D)) := by
    simp only [Matrix.transpose_add, Matrix.transpose_mul]; noncomm_ring
  rw [e, h1, h2, h3, h4]; noncomm_ring

private lemma isUnit_det_spDen_of_mem_siegel {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) {τ : Matrix ι ι ℂ} (hτ : τ ∈ _root_.GlobalTheory.SW.Siegel ι) :
    IsUnit (_root_.GlobalTheory.SW.spDen σ τ).det := by
  obtain ⟨-, ⟨s1, s2, s3, s4⟩⟩ := symplectic_transpose_block_relations hσ
  have d1 := congrArg _root_.GlobalTheory.SW.qm s1
  have d2 := congrArg _root_.GlobalTheory.SW.qm s2
  have d3 := congrArg _root_.GlobalTheory.SW.qm s3
  have d4 := congrArg _root_.GlobalTheory.SW.qm s4
  simp only [qm_add_siegel_theta_transformation, qm_neg_siegel_theta_transformation, qm_mul_siegel_theta_transformation', qm_transpose_siegel_theta_transformation, qm_zero_siegel_theta_transformation,
    qm_one_siegel_theta_transformation] at d1 d2 d3 d4
  have hτs : τᵀ = τ := hτ.1
  have hY := hτ.2
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hJ : _root_.GlobalTheory.SW.spDen σ τ =
      _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ * τ + _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ := rfl
  rw [hJ] at hv
  set τc : Matrix ι ι ℂ := τ.map (starRingEnd ℂ) with hτc
  have hτcs : τcᵀ = τc := by
    ext i j
    have h := congrFun (congrFun hτs i) j
    simp only [Matrix.transpose_apply] at h
    simp only [hτc, Matrix.transpose_apply, Matrix.map_apply, h]
  have hs : ∀ (M : Matrix ι ι ℂ) (w : ι → ℂ),
      M.map (starRingEnd ℂ) *ᵥ star w = star (M *ᵥ w) := fun M w ↦ by
    ext i; simp [mulVec, dotProduct, map_sum, Complex.star_def]
  have e : _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ * τc + _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ =
      (_root_.GlobalTheory.SW.qm σ.toBlocks₂₁ * τ + _root_.GlobalTheory.SW.qm σ.toBlocks₂₂).map
        (starRingEnd ℂ) := by
    ext i j; simp [hτc, Matrix.mul_apply, _root_.GlobalTheory.SW.qm, map_sum]
  have hconj : (_root_.GlobalTheory.SW.qm σ.toBlocks₂₁ * τc + _root_.GlobalTheory.SW.qm σ.toBlocks₂₂)
      *ᵥ star v = 0 := by
    rw [e, hs, hv, star_zero]
  have iden := transpose_mobius_mul_sub_eq_of_block_relations (_root_.GlobalTheory.SW.qm σ.toBlocks₁₁)
    (_root_.GlobalTheory.SW.qm σ.toBlocks₁₂) (_root_.GlobalTheory.SW.qm σ.toBlocks₂₁)
    (_root_.GlobalTheory.SW.qm σ.toBlocks₂₂) τc τ d1 d2 d3 d4
  have h0 : star v ⬝ᵥ (τcᵀ - τ) *ᵥ v = 0 := by
    rw [← iden, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_zero, zero_sub,
      dotProduct_neg, dotProduct_mulVec, vecMul_transpose, hconj, zero_dotProduct, neg_zero]
  have hvY : star v ⬝ᵥ (τ.map Complex.im).map (fun t : ℝ ↦ (t : ℂ)) *ᵥ v = 0 := by
    have e2 : τcᵀ - τ = (-2 * I) • (τ.map Complex.im).map (fun t : ℝ ↦ (t : ℂ)) := by
      rw [hτcs]; ext i j; apply Complex.ext <;> simp [hτc] <;> ring
    rw [e2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  set x : ι → ℝ := fun i ↦ (v i).re with hxdef
  set y : ι → ℝ := fun i ↦ (v i).im with hydef
  have hre : (star v ⬝ᵥ (τ.map Complex.im).map (fun t : ℝ ↦ (t : ℂ)) *ᵥ v).re =
      x ⬝ᵥ (τ.map Complex.im) *ᵥ x + y ⬝ᵥ (τ.map Complex.im) *ᵥ y := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp [hxdef, hydef, Complex.mul_re]
  have hx0 := hY.posSemidef.dotProduct_mulVec_nonneg x
  have hy0 := hY.posSemidef.dotProduct_mulVec_nonneg y
  rw [star_trivial] at hx0 hy0
  rw [hvY, Complex.zero_re] at hre
  have hxz : x = 0 := by
    by_contra hx
    have h := hY.dotProduct_mulVec_pos hx
    rw [star_trivial] at h
    linarith
  have hyz : y = 0 := by
    by_contra hy
    have h := hY.dotProduct_mulVec_pos hy
    rw [star_trivial] at h
    linarith
  exact hv0 (funext fun i ↦ Complex.ext (by simpa [hxdef] using congrFun hxz i)
    (by simpa [hydef] using congrFun hyz i))

private lemma qv_add_row (P Q : Matrix κ ι ℚ) (k : κ) :
    _root_.GlobalTheory.SW.qv ((P + Q) k) =
      _root_.GlobalTheory.SW.qv (P k) + _root_.GlobalTheory.SW.qv (Q k) := by
  funext j; simp [_root_.GlobalTheory.SW.qv]

private lemma qv_mul_row (P : Matrix κ ι ℚ) (X : Matrix ι ι ℚ) (k : κ) :
    _root_.GlobalTheory.SW.qv ((P * X) k) =
      _root_.GlobalTheory.SW.qv (P k) ᵥ* _root_.GlobalTheory.SW.qm X := by
  funext j; simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, Matrix.mul_apply, vecMul,
    dotProduct]

private lemma ratCast_dotProduct_eq_qv_dotProduct (u v : ι → ℚ) :
    ((u ⬝ᵥ v : ℚ) : ℂ) = _root_.GlobalTheory.SW.qv u ⬝ᵥ _root_.GlobalTheory.SW.qv v := by
  simp [_root_.GlobalTheory.SW.qv, dotProduct]

private lemma thS_heisenberg_translate (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ)
    {τ : Matrix ι ι ℂ} (hτ : τᵀ = τ) (ζ : κ → ι → ℂ) :
    _root_.GlobalTheory.SW.thS (_root_.GlobalTheory.SW.heisS a b φ) τ ζ =
      Complex.exp (↑π * I * ∑ k, (_root_.GlobalTheory.SW.qv (b k) ⬝ᵥ τ *ᵥ _root_.GlobalTheory.SW.qv (b k)
        + 2 * _root_.GlobalTheory.SW.qv (b k) ⬝ᵥ ζ k
        + _root_.GlobalTheory.SW.qv (a k) ⬝ᵥ _root_.GlobalTheory.SW.qv (b k))) *
      _root_.GlobalTheory.SW.thS φ τ
        (fun k ↦ ζ k + _root_.GlobalTheory.SW.qv (a k) + τ *ᵥ _root_.GlobalTheory.SW.qv (b k)) := by
  have hs : ∀ v w : ι → ℂ, v ⬝ᵥ τ *ᵥ w = w ⬝ᵥ τ *ᵥ v := by
    intro v w
    rw [dotProduct_mulVec, ← mulVec_transpose, hτ, dotProduct_comm]
  unfold _root_.GlobalTheory.SW.thS _root_.GlobalTheory.SW.heisS
  rw [← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]
  refine tsum_congr fun u ↦ ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [← mul_add, ← mul_add]
  congr 1
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [ratCast_dotProduct_eq_qv_dotProduct, qv_add_row, dotProduct_add, add_dotProduct, mulVec_add]
  rw [hs (_root_.GlobalTheory.SW.qv (b k)) (_root_.GlobalTheory.SW.qv (u k)),
    dotProduct_comm (_root_.GlobalTheory.SW.qv (b k)) (_root_.GlobalTheory.SW.qv (a k))]
  ring

private lemma exp_mul_mul_exp_mul_eq_of_add_eq (d Θ X Y Z W : ℂ) (h : X + Y = Z + W) :
    Complex.exp X * (d * Complex.exp Y * Θ) = d * Complex.exp Z * (Complex.exp W * Θ) := by
  have e : Complex.exp X * Complex.exp Y = Complex.exp Z * Complex.exp W := by
    rw [← Complex.exp_add, ← Complex.exp_add, h]
  linear_combination (d * Θ) * e

private lemma quadratic_phase_identity_of_symm (τ τ' Q Ji : Matrix ι ι ℂ) (u v z p q : ι → ℂ) (hQ : Qᵀ = Q)
    (h1 : (p + τ *ᵥ q) ᵥ* Ji = u + τ' *ᵥ v) (h2 : Q *ᵥ (p + τ *ᵥ q) = q - Ji *ᵥ v) :
    v ⬝ᵥ τ' *ᵥ v + 2 * v ⬝ᵥ (z ᵥ* Ji) + u ⬝ᵥ v +
        (z + p + τ *ᵥ q) ⬝ᵥ Q *ᵥ (z + p + τ *ᵥ q) =
      z ⬝ᵥ Q *ᵥ z + (q ⬝ᵥ τ *ᵥ q + 2 * q ⬝ᵥ z + p ⬝ᵥ q) := by
  obtain ⟨w, hw⟩ : ∃ w, w = p + τ *ᵥ q := ⟨_, rfl⟩
  rw [← hw] at h1 h2
  have e : (z + p + τ *ᵥ q) ⬝ᵥ Q *ᵥ (z + p + τ *ᵥ q) =
      z ⬝ᵥ Q *ᵥ z + z ⬝ᵥ Q *ᵥ w + w ⬝ᵥ Q *ᵥ z + w ⬝ᵥ Q *ᵥ w := by
    rw [show z + p + τ *ᵥ q = z + w by rw [hw, add_assoc], mulVec_add, dotProduct_add,
      add_dotProduct, add_dotProduct]; ring
  have f1 : w ⬝ᵥ Q *ᵥ z = z ⬝ᵥ Q *ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  have f2 : z ⬝ᵥ Q *ᵥ w = z ⬝ᵥ q - z ⬝ᵥ Ji *ᵥ v := by rw [h2, dotProduct_sub]
  have f3 : w ⬝ᵥ Q *ᵥ w = w ⬝ᵥ q - (u ⬝ᵥ v + v ⬝ᵥ τ' *ᵥ v) := by
    rw [h2, dotProduct_sub, dotProduct_mulVec w Ji v, h1, add_dotProduct,
      dotProduct_comm (τ' *ᵥ v) v]
  have f4 : v ⬝ᵥ (z ᵥ* Ji) = z ⬝ᵥ Ji *ᵥ v := by rw [dotProduct_comm, ← dotProduct_mulVec]
  have f5 : w ⬝ᵥ q = p ⬝ᵥ q + q ⬝ᵥ τ *ᵥ q := by
    rw [hw, add_dotProduct, dotProduct_comm (τ *ᵥ q) q]
  rw [e, f1, f2, f3, f4, f5, dotProduct_comm q z]
  ring

private lemma transS_heisS_rowAct {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (φ ψ : Matrix κ ι ℚ → ℂ)
    (hT : _root_.GlobalTheory.SW.TransS σ φ ψ) (p : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    _root_.GlobalTheory.SW.TransS σ
      (_root_.GlobalTheory.SW.heisS (_root_.GlobalTheory.Phase.Inter.rowAct σ p).1
        (_root_.GlobalTheory.Phase.Inter.rowAct σ p).2 φ)
      (_root_.GlobalTheory.SW.heisS p.1 p.2 ψ) := by
  obtain ⟨⟨-, r2, -, r4⟩, ⟨s1, s2, s3, s4⟩⟩ := symplectic_transpose_block_relations hσ
  obtain ⟨a', b'⟩ := p
  simp only [_root_.GlobalTheory.Phase.Inter.rowAct]
  unfold _root_.GlobalTheory.SW.TransS at hT ⊢
  intro τ hτ ζ
  have hτs : τᵀ = τ := hτ.1
  have hu := isUnit_det_spDen_of_mem_siegel hσ hτ
  have hT' := hT τ hτ (fun k ↦ ζ k
    + _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
    + τ *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k))
  have c2 := congrArg _root_.GlobalTheory.SW.qm r2
  have c4 := congrArg _root_.GlobalTheory.SW.qm r4
  have d1 := congrArg _root_.GlobalTheory.SW.qm s1
  have d2 := congrArg _root_.GlobalTheory.SW.qm s2
  have d3 := congrArg _root_.GlobalTheory.SW.qm s3
  have d4 := congrArg _root_.GlobalTheory.SW.qm s4
  simp only [qm_add_siegel_theta_transformation, qm_neg_siegel_theta_transformation, qm_mul_siegel_theta_transformation', qm_transpose_siegel_theta_transformation, qm_zero_siegel_theta_transformation,
    qm_one_siegel_theta_transformation] at c2 c4 d1 d2 d3 d4
  obtain ⟨A, hA⟩ : ∃ A, A = _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ := ⟨_, rfl⟩
  simp only [← hA, ← hB, ← hC, ← hD] at c2 c4 d1 d2 d3 d4
  obtain ⟨J, hJdef⟩ : ∃ J, J = C * τ + D := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = A * τ + B := ⟨_, rfl⟩
  have hJ : _root_.GlobalTheory.SW.spDen σ τ = J := by rw [hJdef, hC, hD]; rfl
  have hτ' : _root_.GlobalTheory.SW.spAct σ τ = N * J⁻¹ := by rw [hNdef, ← hJ, hA, hB]; rfl
  rw [hJ, hτ'] at hT' ⊢
  rw [hJ] at hu
  simp only [← hC] at hT' ⊢
  beta_reduce at hT'
  have hJ1 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJ2 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hNJ : Nᵀ * J = Jᵀ * N := by
    have e := transpose_mobius_mul_sub_eq_of_block_relations A B C D τ τ d1 d2 d3 d4
    rw [← hNdef, ← hJdef, hτs, sub_self] at e
    exact sub_eq_zero.mp e
  have hτ'sym : (N * J⁻¹)ᵀ = N * J⁻¹ := by
    calc (N * J⁻¹)ᵀ = J⁻¹ᵀ * Nᵀ * (J * J⁻¹) := by
          rw [hJ2, Matrix.mul_one, Matrix.transpose_mul]
      _ = J⁻¹ᵀ * (Nᵀ * J) * J⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (J * J⁻¹)ᵀ * N * J⁻¹ := by
          rw [hNJ, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = N * J⁻¹ := by rw [hJ2, Matrix.transpose_one, Matrix.one_mul]
  have hτ'J : N * J⁻¹ * J = N := by rw [Matrix.mul_assoc, hJ1, Matrix.mul_one]
  have hCJ : J * Cᵀ = C * Jᵀ := by
    have e2 : J * Cᵀ - C * Jᵀ = D * Cᵀ + -(C * Dᵀ) := by
      rw [hJdef, Matrix.transpose_add, Matrix.transpose_mul, hτs]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
    exact sub_eq_zero.mp (e2.trans c4)
  have hQ : (J⁻¹ * C)ᵀ = J⁻¹ * C := by
    calc (J⁻¹ * C)ᵀ = (J⁻¹ * J) * Cᵀ * J⁻¹ᵀ := by
          rw [hJ1, Matrix.one_mul, Matrix.transpose_mul]
      _ = J⁻¹ * (J * Cᵀ) * J⁻¹ᵀ := by simp only [Matrix.mul_assoc]
      _ = J⁻¹ * C * (J⁻¹ * J)ᵀ := by
          rw [hCJ, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J⁻¹ * C := by rw [hJ1, Matrix.transpose_one, Matrix.mul_one]
  have mvT : ∀ (M : Matrix ι ι ℂ) (x : ι → ℂ), M *ᵥ x = x ᵥ* Mᵀ := fun M x ↦ by
    rw [← mulVec_transpose, Matrix.transpose_transpose]
  have symv : ∀ (M : Matrix ι ι ℂ), Mᵀ = M → ∀ x, M *ᵥ x = x ᵥ* M := fun M hM x ↦ by
    rw [mvT, hM]
  have hp : ∀ k, _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k) =
      _root_.GlobalTheory.SW.qv (b' k) ᵥ* B + _root_.GlobalTheory.SW.qv (a' k) ᵥ* D := fun k ↦ by
    rw [qv_add_row, qv_mul_row, qv_mul_row, hB, hD]
  have hq : ∀ k, _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k) =
      _root_.GlobalTheory.SW.qv (b' k) ᵥ* A + _root_.GlobalTheory.SW.qv (a' k) ᵥ* C := fun k ↦ by
    rw [qv_add_row, qv_mul_row, qv_mul_row, hA, hC]
  have hshift : ∀ k, (_root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
      + τ *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k)) ᵥ* J⁻¹ =
      _root_.GlobalTheory.SW.qv (a' k) + (N * J⁻¹) *ᵥ _root_.GlobalTheory.SW.qv (b' k) := by
    intro k
    have e : _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
        + τ *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k) =
        (_root_.GlobalTheory.SW.qv (a' k) + (N * J⁻¹) *ᵥ _root_.GlobalTheory.SW.qv (b' k)) ᵥ* J := by
      rw [add_vecMul, symv _ hτ'sym, vecMul_vecMul, hτ'J, symv _ hτs, hp, hq, hJdef, hNdef]
      simp only [vecMul_add, add_vecMul, ← vecMul_vecMul]; abel
    rw [e, vecMul_vecMul, hJ2, vecMul_one]
  have eAD : A * Dᵀ = B * Cᵀ + 1 := by
    have h := c2; rw [add_neg_eq_iff_eq_add] at h; rw [h]; abel
  have eCD : C * Dᵀ = D * Cᵀ := by
    have h := c4; rw [add_neg_eq_iff_eq_add, zero_add] at h; exact h.symm
  have hcoeff : ∀ k, (J⁻¹ * C) *ᵥ (_root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
      + τ *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k)) =
      _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k)
        - J⁻¹ *ᵥ _root_.GlobalTheory.SW.qv (b' k) := by
    intro k
    have hpq : C *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
        + _root_.GlobalTheory.SW.qv (b' k) =
        D *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k) := by
      rw [mvT C, mvT D, hp, hq]
      simp only [add_vecMul, vecMul_vecMul, eAD, eCD, vecMul_add, vecMul_one]; abel
    have hx : C *ᵥ (_root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
        + τ *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k)) =
        J *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k)
          - _root_.GlobalTheory.SW.qv (b' k) := by
      rw [mulVec_add, hJdef, add_mulVec, ← mulVec_mulVec, ← hpq]; abel
    rw [← mulVec_mulVec, hx, mulVec_sub, mulVec_mulVec, hJ1, one_mulVec]
  rw [thS_heisenberg_translate _ _ _ hτ'sym, thS_heisenberg_translate _ _ _ hτs]
  beta_reduce
  have harg : (fun k ↦ ζ k ᵥ* J⁻¹ + _root_.GlobalTheory.SW.qv (a' k)
      + (N * J⁻¹) *ᵥ _root_.GlobalTheory.SW.qv (b' k)) =
      fun k ↦ (ζ k + _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₂ + a' * σ.toBlocks₂₂) k)
        + τ *ᵥ _root_.GlobalTheory.SW.qv ((b' * σ.toBlocks₁₁ + a' * σ.toBlocks₂₁) k)) ᵥ* J⁻¹ := by
    funext k; rw [add_assoc (ζ k), add_vecMul, hshift k, add_assoc]
  rw [harg, hT']
  refine exp_mul_mul_exp_mul_eq_of_add_eq _ _ _ _ _ _ ?_
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦
    quadratic_phase_identity_of_symm τ (N * J⁻¹) (J⁻¹ * C) J⁻¹ _ _ (ζ k) _ _ hQ (hshift k) (hcoeff k)

theorem _root_.GlobalTheory.Phase.transS_intertwines : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∃ T : (Matrix κ ι ℚ × Matrix κ ι ℚ) ≃+ (Matrix κ ι ℚ × Matrix κ ι ℚ), (∀ y y', _root_.GlobalTheory.Phase.om (T y) (T y') = _root_.GlobalTheory.Phase.om y y') ∧ ∀ φ ψ : Matrix κ ι ℚ → ℂ, _root_.GlobalTheory.SW.IsSB φ → _root_.GlobalTheory.SW.IsSB ψ → _root_.GlobalTheory.SW.TransS σ φ ψ → ∀ y, _root_.GlobalTheory.SW.TransS σ (_root_.GlobalTheory.SW.heisS y.1 y.2 φ) (_root_.GlobalTheory.SW.heisS (T y).1 (T y).2 ψ) := by
  intro κ ι _ _ _ σ hσ
  obtain ⟨⟨r1, r2, r3, r4⟩, ⟨s1, s2, s3, s4⟩⟩ := symplectic_transpose_block_relations hσ
  let T : (Matrix κ ι ℚ × Matrix κ ι ℚ) ≃+ (Matrix κ ι ℚ × Matrix κ ι ℚ) :=
    { toFun := fun y ↦ (y.1 * σ.toBlocks₁₁ᵀ - y.2 * σ.toBlocks₁₂ᵀ,
        y.2 * σ.toBlocks₂₂ᵀ - y.1 * σ.toBlocks₂₁ᵀ)
      invFun := _root_.GlobalTheory.Phase.Inter.rowAct σ
      left_inv := fun y ↦ Prod.ext
        (inverse_block_combination_eq_fst σ.toBlocks₁₁ σ.toBlocks₁₂ σ.toBlocks₂₁ σ.toBlocks₂₂ y.1 y.2 s2 s4)
        (inverse_block_combination_eq_snd σ.toBlocks₁₁ σ.toBlocks₁₂ σ.toBlocks₂₁ σ.toBlocks₂₂ y.1 y.2 s3 s1)
      right_inv := fun y ↦ Prod.ext
        (block_combination_mul_transpose_sub_eq_fst σ.toBlocks₁₁ σ.toBlocks₁₂ σ.toBlocks₂₁ σ.toBlocks₂₂ y.1 y.2 r1 r3)
        (block_combination_mul_transpose_sub_eq_snd σ.toBlocks₁₁ σ.toBlocks₁₂ σ.toBlocks₂₁ σ.toBlocks₂₂ y.1 y.2 r2 r4)
      map_add' := fun y z ↦ Prod.ext
        (by simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul]; abel)
        (by simp only [Prod.fst_add, Prod.snd_add, Matrix.add_mul]; abel) }
  refine ⟨T, fun y y' ↦ ?_, fun φ ψ _ _ hT y ↦ ?_⟩
  · rw [om_eq_trace, om_eq_trace]
    exact congrArg Matrix.trace (inverse_block_pairing_eq σ.toBlocks₁₁ σ.toBlocks₁₂ σ.toBlocks₂₁
      σ.toBlocks₂₂ y.1 y.2 y'.1 y'.2 s1 s2 s3 s4)
  · have hy : _root_.GlobalTheory.Phase.Inter.rowAct σ (T y) = y := T.symm_apply_apply y
    have key := transS_heisS_rowAct hσ φ ψ hT (T y)
    rw [hy] at key
    exact key
end

end GlobalTheory.Phase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhase
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhase
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ParabValues

open GlobalTheory.SW.Parab

theorem ph_rat_mul_exp (r q : ℚ) : Ph ((r : ℂ) * cexp (-(Real.pi * I * (q : ℂ)))) := by
  refine ⟨2 * q.den, by have := q.den_pos; omega, ?_⟩
  have hn : ‖cexp (-(Real.pi * I * (q : ℂ)))‖ = 1 := by
    have : -(Real.pi * I * (q : ℂ)) = ((-(Real.pi * q) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have he : cexp (-(Real.pi * I * (q : ℂ))) ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    have h : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
    push_cast
    rw [← h]
    ring
  rw [mul_pow, he, mul_one, norm_mul, hn, mul_one, Complex.norm_ratCast]
  have : (|(r : ℝ)|) ^ (2 * q.den) = (r : ℝ) ^ (2 * q.den) := Even.pow_abs ⟨q.den, by ring⟩ _
  rw [← Complex.ofReal_pow, this]
  push_cast
  rfl

theorem trans_explicit (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hC : σ.toBlocks₂₁ = 0)
    (φ : Matrix κ ι ℚ → ℂ) (hφ : IsSB φ) :
    IsSB (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) ∧
    TransS σ φ (((σ.toBlocks₂₂.det : ℂ) ^ (Fintype.card κ / 2)) •
      fun x => parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) x * φ (x * σ.toBlocks₁₁)) := by
  classical
  set A := σ.toBlocks₁₁ with hA
  set B := σ.toBlocks₁₂ with hB
  set D := σ.toBlocks₂₂ with hD
  have hDA : D * Aᵀ = 1 := by
    have h := SymplecticGroup.mem_iff.mp hσ
    rw [← Matrix.fromBlocks_toBlocks σ, hC, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
    have := congrArg Matrix.toBlocks₂₁ h
    simpa using this
  have hdet : D.det * A.det = 1 := by
    have := congrArg Matrix.det hDA
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hA0 : A.det ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA0
  refine ⟨?_, ?_⟩
  · have h1 := isSB_parChar_mul (B * Aᵀ) _
      ((GlobalTheory.SW.LinChange.haar_mul ℚ κ ι φ hφ).1 A hA0).1
    exact (GlobalTheory.SW.isSB_algebra_haar_linear ℚ κ ι _ _ h1 h1).2.1 _
  · intro τ _ ζ
    have hden : spDen σ τ = qm D := by
      unfold spDen
      rw [hC]
      have : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
      rw [this, Matrix.zero_mul, zero_add]
    have hinv : (qm D)⁻¹ = (qm A)ᵀ := by
      apply Matrix.inv_eq_right_inv
      have e : (qm A)ᵀ = qm Aᵀ := rfl
      rw [e, ← qm_mul', hDA]
      ext i j; by_cases h : i = j <;> simp [qm, Matrix.one_apply, h]
    have hdetD : (qm D).det = (D.det : ℂ) := ((Rat.castHom ℂ).map_det D).symm
    have hC' : qm σ.toBlocks₂₁ = 0 := by rw [hC]; ext i j; simp [qm]
    unfold spAct
    rw [hden, hinv, hC', hdetD]
    simp only [Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero, Finset.sum_const_zero,
      mul_zero, Complex.exp_zero, mul_one]
    let e : Matrix κ ι ℚ ≃ Matrix κ ι ℚ :=
      { toFun := fun x => x * A
        invFun := fun x => x * A⁻¹
        left_inv := fun x => Matrix.mul_nonsing_inv_cancel_right A x hAu
        right_inv := fun x => Matrix.nonsing_inv_mul_cancel_right A x hAu }
    unfold thS
    rw [← tsum_mul_left, ← e.tsum_eq (fun x => _ * (φ x * _))]
    refine tsum_congr fun x => ?_
    show ((D.det : ℂ) ^ (Fintype.card κ / 2)) * (parChar (B * Aᵀ) x * φ (x * A)) * _ =
      _ * (φ (x * A) * cexp (Real.pi * I * ∑ k, (qv ((x * A) k) ⬝ᵥ τ *ᵥ qv ((x * A) k) +
        2 * (qv ((x * A) k) ⬝ᵥ ζ k))))
    rw [mul_assoc, mul_comm (parChar _ _), mul_assoc]
    congr 2
    unfold parChar
    rw [← Complex.exp_add]
    congr 1
    rw [← mul_neg, ← mul_add, Rat.cast_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qv_bilin, qv_row_mul, qm_mul']
    have e1 : qm Aᵀ = (qm A)ᵀ := rfl
    beta_reduce
    rw [e1, Matrix.add_mul, Matrix.add_mulVec, dotProduct_add, Matrix.vecMul_transpose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_transpose, Matrix.dotProduct_mulVec (qv (x k)) (qm A),
      Matrix.dotProduct_mulVec (qv (x k)) (qm A)]
    ring

theorem trans_unique (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι]
    (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ) (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    (φ ψ ψ' : Matrix κ ι ℚ → ℂ) (hψ : IsSB ψ) (hψ' : IsSB ψ') (h : TransS σ φ ψ)
    (h' : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' hψ hψ' _ hs fun ζ => ?_
  have e : ζ = fun k => (ζ k ᵥ* spDen σ (I • (1 : Matrix ι ι ℂ))) ᵥ*
      (spDen σ (I • (1 : Matrix ι ι ℂ)))⁻¹ := by
    funext k
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.vecMul_one]
  rw [e, h _ I_mem_siegel, h' _ I_mem_siegel]

theorem values_parabolic : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  intro κ ι _ _ _ _ σ hσ hC φ ψ hφ hψ h y
  obtain ⟨h1, h2⟩ := trans_explicit κ ι σ hσ hC φ hφ
  have e := trans_unique κ ι σ hσ φ _ _ hψ h1 h h2
  refine ⟨((σ.toBlocks₂₂.det ^ (Fintype.card κ / 2) : ℚ) : ℂ) *
    parChar (σ.toBlocks₁₂ * σ.toBlocks₁₁ᵀ) y, y * σ.toBlocks₁₁, ph_rat_mul_exp _ _, ?_⟩
  rw [e]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.Phase.ParabValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhaseStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, σ.toBlocks₂₁ = 0 → ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB φ → IsSB ψ → TransS σ φ ψ → ∀ y, ∃ (u : ℂ) (y' : Matrix κ ι ℚ), Ph u ∧ ψ y = u * φ y' := by
  first | exact @GlobalTheory.Phase.ParabValues.values_parabolic | exact GlobalTheory.Phase.ParabValues.values_parabolic | (intros; apply GlobalTheory.Phase.ParabValues.values_parabolic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransform
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.WeilPV

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem trans_unique {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (h1 : IsSB ψ) (h2 : IsSB ψ') (t1 : TransS σ φ ψ)
    (t2 : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' h1 h2 _ hs fun ζ => ?_
  have e1 := t1 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e2 := t2 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e := e1.trans e2.symm
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
    Matrix.vecMul_one] at e
  exact e

omit [DecidableEq ι] in
theorem thS_smul (c : ℂ) (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) :
    thS (c • φ) τ ζ = c * thS φ τ ζ := by
  unfold thS
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem trans_smul {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} {φ ψ : Matrix κ ι ℚ → ℂ} (c : ℂ)
    (t : TransS σ φ ψ) : TransS σ (c • φ) (c • ψ) := fun τ hτ ζ => by
  rw [thS_smul, thS_smul, t τ hτ ζ]; ring

omit [DecidableEq ι] in
theorem sb_smul (c : ℂ) {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem vac_trans {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : ∃ A ε, VacS A ε φ) :
    ∃ A ε, VacS A ε ψ := by
  obtain ⟨A, ε, h⟩ := h
  obtain ⟨T, hom, hT⟩ := GlobalTheory.Phase.transS_intertwines κ ι σ hσ
  have mem : ∀ y, y ∈ A.map T.toAddMonoidHom ↔ T.symm y ∈ A := fun y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa using hz, fun hy => ⟨_, hy, by simp⟩⟩
  have hom' : ∀ y y', om (T.symm y) (T.symm y') = om y y' := fun y y' => by
    rw [← hom]; simp
  refine ⟨A.map T.toAddMonoidHom, fun y => ε (T.symm y), ?_, ?_, ?_, ?_, ?_, hψ, ?_⟩
  · obtain ⟨S, hS⟩ := h.fg
    classical
    let e := A.equivMapOfInjective T.toAddMonoidHom T.injective
    refine ⟨S.image e, ?_⟩
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∈ AddSubsemigroup.closure (S : Set A) := by rw [hS]; trivial
    induction hx using AddSubsemigroup.closure_induction with
    | mem x hx =>
        apply AddSubsemigroup.subset_closure
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using AddSubsemigroup.add_mem _ (ihx (by trivial)) (ihy (by trivial))
  · intro y
    rw [mem, h.dual]
    constructor
    · intro H y' hy'
      rw [← hom']; exact H _ ((mem _).1 hy')
    · intro H y' hy'
      have := H (T y') ((mem _).2 (by simpa using hy'))
      rw [← hom'] at this
      simpa using this
  · intro y hy; exact h.norm _ ((mem _).1 hy)
  · intro y hy y' hy'
    rw [map_add (f := _), h.semi _ ((mem _).1 hy) _ ((mem _).1 hy'), hom']
  · obtain ⟨m, hm, H⟩ := h.ord
    exact ⟨m, hm, fun y hy => by rw [map_nsmul]; exact H _ ((mem _).1 hy)⟩
  · intro y hy
    have t1 := trans_smul (ε (T.symm y)) (hT φ ψ h.sb hψ t (T.symm y))
    rw [h.fix _ ((mem _).1 hy), T.apply_symm_apply] at t1
    exact trans_unique hσ (sb_smul _ (GlobalTheory.SW.heisS_laws _ _ _ _ ψ hψ).1) hψ t1 t

omit [DecidableEq ι] in
theorem pv_sb {φ : Matrix κ ι ℚ → ℂ} (h : PV φ) : IsSB φ := by
  obtain ⟨⟨_, _, h⟩, -⟩ := h
  exact h.sb

theorem pv_parabolic (he : Even (Fintype.card κ)) {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (h0 : σ.toBlocks₂₁ = 0)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans hσ hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity κ ι he σ hσ h0 φ ψ (pv_sb h) hψ t y
  rw [e]; exact hu.mul (h.2 _)

theorem pv_J (he : Even (Fintype.card κ))
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS (Matrix.J ι ℚ) φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans (SymplecticGroup.J_mem ι ℚ) hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.Phase.val_trans_J κ ι he φ ψ (pv_sb h) hψ t y
  rw [e]
  exact hu.mul (GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase κ ι _
    ((GlobalTheory.Phase.shape_conj_chr_mul κ ι φ ((GlobalTheory.Phase.VacShape.vacuum_shape κ ι φ).2.1 h)).2.1 y'))

theorem pv_mul (he : Even (Fintype.card κ)) {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (H : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ)
    (H' : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ' φ ψ → PV φ → PV ψ) :
    ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (σ' * σ) φ ψ → PV φ → PV ψ := by
  intro φ ψ hψ t h
  obtain ⟨w, hw⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ he hσ
  obtain ⟨w', hw'⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ' he hσ'
  obtain ⟨s1, t1, -⟩ := hw φ (pv_sb h)
  obtain ⟨s2, t2, -⟩ := hw' (w φ) s1
  have t3 := GlobalTheory.SW.transS_comp κ ι σ σ' hσ hσ' _ _ _ t1 t2
  rw [trans_unique (mul_mem hσ' hσ) hψ s2 t t3]
  exact H' _ _ s2 t2 (H _ _ s1 t1 h)

theorem pv_of_transS : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  intro κ ι _ _ _ he σ hσ
  obtain ⟨p₁, h1, p₂, h2, p₃, h3, z1, z2, z3, rfl⟩ :=
    GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ := SymplecticGroup.J_mem ι ℚ
  have P : ∀ p ∈ Matrix.symplecticGroup ι ℚ, p.toBlocks₂₁ = 0 →
      ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS p φ ψ → PV φ → PV ψ :=
    fun p hp z φ ψ hψ t h => pv_parabolic he hp z hψ t h
  have Q : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (Matrix.J ι ℚ) φ ψ → PV φ → PV ψ :=
    fun φ ψ hψ t h => pv_J he hψ t h
  have a := mul_mem h1 hJ
  have b := mul_mem a h2
  have c := mul_mem b hJ
  exact pv_mul he h3 c (P _ h3 z3) (pv_mul he hJ b Q (pv_mul he h2 a (P _ h2 z2)
    (pv_mul he hJ h1 Q (P _ h1 z1))))

end GlobalTheory.Phase.WeilPV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransformStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnityPhaseVacuum_siegelThetaTransform : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  first | exact @GlobalTheory.Phase.WeilPV.pv_of_transS | exact GlobalTheory.Phase.WeilPV.pv_of_transS | (intros; apply GlobalTheory.Phase.WeilPV.pv_of_transS <;> assumption)
end
