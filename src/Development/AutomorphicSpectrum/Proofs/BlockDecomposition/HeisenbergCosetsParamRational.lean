module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCentreRationalForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockFourMatrices
noncomputable def UpperTheory.Reformulated.B.BlockFourMatrices.blk4 :
    {R : Type} →
      {n : ℕ} →
        Matrix (Fin n) (Fin n) R →
          Matrix (Fin n) (Fin n) R →
            Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R → Matrix (Fin (n + n)) (Fin (n + n)) R :=
    fun {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) ↦
      (Matrix.fromBlocks a b c d).submatrix (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)
        (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)

theorem UpperTheory.Reformulated.B.BlockFourMatrices.main :
    ∀ {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R),
      (UpperTheory.Reformulated.B.BlockFourMatrices.blk4 a b c d).map f = UpperTheory.Reformulated.B.BlockFourMatrices.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  intro R S m f a b c d
  unfold UpperTheory.Reformulated.B.BlockFourMatrices.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRows
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRows
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SRows

theorem blkD_siegel_mul {K : Type} [Field K] {n : ℕ} {y : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hy : IsSiegelP y) (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * GlobalTheory.CompanionTheory.RatPtsUnn.blkD W := by
  ext i j
  change (y * W) (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = _
  rw [Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type, Matrix.mul_apply]
  have h0 : ∑ k : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl k)) *
      W (finSumFinEquiv (Sum.inl k)) (finSumFinEquiv (Sum.inr j)) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hy i k, zero_mul]
  rw [h0, zero_add]
  rfl

theorem inverse_unitary_block_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {a b c d : Matrix (Fin n) (Fin n) K}
    (h : IsUnitary σ (blk4 0 1 (-1) 0) (blk4 a b c d)) :
    (blk4 a b c d)⁻¹ = blk4 (cT σ d) (-cT σ b) (-cT σ c) (cT σ a) := by
  have hJJ' : (blk4 0 (-1) 1 0 : Matrix (Fin (n + n)) (Fin (n + n)) K) * blk4 0 1 (-1) 0 = 1 := by
    rw [submatrix_fromBlocks_mul]
    simp [GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]
  have h0 : cT σ (blk4 a b c d) * blk4 0 1 (-1) 0 * blk4 a b c d = blk4 0 1 (-1) 0 := h
  have h1 : (blk4 0 (-1) 1 0 * cT σ (blk4 a b c d) * blk4 0 1 (-1) 0) * blk4 a b c d = 1 := by
    rw [mul_assoc (blk4 0 (-1) 1 0), mul_assoc (blk4 0 (-1) 1 0), h0, hJJ']
  rw [Matrix.inv_eq_left_inv h1, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

end GlobalTheory.CompanionTheory.ZUnf.SRows

theorem GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (x r : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit r.det → IsUnitary σ (blk4 0 1 (-1) 0) x → IsUnitary σ (blk4 0 1 (-1) 0) r →
    (IsSiegelP (x * r⁻¹) ↔ ∃ T : Matrix (Fin n) (Fin n) K, lowerC x = T * lowerC r ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD r) := by
  intro K _ σ _ n x r hr hx hrU
  obtain ⟨a, b, hr4⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq r
  constructor
  · intro h
    have e : x = (x * r⁻¹) * r := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hr, Matrix.mul_one]
    refine ⟨GlobalTheory.CompanionTheory.RatPtsUnn.blkD (x * r⁻¹), ?_, ?_⟩
    · conv_lhs => rw [e]
      exact GlobalTheory.CompanionTheory.SwUnf.lowerC_siegel_mul h r
    · conv_lhs => rw [e]
      exact GlobalTheory.CompanionTheory.ZUnf.SRows.blkD_siegel_mul h r
  · rintro ⟨T, h1, h2⟩
    rw [GlobalTheory.CompanionTheory.SwUnf.BigCell.isSiegelParabolic_iff]
    obtain ⟨a', b', hx4⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x
    have hU' : IsUnitary σ (blk4 0 1 (-1) 0)
        (blk4 a b (lowerC r) (GlobalTheory.CompanionTheory.RatPtsUnn.blkD r)) := by
      rw [← hr4]; exact hrU
    have hinv := GlobalTheory.CompanionTheory.ZUnf.SRows.inverse_unitary_block_form σ hU'
    rw [← hr4] at hinv
    have hrel := GlobalTheory.CompanionTheory.SwUnf.BigCell.lower_rel σ hU'
    have e : lowerC (x * r⁻¹) = lowerC x * cT σ (GlobalTheory.CompanionTheory.RatPtsUnn.blkD r)
        - GlobalTheory.CompanionTheory.RatPtsUnn.blkD x * cT σ (lowerC r) := by
      rw [hinv]
      conv_lhs => rw [hx4]
      rw [submatrix_fromBlocks_mul, GlobalTheory.CompanionTheory.SwUnf.BigCell.lowerLeft_block]
      simp [sub_eq_add_neg]
    rw [e, h1, h2, mul_assoc, mul_assoc, hrel, sub_self]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRowsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_parabolic_quotient_iff_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (x r : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit r.det → IsUnitary σ (blk4 0 1 (-1) 0) x → IsUnitary σ (blk4 0 1 (-1) 0) r →
    (IsSiegelP (x * r⁻¹) ↔ ∃ T : Matrix (Fin n) (Fin n) K, lowerC x = T * lowerC r ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD r) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows | exact GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows | (intros; apply GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCellBlockNormalForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCellBlockNormalForm
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

section RowReduce

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem exists_rowReduce_firstCols (hn : ρ + p = n) (C : Matrix (Fin n) (Fin n) K)
    (h : LinearMap.ker (C.mulVecLin ∘ₗ zinc hn) = ⊥) :
    ∃ T : Matrix (Fin n) (Fin n) K, IsUnit T.det ∧ ∀ u, (T * C).mulVec (zinc hn u) = -(zinc hn u) := by
  have hz : Function.Injective (zinc (K := K) hn) := by
    intro u v huv
    funext j
    have := congrFun huv ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
    simpa [zinc] using this
  set f : (Fin ρ → K) →ₗ[K] (Fin n → K) := C.mulVecLin ∘ₗ zinc hn with hfdef
  set g : (Fin ρ → K) →ₗ[K] (Fin n → K) := -(zinc hn) with hgdef
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp h
  have hg : Function.Injective g := by
    intro u v huv
    apply hz
    simpa [hgdef] using huv
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range g)
  have hfin : Module.finrank K W = Module.finrank K W' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW
    have h2 := Submodule.finrank_add_eq_of_isCompl hW'
    rw [LinearMap.finrank_range_of_inj hf] at h1
    rw [LinearMap.finrank_range_of_inj hg] at h2
    omega
  let ψ : W ≃ₗ[K] W' := LinearEquiv.ofFinrankEq W W' hfin
  let φ : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
    (LinearEquiv.ofInjective f hf).symm.trans (LinearEquiv.ofInjective g hg)
  let A : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
    (Submodule.prodEquivOfIsCompl _ _ hW).symm.trans
      ((φ.prodCongr ψ).trans (Submodule.prodEquivOfIsCompl _ _ hW'))
  have hA : ∀ u, A (f u) = g u := by
    intro u
    have h0 : (Submodule.prodEquivOfIsCompl _ _ hW).symm (f u) =
        ((⟨f u, LinearMap.mem_range_self f u⟩ : LinearMap.range f), (0 : W)) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hW ⟨f u, LinearMap.mem_range_self f u⟩
    have h1 : φ ⟨f u, LinearMap.mem_range_self f u⟩ = ⟨g u, LinearMap.mem_range_self g u⟩ := by
      have : (LinearEquiv.ofInjective f hf).symm ⟨f u, LinearMap.mem_range_self f u⟩ = u :=
        (LinearEquiv.ofInjective f hf).symm_apply_apply u
      simp only [φ, LinearEquiv.trans_apply, this]
      rfl
    simp only [A, LinearEquiv.trans_apply, h0, LinearEquiv.prodCongr_apply, h1, ψ.map_zero]
    simp
  refine ⟨LinearMap.toMatrix' A.toLinearMap, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_left_inverse (B := LinearMap.toMatrix' A.symm.toLinearMap) ?_
    rw [← LinearMap.toMatrix'_comp]
    simp
  · intro u
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    exact hA u

theorem exists_bl_firstCols (hn : ρ + p = n) (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ u, N.mulVec (zinc hn u) = -(zinc hn u)) :
    ∃ (X : Matrix (Fin ρ) (Fin p) K) (c' : Matrix (Fin p) (Fin p) K), N = bl hn (-1) X 0 c' := by
  classical
  set e := finSumFinEquiv.trans (finCongr hn) with he
  refine ⟨(N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₂, ?_⟩
  have hcol : ∀ (i : Fin n) (j : Fin ρ), N i (e (Sum.inl j)) = -(zinc hn (Pi.single j 1) i) := by
    intro i j
    have h1 := congrFun (h (Pi.single j 1)) i
    have h2 : zinc hn (Pi.single j (1 : K)) = Pi.single (e (Sum.inl j)) 1 := by
      funext k
      obtain ⟨k, rfl⟩ := e.surjective k
      rcases k with k | k
      · simp [zinc, he, Pi.single_apply]
      · have hne : e (Sum.inr k) ≠ e (Sum.inl j) := fun hh => by simpa using e.injective hh
        rw [Pi.single_eq_of_ne hne]
        simp [zinc, he]
    rw [h2, Matrix.mulVec_single_one] at h1
    rw [h2]
    simpa using h1
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simp [bl, ← he, hcol, zinc, Matrix.one_apply, Pi.single_apply]
  · simp [bl, ← he, Matrix.toBlocks₁₂]
  · simp [bl, ← he, hcol, zinc]
  · simp [bl, ← he, Matrix.toBlocks₂₂]

theorem exists_bl_blocks (hn : ρ + p = n) (N : Matrix (Fin n) (Fin n) K) :
    ∃ (a : Matrix (Fin ρ) (Fin ρ) K) (b : Matrix (Fin ρ) (Fin p) K) (c : Matrix (Fin p) (Fin ρ) K)
      (d : Matrix (Fin p) (Fin p) K), N = bl hn a b c d := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  refine ⟨(N.submatrix e e).toBlocks₁₁, (N.submatrix e e).toBlocks₁₂, (N.submatrix e e).toBlocks₂₁,
    (N.submatrix e e).toBlocks₂₂, ?_⟩
  unfold bl
  rw [Matrix.fromBlocks_toBlocks]
  ext i j
  simp [← he]

end RowReduce

theorem rowReduce_lowerC : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit x.det → IsUnitary σ (blk4 0 1 (-1) 0) x → LinearMap.ker ((lowerC x).mulVecLin ∘ₗ zinc hn) = ⊥ →
    ∃ (T₀ : Matrix (Fin n) (Fin n) K) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
      IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) ∧
      IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det ∧
      lowerC x = T₀ * bl hn (-1) X 0 c' ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T₀ * bl hn Z Y W d' := by
  intro K _ σ hσ n ρ p hn x hdet hU hker
  obtain ⟨T, hT, hTC⟩ := exists_rowReduce_firstCols hn (lowerC x) hker
  obtain ⟨X, c', hN⟩ := exists_bl_firstCols hn (T * lowerC x) hTC
  obtain ⟨a, b, hx⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq x
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hiT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have hcc : ∀ M : Matrix (Fin n) (Fin n) K, cT σ (cT σ M) = M := by
    intro M
    ext i j
    simp [cT, hσ]
  have hcTi : cT σ T * cT σ T⁻¹ = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  have hcTi' : cT σ T⁻¹ * cT σ T = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, hiT, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  set m : Matrix (Fin (n + n)) (Fin (n + n)) K := blk4 (cT σ T⁻¹) 0 0 T with hm
  have hmU : cT σ m * blk4 0 1 (-1) 0 * m = blk4 0 1 (-1) 0 := by
    rw [hm, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hcc]
    have hc0 : cT σ (0 : Matrix (Fin n) (Fin n) K) = 0 := by
      ext i j
      simp [cT]
    simp [hTi, hcTi, hc0]
  have hmdet : IsUnit m.det := by
    refine Matrix.isUnit_det_of_left_inverse (B := blk4 (cT σ T) 0 0 T⁻¹) ?_
    rw [hm, submatrix_fromBlocks_mul]
    simp [hTi, hcTi, GlobalTheory.CompanionTheory.SwUnf.BigCell.block_identity_eq_one]
  have hmx : m * x = blk4 (cT σ T⁻¹ * a) (cT σ T⁻¹ * b) (T * lowerC x) (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x) := by
    conv_lhs => rw [hx, hm, submatrix_fromBlocks_mul]
    simp
  obtain ⟨a₁, a₂, a₃, a₄, ha⟩ := exists_bl_blocks hn (cT σ T⁻¹ * a)
  obtain ⟨b₁, b₂, b₃, b₄, hb⟩ := exists_bl_blocks hn (cT σ T⁻¹ * b)
  obtain ⟨Z, Y, W, d', hd⟩ := exists_bl_blocks hn (T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD x)
  have hfin : blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d') = m * x := by
    rw [hmx, ha, hb, hN, hd]
  refine ⟨T⁻¹, a₁, b₁, Z, a₂, b₂, X, Y, a₃, b₃, W, a₄, b₄, c', d', ?_, ?_, ?_, ?_⟩
  · rw [hfin]
    unfold IsUnitary at hU ⊢
    have hc : cT σ (m * x) = cT σ x * cT σ m := by
      unfold cT
      rw [Matrix.map_mul, Matrix.transpose_mul]
    rw [hc]
    calc cT σ x * cT σ m * blk4 0 1 (-1) 0 * (m * x)
        = cT σ x * (cT σ m * blk4 0 1 (-1) 0 * m) * x := by simp only [Matrix.mul_assoc]
      _ = blk4 0 1 (-1) 0 := by rw [hmU, hU]
  · rw [hfin, Matrix.det_mul]
    exact hmdet.mul hdet
  · rw [← hN, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  · rw [← hd, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
end GlobalTheory.CompanionTheory.ZUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCellBlockNormalFormStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_cell_block_normal_form : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (x : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit x.det → IsUnitary σ (blk4 0 1 (-1) 0) x → LinearMap.ker ((lowerC x).mulVecLin ∘ₗ zinc hn) = ⊥ →
    ∃ (T₀ : Matrix (Fin n) (Fin n) K) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
      IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) ∧
      IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det ∧
      lowerC x = T₀ * bl hn (-1) X 0 c' ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T₀ * bl hn Z Y W d' := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.rowReduce_lowerC | exact GlobalTheory.CompanionTheory.ZUnf.rowReduce_lowerC | (intros; apply GlobalTheory.CompanionTheory.ZUnf.rowReduce_lowerC <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProduct
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem block_matrix_mul {m : ℕ} (a b c d a' b' c' d' : Matrix (Fin m) (Fin m) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_mul_blockMatrix (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockMatrix_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) K) (b b' : Matrix (Fin ρ) (Fin p) K)
    (c c' : Matrix (Fin p) (Fin ρ) K) (d d' : Matrix (Fin p) (Fin p) K) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem lowerRight_block_matrix {m : ℕ} (a b c d : Matrix (Fin m) (Fin m) K) :
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (blk4 a b c d) = d := by
  ext i j
  simp only [GlobalTheory.CompanionTheory.RatPtsUnn.blkD, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₂₂]

theorem lower_rows_word (σ : K →+* K) (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K)
    (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) :
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  simp only [wM, nM, sM, eM, rowC, rowD, block_matrix_mul, BigCell.lowerLeft_block, lowerRight_block_matrix, blockMatrix_mul_blockMatrix,
    blockMatrix_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, and_self]

theorem lower_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  intro K _ σ _ n ρ p hn a b c d ζ η
  exact lower_rows_word σ hn a b c d ζ η

end GlobalTheory.CompanionTheory.ZUnf.LowerRows
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsOfWeylHeisenbergProductStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_weyl_heisenberg_product : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d : Matrix (Fin p) (Fin p) K) (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K),
    lowerC (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowC hn η a c ∧
    GlobalTheory.CompanionTheory.RatPtsUnn.blkD (wM hn * nM hn ζ * sM hn σ η * eM hn a b c d) = rowD hn σ ζ η b d := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows | exact GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows | (intros; apply GlobalTheory.CompanionTheory.ZUnf.LowerRows.lower_rows <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylHeisenbergLeviRational
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylHeisenbergLeviRational
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.Rat

variable {D : D7} {n ρ p : ℕ}

theorem blockMatrix_map {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) :=
  _root_.UpperTheory.Reformulated.B.BlockFourMatrices.main f a b c d

theorem map_bl {R S : Type} (hn : ρ + p = n) (f : R → S) (a : Matrix (Fin ρ) (Fin ρ) R) (b : Matrix (Fin ρ) (Fin p) R)
    (c : Matrix (Fin p) (Fin ρ) R) (d : Matrix (Fin p) (Fin p) R) :
    (bl hn a b c d).map f = bl hn (a.map f) (b.map f) (c.map f) (d.map f) := by
  ext i j
  simp only [bl, Matrix.map_apply, Matrix.submatrix_apply]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm i = x
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp

theorem map_incA_zero {a b : Type} : (0 : Matrix a b D.host.E).map (incA D) = 0 := by
  ext i j; simp

theorem map_incA_one {m : ℕ} : (1 : Matrix (Fin m) (Fin m) D.host.E).map (incA D) = 1 :=
  map_one (incA D).mapMatrix

theorem map_incA_neg {a b : Type} (x : Matrix a b D.host.E) : (-x).map (incA D) = -(x.map (incA D)) := by
  ext i j; simp

theorem adj_map_incA {a b : ℕ} (x : Matrix (Fin a) (Fin b) D.host.E) :
    adj (x.map (incA D) : Mx D a b) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) x).map (incA D) := by
  ext i j
  simp only [adj, cT, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA]
  rfl

theorem adj_zero {a b : ℕ} : adj (0 : Mx D a b) = 0 := by
  ext i j
  simp [adj]

theorem mat_eq : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn) (z : hermA D ρ) (ζ : Matrix (Fin ρ) (Fin ρ) D.host.E), ζ.map (incA D) = z.1 →
    ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (γ : G D p) (a b c d : Matrix (Fin p) (Fin p) D.host.E), mat γ = (blk4 a b c d).map (incA D) →
    mat (M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb γ) =
      (wM hn * nM hn ζ * sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η * eM hn a b c d).map (incA D) := by
  intro D n ρ p hn M z ζ hζ η γ a b c d hγ
  have hm : ∀ x y : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E,
      (x * y).map (incA D) = x.map (incA D) * y.map (incA D) := fun x y => Matrix.map_mul
  rw [hm, hm, hm]
  have e1 : mat M.w = (wM hn).map (incA D) := by
    rw [M.w_mat, wM, blockMatrix_map]
    simp only [map_bl, map_incA_zero, map_incA_one, map_incA_neg]
  have e2 : mat (M.nzx z 0) = (nM hn ζ).map (incA D) := by
    rw [M.nzx_mat, nM, blockMatrix_map, adj_zero]
    simp only [map_bl, map_incA_zero, map_incA_one, hζ]
  have e3 : mat (M.sh (η.map (incA D))) = (sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η).map (incA D) := by
    rw [M.sh_mat, sM, blockMatrix_map, adj_map_incA]
    simp only [map_bl, map_incA_zero, map_incA_one, map_incA_neg]
  have e4 : mat (M.emb γ) = (eM hn a b c d).map (incA D) := by
    have h' := hγ
    rw [blockMatrix_map] at h'
    rw [M.emb_mat γ _ _ _ _ h', eM, blockMatrix_map]
    simp only [map_bl, map_incA_zero, map_incA_one]
  rw [← e1, ← e2, ← e3, ← e4]
  rfl

theorem rat_cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn) (z : hermA D ρ) (ζ : Matrix (Fin ρ) (Fin ρ) D.host.E), ζ.map (incA D) = z.1 →
    ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (γ : GF D p) (a b c d : Matrix (Fin p) (Fin p) D.host.E), mat (γ : G D p) = (blk4 a b c d).map (incA D) →
    M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p) ∈ GF D n ∧
    mat (M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p)) =
      (wM hn * nM hn ζ * sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η * eM hn a b c d).map (incA D) := by
  intro D n ρ p hn M z ζ hζ η γ a b c d hγ
  have h := mat_eq hn M z ζ hζ η γ.1 a b c d hγ
  refine ⟨(GlobalTheory.StdUnn.ChartRat.mem_GF_iff _).2 ⟨_, h.symm⟩, h⟩

end GlobalTheory.CompanionTheory.ZUnf.Rat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylHeisenbergLeviRationalStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_heisenberg_levi_rational : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn) (z : hermA D ρ) (ζ : Matrix (Fin ρ) (Fin ρ) D.host.E), ζ.map (incA D) = z.1 →
    ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (γ : GF D p) (a b c d : Matrix (Fin p) (Fin p) D.host.E), mat (γ : G D p) = (blk4 a b c d).map (incA D) →
    M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p) ∈ GF D n ∧
    mat (M.w * M.nzx z 0 * M.sh (η.map (incA D)) * M.emb (γ : G D p)) =
      (wM hn * nM hn ζ * sM hn (D.sp.cm.sig : D.host.E →+* D.host.E) η * eM hn a b c d).map (incA D) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.Rat.rat_cell | exact GlobalTheory.CompanionTheory.ZUnf.Rat.rat_cell | (intros; apply GlobalTheory.CompanionTheory.ZUnf.Rat.rat_cell <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransform
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransform
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.LowerRows

variable {R : Type} [CommRing R] {n ρ p : ℕ}

theorem lr_bl_mul (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem lr_bl_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn))
    (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem lr_exists_bl (hn : ρ + p = n) (T : Matrix (Fin n) (Fin n) R) :
    ∃ (T₁₁ : Matrix (Fin ρ) (Fin ρ) R) (T₁₂ : Matrix (Fin ρ) (Fin p) R)
      (T₂₁ : Matrix (Fin p) (Fin ρ) R) (T₂₂ : Matrix (Fin p) (Fin p) R),
      T = bl hn T₁₁ T₁₂ T₂₁ T₂₂ := by
  let M := T.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₁, M.toBlocks₂₂, ?_⟩
  simp only [bl, Matrix.fromBlocks_toBlocks, M, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem lr_eq_zero {m : ℕ} (a b c d : Matrix (Fin p) (Fin p) R) (hy : IsUnit (blk4 a b c d).det)
    (X : Matrix (Fin m) (Fin p) R) (hc : X * c = 0) (hd : X * d = 0) : X = 0 := by
  have hF : IsUnit (Matrix.fromBlocks a b c d).det := by
    have h := hy
    simp only [blk4] at h
    rwa [Matrix.det_submatrix_equiv_self] at h
  have hRF : Matrix.fromCols (0 : Matrix (Fin m) (Fin p) R) X * Matrix.fromBlocks a b c d = 0 := by
    ext i (j | j)
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type] using congrFun (congrFun hc i) j
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type] using congrFun (congrFun hd i) j
  have hR : Matrix.fromCols (0 : Matrix (Fin m) (Fin p) R) X = 0 := by
    have h := congrArg (· * (Matrix.fromBlocks a b c d)⁻¹) hRF
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF] using h
  ext i j
  simpa using congrFun (congrFun hR i) (Sum.inr j)

end GlobalTheory.CompanionTheory.ZUnf.LowerRows

namespace GlobalTheory.CompanionTheory.ZUnf


open GlobalTheory.CompanionTheory.ZUnf.LowerRows in
theorem lowerRows_determine : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ : Matrix (Fin p) (Fin p) K) (ζ ζ₂ : Matrix (Fin ρ) (Fin ρ) K)
      (η η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
    rowC hn η₂ a₂ c₂ = T * rowC hn η a c → rowD hn σ ζ₂ η₂ b₂ d₂ = T * rowD hn σ ζ η b d →
    (∃ T' : Matrix (Fin p) (Fin p) K, c₂ = T' * c ∧ d₂ = T' * d) ∧
    (IsUnit (blk4 a b c d).det → a₂ = a → b₂ = b → c₂ = c → d₂ = d → ζ₂ = ζ ∧ η₂ = η) := by
  intro K _ σ _ n ρ p hn a b c d a₂ b₂ c₂ d₂ ζ ζ₂ η η₂ T h₁ h₂
  obtain ⟨T₁₁, T₁₂, T₂₁, T₂₂, rfl⟩ := lr_exists_bl hn T
  simp only [rowC, rowD, lr_bl_mul] at h₁ h₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := lr_bl_inj hn h₁
  obtain ⟨f₁, f₂, f₃, f₄⟩ := lr_bl_inj hn h₂
  have hT₁₁ : T₁₁ = 1 := by
    simpa using e₁.symm
  have hT₂₁ : T₂₁ = 0 := by
    simpa using e₃.symm
  subst hT₁₁ hT₂₁
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_neg, zero_add, add_zero,
    neg_zero] at e₂ e₄ f₁ f₂ f₃ f₄
  refine ⟨⟨T₂₂, e₄, f₄⟩, ?_⟩
  intro hy ha hb hc hd
  subst ha hb hc hd
  have hT₂₂ : T₂₂ = 1 := by
    have h0 : T₂₂ - 1 = 0 := by
      refine lr_eq_zero a₂ b₂ c₂ d₂ hy (T₂₂ - 1) ?_ ?_
      · rw [Matrix.sub_mul, Matrix.one_mul, ← e₄, sub_self]
      · rw [Matrix.sub_mul, Matrix.one_mul, ← f₄, sub_self]
    exact sub_eq_zero.1 h0
  subst hT₂₂
  have hη : η₂ = η := by
    have h := neg_injective (by simpa using f₃ : -cT σ η₂ = -cT σ η)
    ext i j
    have := congrFun (congrFun h j) i
    exact σ.injective (by simpa [cT] using this)
  subst hη
  have hT₁₂ : T₁₂ = 0 := by
    refine lr_eq_zero a₂ b₂ c₂ d₂ hy T₁₂ ?_ ?_
    · simpa using e₂
    · simpa using f₂
  subst hT₁₂
  refine ⟨?_, rfl⟩
  simpa using f₁

end GlobalTheory.CompanionTheory.ZUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransformStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_proportional_of_transform : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ : Matrix (Fin p) (Fin p) K) (ζ ζ₂ : Matrix (Fin ρ) (Fin ρ) K)
      (η η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
    rowC hn η₂ a₂ c₂ = T * rowC hn η a c → rowD hn σ ζ₂ η₂ b₂ d₂ = T * rowD hn σ ζ η b d →
    (∃ T' : Matrix (Fin p) (Fin p) K, c₂ = T' * c ∧ d₂ = T' * d) ∧
    (IsUnit (blk4 a b c d).det → a₂ = a → b₂ = b → c₂ = c → d₂ = d → ζ₂ = ζ ∧ η₂ = η) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine | exact GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine | (intros; apply GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRational
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.CellGlue

section Field

variable {K : Type} [Field K] {n ρ p : ℕ}

theorem zinc_eq_comp (hn : ρ + p = n) (v : Fin ρ → K) :
    zinc hn v = Sum.elim v (fun _ : Fin p => (0 : K)) ∘ (finSumFinEquiv.trans (finCongr hn)).symm := rfl

theorem bl_mulVec_zinc (hn : ρ + p = n) (X : Matrix (Fin ρ) (Fin p) K) (c : Matrix (Fin p) (Fin p) K) (v : Fin ρ → K) :
    (bl hn (-1) X 0 c).mulVec (zinc hn v) = - zinc hn v := by
  rw [zinc_eq_comp]
  unfold bl
  rw [Matrix.submatrix_mulVec_equiv]
  funext i
  simp only [Function.comp_apply, Pi.neg_apply, Equiv.symm_symm]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm i = j
  have e : (Sum.elim v (fun _ : Fin p => (0 : K)) ∘ ⇑(finSumFinEquiv.trans (finCongr hn)).symm) ∘
      ⇑(finSumFinEquiv.trans (finCongr hn)) = Sum.elim v (fun _ : Fin p => (0 : K)) := by
    funext t
    simp
  rw [e, Matrix.fromBlocks_mulVec]
  rcases j with j | j
  · simp [Function.comp_def, Matrix.neg_mulVec]
    exact congrFun (Matrix.mulVec_zero X) j
  · simp [Function.comp_def]
    exact congrFun (Matrix.mulVec_zero c) j

theorem zinc_eq_zero (hn : ρ + p = n) {v : Fin ρ → K} (h : zinc hn v = 0) : v = 0 := by
  funext j
  have := congrFun h (finSumFinEquiv.trans (finCongr hn) (Sum.inl j))
  rw [zinc_eq_comp] at this
  simpa using this

theorem ker_rows_eq_bot (hn : ρ + p = n) {T : Matrix (Fin n) (Fin n) K} (hT : IsUnit T.det)
    (η : Matrix (Fin ρ) (Fin p) K) (a c : Matrix (Fin p) (Fin p) K) :
    LinearMap.ker ((T * rowC hn η a c).mulVecLin ∘ₗ zinc hn) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have h0 : (T * rowC hn η a c).mulVec (zinc hn v) = 0 := hv
  rw [← Matrix.mulVec_mulVec] at h0
  have h1 : (rowC hn η a c).mulVec (zinc hn v) = 0 := by
    have := congrArg (T⁻¹).mulVec h0
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hT, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have h2 : (rowC hn η a c).mulVec (zinc hn v) = - zinc hn v := bl_mulVec_zinc hn _ _ _
  rw [h2, neg_eq_zero] at h1
  exact zinc_eq_zero hn h1

theorem exists_unit_lowerC {x r : Matrix (Fin (n + n)) (Fin (n + n)) K} (hx : IsUnit x.det) (hr : IsUnit r.det)
    (hS : IsSiegelP (x * r⁻¹)) : ∃ T : Matrix (Fin n) (Fin n) K, IsUnit T.det ∧ lowerC x = T * lowerC r := by
  set S := x * r⁻¹ with hSd
  have hSr : S * r = x := by rw [hSd, mul_assoc, Matrix.nonsing_inv_mul _ hr, mul_one]
  have hdet : IsUnit S.det := by
    rw [hSd, Matrix.det_mul]
    exact hx.mul (Matrix.isUnit_nonsing_inv_det _ hr)
  have hd : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD S).det := by
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero S hS] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  refine ⟨_, hd, ?_⟩
  rw [← hSr]
  exact GlobalTheory.CompanionTheory.SwUnf.lowerC_siegel_mul hS r

theorem isUnitary_mul_inv (σ : K →+* K) {m : ℕ} {J y z : Matrix (Fin m) (Fin m) K} (hz : IsUnit z.det)
    (hy : IsUnitary σ J y) (h2 : IsUnitary σ J z) : IsUnitary σ J (y * z⁻¹) := by
  have hy' : cT σ y * J * y = J := hy
  have hz' : cT σ z * J * z = J := h2
  change cT σ (y * z⁻¹) * J * (y * z⁻¹) = J
  have e1 : cT σ z⁻¹ * cT σ z = 1 := by
    rw [← GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq, Matrix.mul_nonsing_inv _ hz, GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_one_sq]
  have e2 : z * z⁻¹ = 1 := Matrix.mul_nonsing_inv _ hz
  rw [GlobalTheory.CompanionTheory.SwUnf.BigCell.cT_mul_sq]
  calc cT σ z⁻¹ * cT σ y * J * (y * z⁻¹) = cT σ z⁻¹ * (cT σ y * J * y) * z⁻¹ := by simp only [mul_assoc]
    _ = cT σ z⁻¹ * (cT σ z * J * z) * z⁻¹ := by rw [hy', hz']
    _ = (cT σ z⁻¹ * cT σ z) * J * (z * z⁻¹) := by simp only [mul_assoc]
    _ = J := by rw [e1, e2, one_mul, mul_one]

end Field


open GlobalTheory.CompanionTheory.EisCellsAsm in
theorem cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧
      (∀ q, zKer hn (ratOf q.out) = ⊥ ↔ q ∈ Set.range e) ∧
      (∀ (l l' : ratHerm D ρ) u (h : M.nzx l'.1 0 ∈ GF D n),
        rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (e (l, u)) = e (l' + l, u)) ∧
      ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D ρ) u (y : G D n),
        term (P D n) (GF D n) f y (e (l, u)) =
          f (M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * y) := by
  intro D n ρ p hn M
  have hσ : ∀ x, sg D (sg D x) = x := sg_sg D
  obtain ⟨hadd, hsh, hemb, hc⟩ := GlobalTheory.T.heisenberg_centre_rational_form M
  choose hnm ζ hζ hζm using hc
  choose a b hab using fun q : Cosets (P D p) (GF D p) =>
    GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq (ratOf (Quotient.out q))
  let cc : Cosets (P D p) (GF D p) → Matrix (Fin p) (Fin p) D.host.E := fun q => lowerC (ratOf (Quotient.out q))
  let dd : Cosets (P D p) (GF D p) → Matrix (Fin p) (Fin p) D.host.E :=
    fun q => GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (Quotient.out q))
  have hab' : ∀ q, ratOf (Quotient.out q) = blk4 (a q) (b q) (cc q) (dd q) := hab
  have hmat : ∀ q, mat ((Quotient.out q : GF D p) : G D p) = (blk4 (a q) (b q) (cc q) (dd q)).map (incA D) := fun q => by
    rw [← hab']
    exact mat_ratOf _
  have hI := fun (l : ratHerm D ρ) (u : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) =>
    GlobalTheory.T.weyl_heisenberg_levi_rational hn M l.1 (ζ l) (hζ l) u.2 (Quotient.out u.1) (a u.1) (b u.1) (cc u.1) (dd u.1) (hmat u.1)
  let R : ratHerm D ρ → Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E →
      Matrix (Fin (n + n)) (Fin (n + n)) D.host.E :=
    fun l u => wM hn * nM hn (ζ l) * sM hn (sg D) u.2 * eM hn (a u.1) (b u.1) (cc u.1) (dd u.1)
  let c : ratHerm D ρ → Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → GF D n :=
    fun l u => ⟨M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p), (hI l u).1⟩
  have hcm : ∀ l u, mat (c l u : G D n) = (R l u).map (incA D) := fun l u => (hI l u).2
  have hRs : ∀ l u, IsUnit (R l u).det ∧ IsUnitary (sg D) (blk4 0 1 (-1) 0) (R l u) := fun l u => by
    have e : ratOf (c l u) = R l u := Matrix.map_injective incA_injective ((mat_ratOf _).symm.trans (hcm l u))
    rw [← e]
    exact GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec _
  have hRC : ∀ l u, lowerC (R l u) = rowC hn u.2 (a u.1) (cc u.1) := fun l u =>
    (GlobalTheory.T.rows_of_weyl_heisenberg_product (sg D) hσ hn _ _ _ _ _ _).1
  have hRD : ∀ l u, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (R l u) = rowD hn (sg D) (ζ l) u.2 (b u.1) (dd u.1) := fun l u =>
    (GlobalTheory.T.rows_of_weyl_heisenberg_product (sg D) hσ hn _ _ _ _ _ _).2
  refine ⟨fun x => mk ((P D n).subgroupOf (GF D n)) (c x.1 x.2), ?_, ?_, ?_, ?_⟩
  · rintro ⟨l₁, q₁, η₁⟩ ⟨l₂, q₂, η₂⟩ h
    have hS := (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l₁ (q₁, η₁)) (c l₂ (q₂, η₂)) (hRs l₁ _).1
      (hcm l₁ _) (hcm l₂ _)).1 h
    obtain ⟨T, hT1, hT2⟩ := (GlobalTheory.T.siegel_parabolic_quotient_iff_rows (sg D) hσ (R l₂ (q₂, η₂)) (R l₁ (q₁, η₁)) (hRs l₁ _).1 (hRs l₂ _).2
      (hRs l₁ _).2).1 hS
    rw [hRC, hRC] at hT1
    rw [hRD, hRD] at hT2
    obtain ⟨⟨T', h1, h2⟩, h3⟩ := GlobalTheory.T.rows_proportional_of_transform (sg D) hσ hn (a q₁) (b q₁) (cc q₁) (dd q₁) (a q₂) (b q₂) (cc q₂) (dd q₂)
      (ζ l₁) (ζ l₂) η₁ η₂ T hT1 hT2
    have hq : q₁ = q₂ := by
      have hs1 := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q₁)
      have hs2 := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q₂)
      have hSp := (GlobalTheory.T.siegel_parabolic_quotient_iff_rows (sg D) hσ (ratOf (Quotient.out q₂)) (ratOf (Quotient.out q₁)) hs1.1 hs2.2 hs1.2).2
        ⟨T', h1, h2⟩
      have := (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (Quotient.out q₁) (Quotient.out q₂) hs1.1
        (mat_ratOf _) (mat_ratOf _)).2 hSp
      exact (Quotient.out_eq q₁).symm.trans (this.trans (Quotient.out_eq q₂))
    subst hq
    have hU : IsUnit (blk4 (a q₁) (b q₁) (cc q₁) (dd q₁)).det := by
      rw [← hab']
      exact (GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec _).1
    obtain ⟨e1, e2⟩ := h3 hU rfl rfl rfl rfl
    have hl : l₁ = l₂ := Subtype.ext (Subtype.ext (by rw [← hζ l₁, ← hζ l₂, e1]))
    rw [hl, e2]
  · intro q
    have hspec := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q)
    constructor
    · intro hz
      have hker : LinearMap.ker ((lowerC (ratOf (Quotient.out q))).mulVecLin ∘ₗ zinc hn) = ⊥ := by
        rw [LinearMap.ker_comp]
        exact hz
      obtain ⟨T₀, a₁, b₁, Z, a₂, b₂, X, Y, a₃, b₃, W, a₄, b₄, c', d', hU, hD, hL1, hL2⟩ :=
        GlobalTheory.T.unitary_cell_block_normal_form (sg D) hσ hn _ hspec.1 hspec.2 hker
      obtain ⟨ζ₀, η₀, T, hyD, hyU, hζ₀, hr1, hr2⟩ :=
        GlobalTheory.T.unitary_block_invertible_criterion (sg D) hσ hn a₁ b₁ Z a₂ b₂ X Y a₃ b₃ W a₄ b₄ c' d' hU hD
      generalize a₄ + a₃ * X = a' at hyD hyU hr1
      generalize b₄ + a₃ * Y = b' at hyD hyU hr2
      obtain ⟨γ, hγ, hγm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause2 _ hyD hyU
      let q' : Cosets (P D p) (GF D p) := mk ((P D p).subgroupOf (GF D p)) ⟨γ, hγ⟩
      have hs2 := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out q')
      have hSy : IsSiegelP (blk4 a' b' c' d' * (ratOf (Quotient.out q'))⁻¹) :=
        (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (Quotient.out q') ⟨γ, hγ⟩ hs2.1 (mat_ratOf _) hγm).1
          (Quotient.out_eq q')
      have hsU := isUnitary_mul_inv (sg D) hs2.1 hyU hs2.2
      obtain ⟨A, B, hsb⟩ := GlobalTheory.CompanionTheory.SwUnf.BigCell.exists_blockMatrixTwoByTwoFin_eq (blk4 a' b' c' d' * (ratOf (Quotient.out q'))⁻¹)
      rw [(GlobalTheory.CompanionTheory.SwUnf.BigCell.isSiegelParabolic_iff _).1 hSy] at hsb
      generalize GlobalTheory.CompanionTheory.RatPtsUnn.blkD (blk4 a' b' c' d' * (ratOf (Quotient.out q'))⁻¹) = Dd at hsb
      rw [hsb] at hsU
      have hy : blk4 a' b' c' d' = blk4 A B 0 Dd * blk4 (a q') (b q') (cc q') (dd q') := by
        rw [← hsb, ← hab', mul_assoc, Matrix.nonsing_inv_mul _ hs2.1, mul_one]
      obtain ⟨ζ₂, η₂, T₂, hζ₂, hC, hDd⟩ := GlobalTheory.T.parabolic_factorization_rows (sg D) hσ hn a' b' c' d' (a q') (b q') (cc q') (dd q') A B Dd
        hsU hy ζ₀ η₀ hζ₀
      let bq : HermQ D ρ := ⟨ζ₂, fun i j => congrFun (congrFun hζ₂ i) j⟩
      let l₂ : ratHerm D ρ := ⟨⟨ζ₂.map (incA D), adj_map_herm bq⟩, ⟨ζ₂, rfl⟩⟩
      have hl : ζ l₂ = ζ₂ := Matrix.map_injective incA_injective (hζ l₂)
      refine ⟨(l₂, (q', η₂)), ?_⟩
      have hsp : IsSiegelP (ratOf (Quotient.out q) * (R l₂ (q', η₂))⁻¹) :=
        (GlobalTheory.T.siegel_parabolic_quotient_iff_rows (sg D) hσ _ _ (hRs l₂ _).1 hspec.2 (hRs l₂ _).2).2 ⟨T₀ * T * T₂, by
          rw [hRC, hL1, hr1, hC]
          simp only [mul_assoc], by
          rw [hRD, hL2, hr2, hDd, hl]
          simp only [mul_assoc]⟩
      exact ((mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l₂ (q', η₂)) (Quotient.out q) (hRs l₂ _).1 (hcm l₂ _)
        (mat_ratOf _)).2 hsp).trans (Quotient.out_eq q)
    · rintro ⟨⟨l, u⟩, rfl⟩
      have hspec' := GlobalTheory.CompanionTheory.SwUnf.BigCell.ratOf_spec (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l u)))
      have hS := (mk_eq_iff_siegel GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn (c l u) (Quotient.out (mk ((P D n).subgroupOf (GF D n)) (c l u)))
        (hRs l u).1 (hcm l u) (mat_ratOf _)).1 (Quotient.out_eq _).symm
      obtain ⟨T, hT, hTC⟩ := exists_unit_lowerC hspec'.1 (hRs l u).1 hS
      rw [hRC] at hTC
      have h := ker_rows_eq_bot hn hT u.2 (a u.1) (cc u.1)
      rw [← hTC, LinearMap.ker_comp] at h
      exact h
  · intro l l' u h
    change rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (mk ((P D n).subgroupOf (GF D n)) (c l u)) =
      mk ((P D n).subgroupOf (GF D n)) (c (l' + l) u)
    have e : c (l' + l) u = c l u * ⟨M.nzx l'.1 0, h⟩ := by
      apply Subtype.ext
      change M.w * M.nzx (l' + l).1 0 * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p) =
        M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p) * M.nzx l'.1 0
      have e1 : ((l' + l : ratHerm D ρ) : hermA D ρ) = l.1 + l'.1 := Subtype.ext (add_comm l'.1.1 l.1.1)
      have h1 := hemb l'.1 (Quotient.out u.1 : GF D p).1
      have h2 := hsh l'.1 (u.2.map (incA D))
      rw [e1, hadd]
      calc M.w * (M.nzx l.1 0 * M.nzx l'.1 0) * M.sh (u.2.map (incA D)) * M.emb (Quotient.out u.1 : GF D p)
          = M.w * M.nzx l.1 0 * (M.nzx l'.1 0 * M.sh (u.2.map (incA D))) * M.emb (Quotient.out u.1 : GF D p) := by
            simp only [mul_assoc]
        _ = M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * (M.nzx l'.1 0 * M.emb (Quotient.out u.1 : GF D p)) := by
            rw [h2]
            simp only [mul_assoc]
        _ = _ := by
            rw [h1]
            simp only [mul_assoc]
    rw [e]
    exact rmul_mk _ _
  · intro f hf l u y
    exact term_mk hf y (c l u)

end GlobalTheory.CompanionTheory.ZUnf.CellGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRationalStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_cosets_param_rational : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (M : Maps D hn),
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧
      (∀ q, zKer hn (ratOf q.out) = ⊥ ↔ q ∈ Set.range e) ∧
      (∀ (l l' : ratHerm D ρ) u (h : M.nzx l'.1 0 ∈ GF D n),
        rmulEquiv (P D n) (GF D n) ⟨M.nzx l'.1 0, h⟩ (e (l, u)) = e (l' + l, u)) ∧
      ∀ f : G D n → ℂ, LeftInv (P D n ⊓ GF D n) f → ∀ (l : ratHerm D ρ) u (y : G D n),
        term (P D n) (GF D n) f y (e (l, u)) =
          f (M.w * M.nzx l.1 0 * M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * y) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | exact GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell | (intros; apply GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell <;> assumption)
end
end
