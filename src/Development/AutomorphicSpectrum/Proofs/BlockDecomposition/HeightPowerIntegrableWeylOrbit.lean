module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlock
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlock
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HtPull

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_one)
open GlobalTheory.StdUnn.Model

def leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) : GL (Fin n) R :=
  ⟨bl hn a.1 0 0 1, bl hn (a⁻¹).1 0 0 1,
    by rw [blockMatrix_multiply]; simp [blockMatrix_one], by rw [blockMatrix_multiply]; simp [blockMatrix_one]⟩

theorem det_leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) :
    Matrix.GeneralLinearGroup.det (leviBl hn a) = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, leviBl, bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMatrix_zero {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero, Matrix.submatrix_zero, Pi.zero_apply]

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem isHt_blockPull : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  intro D n ρ p hn ι hc hblk H hH
  refine ⟨hH.1.comp hc, fun g => hH.2.1 _, ?_⟩
  intro q hq a ha g
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  rw [ha] at hm
  have hι := hblk q a.1 b 0 d hm
  rw [blockMatrix_zero] at hι
  have hqP : ι q ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hι
  have hA : blkA (mat (ι q)) = (leviBl hn a).1 := by
    rw [hι, blkA_blk4]
    rfl
  show H (ι (q * g)) = _ * H (ι g)
  rw [map_mul, hH.2.2 _ hqP (leviBl hn a) hA, det_leviBl]

end GlobalTheory.CompanionTheory.HtPull

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlockStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_pullback_first_block : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  first | exact @GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | exact GlobalTheory.CompanionTheory.HtPull.isHt_blockPull | (intros; apply GlobalTheory.CompanionTheory.HtPull.isHt_blockPull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitian
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitian
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HermSum

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul block_matrix_one)

theorem mat_mul_block_decomposition {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem weyl_mul_inv {R : Type} [CommRing R] {k : ℕ} :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 0 (-1) 1 0 = 1 := by
  rw [submatrix_fromBlocks_mul]
  simp [block_matrix_one]

theorem weyl_conj {R : Type} [CommRing R] {k : ℕ} (d : Matrix (Fin k) (Fin k) R) :
    blk4 (0 : Matrix (Fin k) (Fin k) R) 1 (-1) 0 * blk4 1 d 0 1 * blk4 0 (-1) 1 0 = blk4 1 0 (-d) 1 := by
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp

private theorem mat_one_eq_one {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [GlobalTheory.StdUnn.mat, map_one, Units.val_one]

private theorem mat_inv_eq_of_mat_mul_eq_one {D : D7} {n : ℕ} (g : G D n) (M : Mx D (n + n) (n + n))
    (h : mat g * M = 1) : mat g⁻¹ = M := by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← mat_mul_block_decomposition, inv_mul_cancel, mat_one_eq_one]
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, mul_one]
    _ = M := by rw [← mul_assoc, h1, one_mul]

private theorem blk4_apply_inr_inl {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  show (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

private theorem mulVec_single_one_apply' {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (i j : Fin m) : (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec]

private theorem eq_zero_of_mem_P_of_mat_eq_blk4 {D : D7} {n : ℕ} (x : G D n) (hx : x ∈ P D n)
    (d : Mx D n n) (hd : mat x = blk4 1 0 (-d) 1) : d = 0 := by
  have key : ∀ v : Fin (n + n) → AE D,
      v ∈ GlobalTheory.StdUnn.upperHalf D n ↔ (mat x).mulVec v ∈ GlobalTheory.StdUnn.upperHalf D n := hx
  refine Matrix.ext fun i j => ?_
  have hv : (Pi.single (finSumFinEquiv (Sum.inl j)) 1 : Fin (n + n) → AE D) ∈
      GlobalTheory.StdUnn.upperHalf D n := by
    rw [GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker]
    ext l
    rw [LinearMap.funLeft_apply, Pi.zero_apply, Pi.single_eq_of_ne]
    exact fun h => Sum.inr_ne_inl (finSumFinEquiv.injective h)
  have h2 := (key _).1 hv
  rw [hd, GlobalTheory.StdUnn.upperHalf, LinearMap.mem_ker] at h2
  have h3 := congrFun h2 i
  rw [LinearMap.funLeft_apply, Pi.zero_apply, mulVec_single_one_apply', blk4_apply_inr_inl, Matrix.neg_apply,
    neg_eq_zero] at h3
  rw [h3, Matrix.zero_apply]

theorem summable_height_rpow : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  intro D ρ H hH w nb hw hnb τ hτ
  have hτ0 : 0 ≤ τ := le_trans (Nat.cast_nonneg ρ) hτ.le
  set Φ : G D ρ → ℂ := fun g => (((H g : ℝ) ^ τ : ℝ) : ℂ) with hΦ
  set s₁ : ℂ := ((τ - (ρ : ℝ) / 2 : ℝ) : ℂ) with hs₁
  have hlaw : PositivityTheory.Rg.Rsw.IsLaw 1 s₁ Φ := by
    intro q hq a ha g
    have e1 := hH.2.2 q hq a ha g
    have e2 : s₁ + (ρ : ℂ) / 2 = (τ : ℂ) := by
      rw [hs₁]
      push_cast
      ring
    rw [e2]
    simp only [hΦ, e1, MonoidHom.one_apply, OneMemClass.coe_one, NNReal.coe_mul, GlobalTheory.Doubling.npow]
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), Complex.ofReal_mul,
      ← Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    simp
  have hcont : Continuous Φ := by
    have hH' : Continuous fun g => (H g : ℝ) := NNReal.continuous_coe.comp hH.1
    exact Complex.continuous_ofReal.comp (hH'.rpow_const fun _ => Or.inr hτ0)
  have hre : (ρ : ℝ) / 2 < s₁.re := by
    rw [hs₁, Complex.ofReal_re]
    linarith
  have hconv := GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law D ρ 1 s₁ Φ hcont hlaw hre 1
  have hHecke : Formalism.L2.Theta.IsHeckeChar D 1 :=
    ⟨by
      have h1 : (⇑(1 : (AE D)ˣ →* Circle)) = fun _ => 1 := funext fun _ => MonoidHom.one_apply _
      rw [h1]
      exact continuous_const, fun _ => MonoidHom.one_apply _⟩
  have hinv := GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw (1 : (AE D)ˣ →* Circle) s₁ Φ hHecke hlaw
  have hWr : mat w = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) 1 (-1) 0) := by
    rw [hw, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_neg',
      GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwinv : mat w⁻¹ = blk4 0 (-1) 1 0 := by
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hw]
    exact weyl_mul_inv
  have hWr' : mat w⁻¹ = GlobalTheory.MixModel.rat (blk4 (0 : Matrix (Fin ρ) (Fin ρ) D.host.E) (-1) 1 0) := by
    rw [hwinv, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_zero', GlobalTheory.CompanionTheory.PcB.rat_neg', GlobalTheory.CompanionTheory.PcB.rat_one']
  have hwmem : w ∈ GF D ρ := GlobalTheory.CompanionTheory.PcB.mem_GF w _ _ hWr hWr'
  have hrat : ∀ ζ : ratHerm D ρ, ∃ Z : Matrix (Fin ρ) (Fin ρ) D.host.E,
      GlobalTheory.MixModel.rat Z = ((ζ.1 : hermA D ρ) : Mx D ρ ρ) := by
    intro ζ
    obtain ⟨Z, hZ⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp ζ.2)
    exact ⟨Z, hZ⟩
  have hnbinv : ∀ ζ : ratHerm D ρ, mat (nb ζ.1)⁻¹ = blk4 1 (-((ζ.1 : hermA D ρ) : Mx D ρ ρ)) 0 1 := by
    intro ζ
    apply mat_inv_eq_of_mat_mul_eq_one
    rw [hnb, GlobalTheory.CompanionTheory.PcB.block_unipotent_mul, add_neg_cancel, block_matrix_one]
  have hnbmem : ∀ ζ : ratHerm D ρ, nb ζ.1 ∈ GF D ρ := by
    intro ζ
    obtain ⟨Z, hZ⟩ := hrat ζ
    refine GlobalTheory.CompanionTheory.PcB.mem_GF _ (blk4 1 Z 0 1) (blk4 1 (-Z) 0 1) ?_ ?_
    · rw [hnb, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero']
    · rw [hnbinv, ← hZ, GlobalTheory.CompanionTheory.PcB.rational_map_block_matrix, GlobalTheory.CompanionTheory.PcB.rat_one', GlobalTheory.CompanionTheory.PcB.rat_zero',
        GlobalTheory.CompanionTheory.PcB.rat_neg']
  set x : ratHerm D ρ → GF D ρ := fun ζ => ⟨w * nb ζ.1, mul_mem hwmem (hnbmem ζ)⟩ with hx
  set ι : ratHerm D ρ → GlobalTheory.Eis.Cosets (P D ρ) (GF D ρ) :=
    fun ζ => Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) with hι
  have hinj : Function.Injective ι := by
    intro ζ ζ' h
    have h0 : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ') := h
    have h1 : x ζ' * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
    have h2 : (w * nb ζ'.1) * (w * nb ζ.1)⁻¹ ∈ P D ρ := Subgroup.mem_subgroupOf.mp h1
    have hm : mat ((w * nb ζ'.1) * (w * nb ζ.1)⁻¹) =
        blk4 1 0 (-(((ζ'.1 : hermA D ρ) : Mx D ρ ρ) + -((ζ.1 : hermA D ρ) : Mx D ρ ρ))) 1 := by
      rw [mul_inv_rev, mat_mul_block_decomposition, mat_mul_block_decomposition, mat_mul_block_decomposition, hw, hnb, hwinv, hnbinv ζ, ← mul_assoc,
        mul_assoc (blk4 0 1 (-1) 0), GlobalTheory.CompanionTheory.PcB.block_unipotent_mul]
      exact weyl_conj _
    have h3 := eq_zero_of_mem_P_of_mat_eq_blk4 _ h2 _ hm
    exact Subtype.ext (Subtype.ext (add_neg_eq_zero.mp h3).symm)
  have hterm : ∀ ζ : ratHerm D ρ,
      ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 (ι ζ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ := by
    intro ζ
    have ho : Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (Quotient.out (ι ζ)) =
        Quotient.mk (QuotientGroup.rightRel ((P D ρ).subgroupOf (GF D ρ))) (x ζ) := Quotient.out_eq (ι ζ)
    have hrel : x ζ * (Quotient.out (ι ζ))⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact ho)
    have hγ : Quotient.out (ι ζ) * (x ζ)⁻¹ ∈ (P D ρ).subgroupOf (GF D ρ) := by
      have h4 := inv_mem hrel
      rwa [mul_inv_rev, inv_inv] at h4
    have hγP : ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) ∈ P D ρ ⊓ GF D ρ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hγ, (Quotient.out (ι ζ) * (x ζ)⁻¹).2⟩
    have hsplit : ((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1 =
        ((Quotient.out (ι ζ) * (x ζ)⁻¹ : GF D ρ) : G D ρ) * ((x ζ : GF D ρ) : G D ρ) := by
      rw [mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right]
    show ‖Φ (((Quotient.out (ι ζ) : GF D ρ) : G D ρ) * 1)‖ = _
    rw [hsplit, hinv _ hγP]
    show ‖(((H (w * nb ζ.1) : ℝ) ^ τ : ℝ) : ℂ)‖ = (H (w * nb ζ.1) : ℝ) ^ τ
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  have hsum : Summable (fun q => ‖GlobalTheory.Eis.term (P D ρ) (GF D ρ) Φ 1 q‖) := hconv
  exact (hsum.comp_injective hinj).congr hterm

end GlobalTheory.CompanionTheory.HermSum

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerSummableRationalHermitianStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_power_summable_rational_hermitian : ∀ (D : D7) (ρ : ℕ) (H : G D ρ → ℝ≥0), IsHt H → ∀ (w : G D ρ) (nb : hermA D ρ → G D ρ),
  mat w = blk4 0 1 (-1) 0 → (∀ z : hermA D ρ, mat (nb z) = blk4 1 z.1 0 1) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Summable (fun ζ : ratHerm D ρ => (H (w * nb ζ.1) : ℝ) ^ τ) := by
  first | exact @GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | exact GlobalTheory.CompanionTheory.HermSum.summable_height_rpow | (intros; apply GlobalTheory.CompanionTheory.HermSum.summable_height_rpow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbedding
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

open GlobalTheory.StdUnn.Model
open GlobalTheory.CompanionTheory.JacobiMaps (b11 b12 b21 b22 block_matrix_of_blocks upperLeft_block upperRight_block lowerLeft_block_entry lowerRight_block continuous_block_matrix continuous_bl
  block_mul₂ bl_add block_sub blockRowSubstitution_one blockMatrix_zero blockMatrix_neg_one adj_bl adjoint_symplectic_block_product mkG isU_mat)

variable {D : D7} {n ρ p : ℕ}

def firstM (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ)) : Mx D (n + n) (n + n) :=
  blk4 (bl hn (b11 M) 0 0 1) (bl hn (b12 M) 0 0 0) (bl hn (b21 M) 0 0 0) (bl hn (b22 M) 0 0 1)

theorem first_block_embedding_block (hn : ρ + p = n) (a b c d : Mx D ρ ρ) :
    firstM hn (blk4 a b c d) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  rw [firstM, upperLeft_block, upperRight_block, lowerLeft_block_entry, lowerRight_block]

def firstMon (hn : ρ + p = n) : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n) where
  toFun := firstM hn
  map_one' := by
    rw [← block_matrix_one (R := AE D) (n := ρ), first_block_embedding_block, blockRowSubstitution_one]
    have e : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
    rw [e, block_matrix_one]
  map_mul' M N := by
    rw [← block_matrix_of_blocks M, ← block_matrix_of_blocks N]
    generalize b11 M = a
    generalize b12 M = b
    generalize b21 M = c
    generalize b22 M = d
    generalize b11 N = a'
    generalize b12 N = b'
    generalize b21 N = c'
    generalize b22 N = d'
    rw [submatrix_fromBlocks_mul, first_block_embedding_block, first_block_embedding_block, first_block_embedding_block, submatrix_fromBlocks_mul]
    simp only [block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem firstM_isU (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ))
    (h : (adj M * blk4 0 1 (-1) 0 * M : Mx D (ρ + ρ) (ρ + ρ)) = blk4 0 1 (-1) 0) :
    (adj (firstM hn M) * blk4 0 1 (-1) 0 * firstM hn M : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  rw [← block_matrix_of_blocks M] at h ⊢
  generalize b11 M = a at h ⊢
  generalize b12 M = b at h ⊢
  generalize b21 M = c at h ⊢
  generalize b22 M = d at h ⊢
  rw [adjoint_symplectic_block_product] at h
  obtain ⟨e1, e2, e3, e4⟩ := blockMatrixTwoByTwoFin_injective h
  have z : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Mx D ρ ρ) 0 0 (1 : Mx D p p) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Mx D ρ ρ) 0 0 (-1 : Mx D p p) = -1 := blockMatrix_neg_one hn
  rw [first_block_embedding_block, adjoint_symplectic_block_product]
  simp only [adj_bl, adj_one, adj_zero, block_mul₂, block_sub, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self, e1, e2, e3, e4, z, o, m]

def firstF (hn : ρ + p = n) (g : G D ρ) : G D n :=
  mkG (Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g)) (firstM_isU hn _ (isU_mat g))

theorem matHom_firstF (hn : ρ + p = n) (g : G D ρ) :
    matHom _ D.sp.cm.sig (Jst D n) (firstF hn g) = Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) := rfl

def firstG (hn : ρ + p = n) : G D ρ →* G D n where
  toFun := firstF hn
  map_one' := matHom_injective _ D.sp.cm.sig (Jst D n) (by rw [matHom_firstF, map_one, map_one, map_one])
  map_mul' g h := matHom_injective _ D.sp.cm.sig (Jst D n) (by
    rw [map_mul, matHom_firstF, matHom_firstF, matHom_firstF, map_mul, map_mul])

theorem mat_firstG (hn : ρ + p = n) (h : G D ρ) : mat (firstG hn h) = firstM hn (mat h) := rfl

theorem continuous_firstM (hn : ρ + p = n) : Continuous (firstM (D := D) hn) :=
  continuous_block_matrix (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const
      continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)

theorem continuous_firstG (hn : ρ + p = n) : Continuous (firstG (D := D) hn) := by
  have h0 : Continuous (Units.map (firstMon (D := D) hn : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n))) :=
    Continuous.units_map _ (continuous_firstM hn)
  have h : Continuous fun g : G D ρ => Units.map (firstMon (D := D) hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) :=
    h0.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D ρ)).continuous
  exact (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff.2 h

end GlobalTheory.CompanionTheory.FirstBlockEmb

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

theorem exists_first_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  intro D n ρ p hn
  refine ⟨firstG hn, continuous_firstG hn, fun h a b c d e => ?_⟩
  exact (mat_firstG hn h).trans ((congrArg (firstM hn) e).trans (first_block_embedding_block hn a b c d))

end GlobalTheory.CompanionTheory.FirstBlockEmb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbeddingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_first_block_group_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  first | exact @GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb | exact GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb | (intros; apply GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomain
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomain
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermFD

theorem integrable_of_cover {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [MeasurableAdd A] [ContinuousAdd A] (L : AddSubgroup A) [Countable L]
    (μ : Measure A) [μ.IsAddLeftInvariant] (𝓖 : Set A) (hFD : IsAddFundamentalDomain L 𝓖 μ) (h1 : μ 𝓖 = 1)
    (f : A → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hS : Summable (fun ζ : L => f ζ.1))
    (K : Set A) (hK : ∀ x, ∃ γ ∈ L, γ + x ∈ K) (κ : ℝ) (hκ : 0 ≤ κ)
    (hb : ∀ ζ ∈ L, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) : Integrable f μ := by
  have hpt : ∀ z : A, ∑' ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hK z
    have h2 : ∀ ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤
        ENNReal.ofReal (κ * f ((Equiv.subRight (⟨γ, hγ⟩ : L) ζ).1)) := by
      intro ζ
      apply ENNReal.ofReal_le_ofReal
      have e : ζ.1 + z = (ζ.1 - γ) + (γ + z) := by simp [sub_eq_add_neg, add_assoc]
      rw [e]
      exact hb _ (L.sub_mem ζ.2 hγ) _ hz
    refine (ENNReal.tsum_le_tsum h2).trans ?_
    rw [(Equiv.subRight (⟨γ, hγ⟩ : L)).tsum_eq (fun ζ : L => ENNReal.ofReal (κ * f ζ.1)),
      ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun ζ => mul_nonneg hκ (hf0 _)) (hS.mul_left κ)]
  have hm : ∀ g : L, AEMeasurable (fun x : A => ENNReal.ofReal (f (g +ᵥ x))) (μ.restrict 𝓖) := fun g =>
    (ENNReal.measurable_ofReal.comp (hf.comp (continuous_const.add continuous_id)).measurable).aemeasurable
  have hI : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    rw [hFD.lintegral_eq_tsum'', ← lintegral_tsum hm]
    calc _ ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) ∂μ :=
          lintegral_mono fun x => hpt x
      _ = _ := by simp [h1]
  exact ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall hf0)).2 (hI.trans_lt ENNReal.ofReal_lt_top)⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_of_periodisation_bound : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  intro D ρ lz 𝓖 hC f hf hf0 hS K hK κ hκ hb
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := by
    haveI : SecondCountableTopology (ratHerm D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  exact integrable_of_cover (ratHerm D ρ) lz 𝓖 hFD h1 f hf hf0 hS K hK κ hκ hb

end GlobalTheory.CompanionTheory.HermFD
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomainStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_of_summable_fundamental_domain : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  first | exact @GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | exact GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound | (intros; apply GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbit
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermConv

theorem integrable_height_rpow : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (H : G D n → ℝ≥0), IsHt H →
  (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Integrable (fun ζ : hermA D ρ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) m.lz := by
  intro D n ρ p hn M m H hH hC τ hτ
  have hτ0 : 0 ≤ τ := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg ρ) hτ)
  have hadj0 : ∀ k l : ℕ, GlobalTheory.MixModel.adj (0 : Mx D k l) = 0 := by
    intro k l
    show ((0 : Mx D k l).map (cA D)).transpose = 0
    ext i j
    simp
  have hadj1 : GlobalTheory.MixModel.adj (1 : Mx D ρ ρ) = 1 := by
    show ((1 : Mx D ρ ρ).map (cA D)).transpose = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hadjn1 : GlobalTheory.MixModel.adj (-1 : Mx D ρ ρ) = -1 := by
    show ((-1 : Mx D ρ ρ).map (cA D)).transpose = -1
    rw [Matrix.map_neg _ (fun a => map_neg (cA D) a), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_neg, Matrix.transpose_one]
  have hone : GlobalTheory.StdUnn.blk4 (1 : Mx D ρ ρ) 0 0 1 = 1 := by
    show (Matrix.fromBlocks (1 : Mx D ρ ρ) 0 0 1).submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm = 1
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hJ1 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0 * GlobalTheory.StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  have hJ2 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) (-1) 1 0 * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  let u : GL (Fin (ρ + ρ)) (AE D) := ⟨GlobalTheory.StdUnn.blk4 0 1 (-1) 0, GlobalTheory.StdUnn.blk4 0 (-1) 1 0, hJ1, hJ2⟩
  have hu : GlobalTheory.MixModel.adj (u : Mx D (ρ + ρ) (ρ + ρ)) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * (u : Mx D (ρ + ρ) (ρ + ρ)) =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    show GlobalTheory.MixModel.adj (GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 *
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = GlobalTheory.StdUnn.blk4 0 1 (-1) 0
    rw [GlobalTheory.CompanionTheory.JacobiMaps.adjoint_symplectic_block_product, hadj0, hadj1, hadjn1]
    simp only [zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, neg_neg, mul_neg, neg_mul, sub_self, neg_zero]
  obtain ⟨ι, hιc, hιm⟩ := GlobalTheory.T.exists_first_block_group_embedding D n ρ p hn
  have hH' := GlobalTheory.T.height_pullback_first_block D n ρ p hn ι hιc hιm H hH
  let w' : G D ρ := GlobalTheory.CompanionTheory.JacobiMaps.mkG u hu
  have hw' : GlobalTheory.StdUnn.mat w' = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := GlobalTheory.CompanionTheory.JacobiMaps.mat_mkG u hu
  let nb : hermA D ρ → G D ρ := fun z => GlobalTheory.CompanionTheory.JacobiMaps.nAt (z : Mx D ρ ρ) z.2
  have hnb : ∀ z : hermA D ρ, GlobalTheory.StdUnn.mat (nb z) = GlobalTheory.StdUnn.blk4 1 (z : Mx D ρ ρ) 0 1 :=
    fun z => GlobalTheory.CompanionTheory.JacobiMaps.mat_nAt _ _
  have hS := GlobalTheory.T.height_power_summable_rational_hermitian D ρ (fun h => H (ι h)) hH' w' nb hw' hnb τ hτ
  have hιw : ι w' = M.w := by
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm w' 0 1 (-1) 0 hw', M.w_mat]
  have hιn : ∀ z : hermA D ρ, ι (nb z) = M.nzx z 0 := by
    intro z
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm (nb z) 1 (z : Mx D ρ ρ) 0 1 (hnb z), M.nzx_mat, hadj0, GlobalTheory.CompanionTheory.PcB.blockMatrix_one, GlobalTheory.CompanionTheory.JacobiMaps.blockMatrix_zero]
  have hf_eq : ∀ z : hermA D ρ, (H (M.w * M.nzx z 0) : ℝ) ^ τ = (H (ι (w' * nb z)) : ℝ) ^ τ := by
    intro z
    rw [map_mul, hιw, hιn]
  have hSum : Summable (fun ζ : ratHerm D ρ => (H (M.w * M.nzx (ζ : hermA D ρ) 0) : ℝ) ^ τ) := by
    simpa only [hf_eq] using hS
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := ρ)
  have hNc : Continuous fun z : hermA D ρ => M.nzx z 0 := GlobalTheory.CompanionTheory.PcB.continuous_nz M
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC
    ((fun z => M.nzx z 0) '' K) (hK.image hNc)
  refine GlobalTheory.T.integrable_of_summable_fundamental_domain D ρ m.lz m.𝓖 m.hz (fun ζ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) ?_ ?_ hSum K hKc (κ ^ τ)
    (Real.rpow_nonneg (by linarith) τ) ?_
  · exact (NNReal.continuous_coe.comp (hH.1.comp (continuous_const.mul hNc))).rpow_const fun _ => Or.inr hτ0
  · exact fun z => Real.rpow_nonneg (NNReal.coe_nonneg _) τ
  · intro ζ _ z hz
    have h1 : M.nzx (ζ + z) 0 = M.nzx ζ 0 * M.nzx z 0 := by
      rw [GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero]
    have h2 := hκ (M.nzx z 0) ⟨z, hz, rfl⟩ (M.w * M.nzx ζ 0)
    show (H (M.w * M.nzx (ζ + z) 0) : ℝ) ^ τ ≤ κ ^ τ * (H (M.w * M.nzx ζ 0) : ℝ) ^ τ
    rw [h1, ← mul_assoc, ← Real.mul_rpow (by linarith) (NNReal.coe_nonneg _)]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) h2 hτ0

end GlobalTheory.CompanionTheory.HermConv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbitStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_power_integrable_weyl_orbit : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (H : G D n → ℝ≥0), IsHt H →
  (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Integrable (fun ζ : hermA D ρ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) m.lz := by
  first | exact @GlobalTheory.CompanionTheory.HermConv.integrable_height_rpow | exact GlobalTheory.CompanionTheory.HermConv.integrable_height_rpow | (intros; apply GlobalTheory.CompanionTheory.HermConv.integrable_height_rpow <;> assumption)
end
