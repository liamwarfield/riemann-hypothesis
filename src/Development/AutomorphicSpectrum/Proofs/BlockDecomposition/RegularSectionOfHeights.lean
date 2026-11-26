module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzHeightMajorantIntegrable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftCommutesLeviEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftCommutesLeviEmbedding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn.Model

namespace GlobalTheory.CompanionTheory.PcB

open GlobalTheory.CompanionTheory.FourierN (mat_injective)

theorem blockMatrix_zero' {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl]
  rw [Matrix.fromBlocks_zero]
  rfl

theorem lowerUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 c 1) (bl hn 1 0 0 d) = bl hn 1 0 c d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_lowerUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (c : Matrix (Fin p) (Fin ρ) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 0 c 1) = bl hn 1 0 (HMul.hMul d c) d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem upperUnipotent_mul_blockDiagonal {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 y 0 1) (bl hn 1 0 0 d) = bl hn 1 (HMul.hMul y d) 0 d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockMatrix_diagonal_mul_upperUnipotent {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (y : Matrix (Fin ρ) (Fin p) R)
    (d : Matrix (Fin p) (Fin p) R) :
    HMul.hMul (bl hn 1 0 0 d) (bl hn 1 y 0 1) = bl hn 1 y 0 d := by
  simp only [bl, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem sh_emb_levi (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p)
    (a : GL (Fin p) (AE D)) (h : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (y : Mx D ρ p) :
    M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  have hinv : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj a.1 : Mx D p p) = (1 : Mx D p p) := by
    have h1 : HMul.hMul (a.1 : Mx D p p) ((a⁻¹).1 : Mx D p p) = (1 : Mx D p p) := by
      exact congrArg Units.val (mul_inv_cancel a)
    rw [← adj_mul, h1]
    exact adj_one
  have diag_mul (A A' B B' : Mx D n n) :
      blk4 A 0 0 A' * blk4 B 0 0 B' = blk4 (A * B) 0 0 (A' * B') := by
    rw [submatrix_fromBlocks_mul]
    congr 1 <;> simp
  apply mat_injective
  rw [mat_mul', mat_mul', M.sh_mat, M.sh_mat, M.emb_mat g₀ _ _ _ _ h, blockMatrix_zero', diag_mul, diag_mul]
  congr 1
  · rw [upperUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_upperUnipotent]
  · have hk : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (adj (HMul.hMul y a.1 : Mx D ρ p)) = adj y := by
      rw [adj_mul, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hk' : HMul.hMul (adj (a⁻¹).1 : Mx D p p) (-adj (HMul.hMul y a.1 : Mx D ρ p)) = -adj y := by
      rw [Matrix.mul_neg, hk]
    rw [lowerUnipotent_mul_blockDiagonal, blockMatrix_diagonal_mul_lowerUnipotent, hk']

end GlobalTheory.CompanionTheory.PcB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftCommutesLeviEmbeddingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_commutes_levi_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ y : Mx D ρ p, M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  first | exact @GlobalTheory.CompanionTheory.PcB.sh_emb_levi | exact GlobalTheory.CompanionTheory.PcB.sh_emb_levi | (intros; apply GlobalTheory.CompanionTheory.PcB.sh_emb_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnit
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CentreChar

theorem continuous_and_norm_chz : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := fun _ _ _ hψ b₀ =>
  ⟨GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀⟩

end GlobalTheory.CompanionTheory.CentreChar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnitStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_continuous_unit : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | exact GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz | (intros; apply GlobalTheory.CompanionTheory.CentreChar.continuous_and_norm_chz <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftUnipotentLeviCommutator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftUnipotentLeviCommutator
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.ThTw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ShEmbUnip


set_option maxHeartbeats 1000000 in
theorem sh_emb_unip : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
    ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
      z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  intro D n ρ p hn M g₁ b hg y
  have hb : adj b = b := (GlobalTheory.StdUnn.Model.exists_unip b).1 ⟨g₁, hg⟩
  have hE := M.emb_mat g₁ _ _ _ _ hg
  refine ⟨⟨HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y), ?_⟩, HMul.hMul y b, ?_, rfl⟩
  · show adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]
  · apply mat_injective'
    rw [mat_mul' (M.sh y), mat_mul' _ (M.sh y), mat_mul' (M.nzx _ _), M.sh_mat, M.nzx_mat, hE, blockMatrix_zero, blockRowSubstitution_one,
      submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add,
      adj_mul, hb, Matrix.mul_neg, add_neg_cancel]

end GlobalTheory.CompanionTheory.ShEmbUnip

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftUnipotentLeviCommutatorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_unipotent_levi_commutator : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₁ : G D p) (b : Mx D p p), mat g₁ = blk4 1 b 0 1 →
  ∀ y : Mx D ρ p, ∃ (z₀ : hermA D ρ) (x₀ : Mx D ρ p), M.sh y * M.emb g₁ = M.nzx z₀ x₀ * M.emb g₁ * M.sh y ∧
    z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) := by
  first | exact @GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip | exact GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip | (intros; apply GlobalTheory.CompanionTheory.ShEmbUnip.sh_emb_unip <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFamilyHeightBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFamilyHeightBound
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FamMajorant

theorem fam_majorant : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  rintro D n H hH ⟨C, hC, hcov⟩ χ s₁ φ hφ hlaw
  have hHpos : ∀ g, 0 < (H g : ℝ) := fun g => NNReal.coe_pos.2 (hH.2.1 g)
  have hpos : ∀ g, 0 < (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := fun g => Real.rpow_pos_of_pos (hHpos g) _
  have hcont : Continuous fun g => ‖φ g‖ / (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
    hφ.norm.div ((NNReal.continuous_coe.comp hH.1).rpow_const fun g => Or.inl (hHpos g).ne') fun g => (hpos g).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ max δ 0 := le_max_right _ _
  have hon : ∀ c ∈ C, ‖φ c‖ ≤ max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro c hc
    have h1 := (hδ c hc).trans (le_max_left δ 0)
    rwa [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hpos c).le), div_le_iff₀ (hpos c)] at h1
  have hall : ∀ g, ‖φ g‖ ≤ max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro g
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
    have hr : 0 < absA D (Matrix.GeneralLinearGroup.det a) := hom_pos _ _
    rw [hlaw q hq a ha c, hH.2.2 q hq a ha c]
    have e1 : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [norm_npow hr]; congr 1; simp
    have e2 : ((absA D (Matrix.GeneralLinearGroup.det a) * H c : ℝ≥0) : ℝ) ^ (s₁.re + (n : ℝ) / 2) =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e2, norm_mul, norm_mul, e1]
    simp only [Circle.norm_coe, one_mul]
    have h0 : 0 ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
      Real.rpow_nonneg (NNReal.coe_nonneg _) _
    calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) *
          (max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2)) := mul_le_mul_of_nonneg_left (hon c hc) h0
      _ = _ := by ring
  refine ⟨max δ 0, hB0, fun z g => ?_⟩
  have e3 : ‖npow (H g) (z - s₁)‖ = (H g : ℝ) ^ (z.re - s₁.re) := by
    rw [norm_npow (hH.2.1 g)]; congr 1
  have e4 : (H g : ℝ) ^ (z.re + (n : ℝ) / 2) = (H g : ℝ) ^ (z.re - s₁.re) * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add (hHpos g)]; congr 1; ring
  have h0 : 0 ≤ (H g : ℝ) ^ (z.re - s₁.re) := (Real.rpow_pos_of_pos (hHpos g) _).le
  simp only [fam]
  rw [norm_mul, e3, e4]
  calc _ ≤ (H g : ℝ) ^ (z.re - s₁.re) * (max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hall g) h0
    _ = _ := by ring

end GlobalTheory.CompanionTheory.FamMajorant

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFamilyHeightBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_family_height_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.FamMajorant.fam_majorant | exact GlobalTheory.CompanionTheory.FamMajorant.fam_majorant | (intros; apply GlobalTheory.CompanionTheory.FamMajorant.fam_majorant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterQuadraticTrace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterQuadraticTrace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ChzConj

theorem chz_conj : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  intro D ρ p ψ b₀ b y z₀ hz
  unfold chz pr
  rw [hz]
  congr 2
  change Matrix.trace (Matrix.map b₀.1 (incA D) * ((y * b) * adj y)) = Matrix.trace (b * (adj y * (Matrix.map b₀.1 (incA D) * y)))
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ChzConj

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterQuadraticTraceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_character_quadratic_trace : ∀ (D : D7) (ρ p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (b : Mx D p p) (y : Mx D ρ p) (z₀ : hermA D ρ),
  z₀.1 = HMul.hMul (HMul.hMul y b : Mx D ρ p) (adj y) →
    chz ψ b₀ z₀ = ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) := by
  first | exact @GlobalTheory.CompanionTheory.ChzConj.chz_conj | exact GlobalTheory.CompanionTheory.ChzConj.chz_conj | (intros; apply GlobalTheory.CompanionTheory.ChzConj.chz_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnDifferentiableOnIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnDifferentiableOnIntegral
open MeasureTheory Filter
open scoped Topology

namespace GlobalTheory.CompanionTheory.Param

theorem continuousOn_differentiableOn_integral :
    ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
      [TopologicalSpace T] [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U →
      ∀ F : ℂ → T → Y → ℂ,
      ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
      (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
      (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧
        ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
      ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
        ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  intro Y T _ _ _ _ _ μ U hU F hF hdiff hdom
  have hGat : ∀ z ∈ U, ∀ (t : T) (y : Y),
      ContinuousAt (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (z, t, y) := fun z hz t y =>
    hF.continuousAt ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz (Set.mem_univ _)))
  have hslice : ∀ z ∈ U, ∀ t : T, Continuous (fun y => F z t y) := fun z hz t =>
    hF.comp_continuous (f := fun y : Y => (z, t, y)) (by fun_prop)
      fun y => Set.mk_mem_prod hz (Set.mem_univ _)
  refine ⟨?_, fun t => ?_⟩
  · rintro ⟨z₀, t₀⟩ ⟨hz₀, -⟩
    obtain ⟨V, hV, N, hN, w, hw, hbound⟩ := hdom z₀ hz₀ t₀
    refine ContinuousAt.continuousWithinAt ?_
    refine MeasureTheory.continuousAt_of_dominated (bound := w) ?_ ?_ hw ?_
    · have hmem : U ×ˢ (Set.univ : Set T) ∈ 𝓝 (z₀, t₀) :=
        (hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hz₀ (Set.mem_univ _))
      filter_upwards [hmem] with x hx
      exact (hslice x.1 hx.1 x.2).aestronglyMeasurable
    · have hmem : V ×ˢ N ∈ 𝓝 (z₀, t₀) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod hV hN
      filter_upwards [hmem] with x hx
      exact Filter.Eventually.of_forall fun y => hbound x.1 hx.1 x.2 hx.2 y
    · exact Filter.Eventually.of_forall fun y =>
        ContinuousAt.comp_of_eq (f := fun x : ℂ × T => (x.1, x.2, y)) (hGat z₀ hz₀ t₀ y)
          (by fun_prop) rfl
  · obtain ⟨h, -⟩ := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ)
      (F := fun y z => F z t y) hU (fun z hz => (hslice z hz t).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => hdiff t y) (fun z hz => by
        obtain ⟨V, hV, N, hN, w, hw, hb⟩ := hdom z hz t
        exact ⟨V, hV, w, hw, Filter.Eventually.of_forall fun y z' hz' =>
          hb z' hz' t (mem_of_mem_nhds hN) y⟩)
    exact h

end GlobalTheory.CompanionTheory.Param
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnDifferentiableOnIntegralStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_differentiableOn_parameter_integral : ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [TopologicalSpace T]
    [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U → ∀ F : ℂ → T → Y → ℂ,
  ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
  (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
  (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧ ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
  ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
    ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  first | exact @GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral | exact GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral | (intros; apply GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeights
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.RSecPf

variable {D : D7} {n ρ p : ℕ}

theorem rpow_le_add {r τ τ₁ τ₂ : ℝ} (hr : 0 < r) (h₁ : τ₁ ≤ τ) (h₂ : τ ≤ τ₂) : r ^ τ ≤ r ^ τ₁ + r ^ τ₂ := by
  rcases le_total r 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hr h h₁).trans (le_add_of_nonneg_right (Real.rpow_nonneg hr.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h h₂).trans (le_add_of_nonneg_left (Real.rpow_nonneg hr.le _))

theorem shear_pt {a b τ τ₁ τ₂ W₁ W₂ c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (h₁ : τ₁ ≤ τ) (h₂ : τ ≤ τ₂)
    (hW₁ : a ^ τ₁ * c ≤ W₁ * b ^ τ₁) (hW₂ : a ^ τ₂ * c ≤ W₂ * b ^ τ₂) :
    a ^ τ * c ≤ (W₁ + W₂) * (b ^ τ₁ + b ^ τ₂) := by
  have hr : 0 < a / b := div_pos ha hb
  have e : ∀ t : ℝ, a ^ t = (a / b) ^ t * b ^ t := fun t => by
    rw [← Real.mul_rpow hr.le hb.le, div_mul_cancel₀ _ hb.ne']
  have key : ∀ {t W : ℝ}, a ^ t * c ≤ W * b ^ t → (a / b) ^ t * c ≤ W := fun {t W} h => by
    have hbt : 0 < b ^ t := Real.rpow_pos_of_pos hb t
    rw [e t] at h
    have : (a / b) ^ t * c * b ^ t ≤ W * b ^ t := by linarith [h]
    exact le_of_mul_le_mul_right this hbt
  have k₁ := key hW₁
  have k₂ := key hW₂
  have n₁ : 0 ≤ W₁ := (mul_nonneg (Real.rpow_nonneg hr.le _) hc).trans k₁
  have n₂ : 0 ≤ W₂ := (mul_nonneg (Real.rpow_nonneg hr.le _) hc).trans k₂
  have h3 : (a / b) ^ τ * c ≤ W₁ + W₂ := by
    have := mul_le_mul_of_nonneg_right (rpow_le_add hr h₁ h₂) hc
    linarith
  have h4 : b ^ τ ≤ b ^ τ₁ + b ^ τ₂ := rpow_le_add hb h₁ h₂
  have hbt : 0 ≤ b ^ τ := Real.rpow_nonneg hb.le _
  calc a ^ τ * c = (a / b) ^ τ * c * b ^ τ := by rw [e τ]; ring
    _ ≤ (W₁ + W₂) * b ^ τ := mul_le_mul_of_nonneg_right h3 hbt
    _ ≤ (W₁ + W₂) * (b ^ τ₁ + b ^ τ₂) := mul_le_mul_of_nonneg_left h4 (add_nonneg n₁ n₂)

theorem local_tau (hn : ρ + p = n) {z₀ : ℂ} (hz : ((ρ : ℝ) - p) / 2 < z₀.re) :
    ∃ V ∈ 𝓝 z₀, ∃ τ₁ τ₂ : ℝ, (ρ : ℝ) < τ₁ ∧ τ₁ ≤ τ₂ ∧
      ∀ z ∈ V, τ₁ ≤ z.re + (n : ℝ) / 2 ∧ z.re + (n : ℝ) / 2 ≤ τ₂ := by
  obtain ⟨ε, hε, hε'⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = (z₀.re - ((ρ : ℝ) - p) / 2) / 2 := ⟨_, by linarith, rfl⟩
  have hnr : (n : ℝ) = ρ + p := by rw [← hn]; push_cast; ring
  refine ⟨Metric.ball z₀ ε, Metric.ball_mem_nhds _ hε, z₀.re - ε + n / 2, z₀.re + ε + n / 2, ?_, ?_, fun z hz' => ?_⟩
  · rw [hnr]; linarith
  · linarith
  · have h : |(z - z₀).re| < ε := (Complex.abs_re_le_norm _).trans_lt (by simpa [dist_eq_norm] using hz')
    rw [Complex.sub_re, abs_lt] at h
    constructor <;> linarith [h.1, h.2]

theorem continuous_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  unfold fam npow
  refine Continuous.mul (Continuous.cpow ?_ (continuous_fst.sub continuous_const) ?_) (hφ.comp continuous_snd)
  · exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hH.1.comp continuous_snd))
  · exact fun u => Complex.ofReal_mem_slitPlane.2 (NNReal.coe_pos.2 (hH.2.1 _))

theorem differentiable_fam {H : G D n → ℝ≥0} (hH : IsHt H) (φ : G D n → ℂ) (s₁ : ℂ) (g : G D n) :
    Differentiable ℂ fun z => fam H φ s₁ z g := by
  have h : ((H g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hH.2.1 g).ne'
  unfold fam npow
  exact ((differentiable_id.sub_const s₁).const_cpow (Or.inl h)).mul_const _

theorem fam_le {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} {s₁ : ℂ} {B κ τ₂ : ℝ} (hB : 0 ≤ B) (hκ : 1 ≤ κ)
    (hf : ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2))
    {z : ℂ} (h0 : 0 ≤ z.re + (n : ℝ) / 2) (h2 : z.re + (n : ℝ) / 2 ≤ τ₂) {x c : G D n}
    (hc : (H (x * c) : ℝ) ≤ κ * (H x : ℝ)) :
    ‖fam H φ s₁ z (x * c)‖ ≤ B * κ ^ τ₂ * (H x : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  have hx : (0 : ℝ) < H x := NNReal.coe_pos.2 (hH.2.1 x)
  have hxc : (0 : ℝ) ≤ H (x * c) := NNReal.coe_nonneg _
  have hκ0 : 0 ≤ κ := by linarith
  calc ‖fam H φ s₁ z (x * c)‖ ≤ B * (H (x * c) : ℝ) ^ (z.re + (n : ℝ) / 2) := hf z _
    _ ≤ B * (κ * (H x : ℝ)) ^ (z.re + (n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxc hc h0) hB
    _ = B * κ ^ (z.re + (n : ℝ) / 2) * (H x : ℝ) ^ (z.re + (n : ℝ) / 2) := by
        rw [Real.mul_rpow hκ0 hx.le]; ring
    _ ≤ B * κ ^ τ₂ * (H x : ℝ) ^ (z.re + (n : ℝ) / 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hB) (Real.rpow_nonneg hx.le _)
        exact Real.rpow_le_rpow_of_exponent_le hκ h2

section Main

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (b₀ : HermE D ρ)

theorem continuous_jacobi_map_origin : Continuous fun ζ : hermA D ρ => M.nzx ζ 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)

theorem wz_family (hψ : IsCharAF D.host.F ψ) {H : G D n → ℝ≥0} (hH : IsHt H)
    (hcpt : ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c)
    {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (hφ : Continuous φ) (hlaw : IsLaw χ s₁ φ) :
    ContinuousOn (fun u : ℂ × G D n => Wz M m ψ b₀ (fam H φ s₁ u.1) u.2)
        ({z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} ×ˢ Set.univ) ∧
      ∀ c, DifferentiableOn ℂ (fun z => Wz M m ψ b₀ (fam H φ s₁ z) c) {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := by
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  obtain ⟨B, hB, hf⟩ := GlobalTheory.T.eisenstein_family_height_bound D n H hH hcpt χ s₁ φ hφ hlaw
  obtain ⟨hcz, hnz⟩ := GlobalTheory.T.centre_character_continuous_unit D ρ ψ hψ b₀
  have hU : IsOpen {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.T.continuousOn_differentiableOn_parameter_integral (Y := hermA D ρ) (T := G D n) m.lz _ hU
    (fun z c ζ => fam H φ s₁ z (M.w * M.nzx ζ 0 * c) * conj (chz ψ b₀ ζ)) ?_ ?_ ?_
  · refine Continuous.continuousOn (Continuous.mul ?_ ?_)
    · refine (continuous_fam hH hφ s₁).comp (continuous_fst.prodMk ?_)
      exact (continuous_const.mul ((continuous_jacobi_map_origin M).comp (continuous_snd.comp continuous_snd))).mul
        (continuous_fst.comp continuous_snd)
    · exact Complex.continuous_conj.comp (hcz.comp (continuous_snd.comp continuous_snd))
  · exact fun c ζ => ((differentiable_fam hH φ s₁ _).mul_const _).differentiableOn
  · intro z₀ hz₀ c₀
    obtain ⟨V, hV, τ₁, τ₂, h1, h12, hτ⟩ := local_tau hn hz₀
    obtain ⟨N, hN, hNm⟩ := exists_compact_mem_nhds c₀
    obtain ⟨κ, hκ, hκc⟩ := GlobalTheory.T.height_right_translate_compact_bound D n H hH hcpt N hN
    have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
    have I₁ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₁ h1
    have I₂ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₂ (h1.trans_le h12)
    refine ⟨V, hV, N, hNm, fun ζ => B * κ ^ τ₂ * ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂),
      (I₁.add I₂).const_mul _, fun z hz c hc ζ => ?_⟩
    have hx : (0 : ℝ) < H (M.w * M.nzx ζ 0) := NNReal.coe_pos.2 (hH.2.1 _)
    have h0 : 0 ≤ z.re + (n : ℝ) / 2 := by linarith [(hτ z hz).1]
    rw [norm_mul, RCLike.norm_conj, hnz, mul_one]
    refine (fam_le hH hB hκ hf h0 (hτ z hz).2 (hκc c hc _)).trans ?_
    refine mul_le_mul_of_nonneg_left (rpow_le_add hx (hτ z hz).1 (hτ z hz).2) ?_
    exact mul_nonneg hB (Real.rpow_nonneg (by linarith) _)

end Main

theorem isLaw_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (hl : IsLaw χ s₁ φ) (z : ℂ) :
    IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) * absA D (Matrix.GeneralLinearGroup.det a)⁻¹ = 1 := by
    rw [← map_mul]; simp
  have hne : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul_eq_one h1
  have hc : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  simp only [fam]
  rw [hH.2.2 q hq a ha g, hl q hq a ha g]
  unfold npow
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  have e : ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) =
      ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ (z - s₁) *
        ((absA D (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ (s₁ + (n : ℂ) / 2) := by
    rw [← Complex.cpow_add _ _ hc]; congr 1; ring
  rw [e]; ring

section Main2

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (b₀ : HermE D ρ)

theorem rsec_family (hψ : IsCharAF D.host.F ψ) {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} (hθ : IsInfFam θ)
    {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {H : G D n → ℝ≥0} (hH : IsHt H)
    (hcpt : ∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c)
    {s₁ : ℂ} {φ : G D n → ℂ} (hφ : Continuous φ) (hlaw : IsLaw χ s₁ φ) (g : G D n) :
    ContinuousOn (fun u : ℂ × G D p => Rsec M m ψ b₀ (fam H φ s₁ u.1) g Ω u.2)
        ({z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} ×ˢ Set.univ) ∧
      ∀ h, DifferentiableOn ℂ (fun z => Rsec M m ψ b₀ (fam H φ s₁ z) g Ω h) {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := by
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨hc1, hd1⟩ := wz_family M m b₀ hψ hH hcpt hφ hlaw
  obtain ⟨B, hB, hf⟩ := GlobalTheory.T.eisenstein_family_height_bound D n H hH hcpt χ s₁ φ hφ hlaw
  obtain ⟨hcz, hnz⟩ := GlobalTheory.T.centre_character_continuous_unit D ρ ψ hψ b₀
  have hU : IsOpen {z : ℂ | ((ρ : ℝ) - p) / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.T.continuousOn_differentiableOn_parameter_integral (Y := Mx D ρ p) (T := G D p) m.μ _ hU
    (fun z h y => Wz M m ψ b₀ (fam H φ s₁ z) (M.sh y * M.emb h * g) * conj (Ω h y)) ?_ ?_ ?_
  · refine ContinuousOn.mul ?_ (Continuous.continuousOn ?_)
    · refine hc1.comp (f := fun u : ℂ × G D p × Mx D ρ p => (u.1, M.sh u.2.2 * M.emb u.2.1 * g))
        (Continuous.continuousOn (continuous_fst.prodMk ?_)) fun u hu => ⟨hu.1, trivial⟩
      exact ((M.sh_cont.comp (continuous_snd.comp continuous_snd)).mul
        (M.emb_cont.comp (continuous_fst.comp continuous_snd))).mul continuous_const
    · exact Complex.continuous_conj.comp (hΩ.cont.comp continuous_snd)
  · exact fun h y => (hd1 _).mul_const _
  · intro z₀ hz₀ h₀
    obtain ⟨V, hV, τ₁, τ₂, h1, h12, hτ⟩ := local_tau hn hz₀
    obtain ⟨N, hN, hNm⟩ := exists_compact_mem_nhds h₀
    have hCc : IsCompact ((fun h => M.emb h * g) '' N) := hN.image (M.emb_cont.mul continuous_const)
    obtain ⟨κ, hκ, hκc⟩ := GlobalTheory.T.height_right_translate_compact_bound D n H hH hcpt _ hCc
    obtain ⟨Φ, hΦ, hmaj⟩ := hΩ.maj N hN
    have hρ : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
    obtain ⟨W₁, iW₁, hW₁⟩ := GlobalTheory.T.schwartz_height_majorant_integrable D n ρ p hn M m θ hθ H hH hcpt Φ hΦ τ₁ (by linarith)
    obtain ⟨W₂, iW₂, hW₂⟩ := GlobalTheory.T.schwartz_height_majorant_integrable D n ρ p hn M m θ hθ H hH hcpt Φ hΦ τ₂ (by linarith)
    have I₁ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₁ h1
    have I₂ := GlobalTheory.T.height_power_integrable_weyl_orbit D n ρ p hn M m H hH hcpt τ₂ (h1.trans_le h12)
    have IA := I₁.add I₂
    refine ⟨V, hV, N, hNm, fun y => B * κ ^ τ₂ * (W₁ y + W₂ y) *
      ∫ ζ : hermA D ρ, ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂) ∂m.lz,
      ((iW₁.add iW₂).const_mul _).mul_const _, fun z hz h hh y => ?_⟩
    have h0 : 0 ≤ z.re + (n : ℝ) / 2 := by linarith [(hτ z hz).1]
    rw [norm_mul, RCLike.norm_conj]
    have hκ0 : 0 ≤ B * κ ^ τ₂ := mul_nonneg hB (Real.rpow_nonneg (by linarith) _)
    have key : ‖Wz M m ψ b₀ (fam H φ s₁ z) (M.sh y * M.emb h * g)‖ * ‖Φ y‖ ≤ B * κ ^ τ₂ * (W₁ y + W₂ y) *
        ∫ ζ : hermA D ρ, ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂) ∂m.lz := by
      have e : ‖Wz M m ψ b₀ (fam H φ s₁ z) (M.sh y * M.emb h * g)‖ * ‖Φ y‖ =
          ‖∫ ζ : hermA D ρ, (fam H φ s₁ z (M.w * M.nzx ζ 0 * (M.sh y * M.emb h * g)) * conj (chz ψ b₀ ζ)) *
            ((‖Φ y‖ : ℝ) : ℂ) ∂m.lz‖ := by
        rw [integral_mul_const, norm_mul, Complex.norm_real, norm_norm]; rfl
      rw [e, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (IA.const_mul _) (.of_forall fun ζ => ?_)
      rw [norm_mul, norm_mul, RCLike.norm_conj, hnz, mul_one, Complex.norm_real, norm_norm]
      have e2 : M.w * M.nzx ζ 0 * (M.sh y * M.emb h * g) = (M.w * M.nzx ζ 0 * M.sh y) * (M.emb h * g) := by
        simp only [mul_assoc]
      rw [e2]
      have hb := fam_le hH hB hκ hf h0 (hτ z hz).2 (hκc _ ⟨h, hh, rfl⟩ (M.w * M.nzx ζ 0 * M.sh y))
      have hp := shear_pt (NNReal.coe_pos.2 (hH.2.1 (M.w * M.nzx ζ 0 * M.sh y))) (NNReal.coe_pos.2 (hH.2.1 (M.w * M.nzx ζ 0)))
        (norm_nonneg (Φ y)) (hτ z hz).1 (hτ z hz).2 (hW₁ _ y) (hW₂ _ y)
      calc _ ≤ (B * κ ^ τ₂ * (H (M.w * M.nzx ζ 0 * M.sh y) : ℝ) ^ (z.re + (n : ℝ) / 2)) * ‖Φ y‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = B * κ ^ τ₂ * ((H (M.w * M.nzx ζ 0 * M.sh y) : ℝ) ^ (z.re + (n : ℝ) / 2) * ‖Φ y‖) := by ring
        _ ≤ B * κ ^ τ₂ * ((W₁ y + W₂ y) * ((H (M.w * M.nzx ζ 0) : ℝ) ^ τ₁ + (H (M.w * M.nzx ζ 0) : ℝ) ^ τ₂)) :=
            mul_le_mul_of_nonneg_left hp hκ0
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left (hmaj h hh y) (norm_nonneg _)).trans key

end Main2

section Law

variable {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (b₀ : HermE D ρ)

theorem npow_add' {r : ℝ≥0} (hr : (r : ℝ) ≠ 0) (s t : ℂ) : npow r (s + t) = npow r s * npow r t := by
  unfold npow
  exact Complex.cpow_add _ _ (by exact_mod_cast hr)

theorem conj_npow_ofReal (r : ℝ≥0) (t : ℝ) : conj (npow r (t : ℂ)) = npow r (t : ℂ) := by
  unfold npow
  rw [← Complex.ofReal_cpow (NNReal.coe_nonneg r), Complex.conj_ofReal]

theorem rsec_levi {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ' θ b₀ m.μ Ω)
    {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (g : G D n) (g₀ : G D p) (a : GL (Fin p) (AE D))
    (ha : mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1)) (h : G D p) :
    Rsec M m ψ b₀ f g Ω (g₀ * h) = ((χ * χ'⁻¹) (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (p : ℂ) / 2) * Rsec M m ψ b₀ f g Ω h := by
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) * absA D (Matrix.GeneralLinearGroup.det a)⁻¹ = 1 := by
    rw [← map_mul]; simp
  have hne : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≠ 0 := by
    exact_mod_cast left_ne_zero_of_mul_eq_one h1
  have e : ∀ y : Mx D ρ p, Wz M m ψ b₀ f (M.sh y * M.emb (g₀ * h) * g) * conj (Ω (g₀ * h) y) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        conj ((χ' (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((ρ : ℂ) / 2))) *
      (fun y' : Mx D ρ p => Wz M m ψ b₀ f (M.sh y' * M.emb h * g) * conj (Ω h y')) (HMul.hMul y a.1 : Mx D ρ p) := by
    intro y
    have e1 : M.sh y * M.emb (g₀ * h) * g = M.emb g₀ * (M.sh (HMul.hMul y a.1 : Mx D ρ p) * M.emb h * g) := by
      rw [map_mul, ← mul_assoc, GlobalTheory.T.shift_commutes_levi_embedding D n ρ p hn M g₀ a ha y]
      simp only [mul_assoc]
    rw [e1, GlobalTheory.T.coefficient_levi_equivariance D n ρ p hn M m ψ b₀ χ z f hf g₀ a ha, hΩ.levi g₀ a ha h y]
    simp only [map_mul]
    ring
  unfold Rsec
  simp_rw [e]
  rw [integral_const_mul, GlobalTheory.RightMulJac.integral_mul_right D ρ p m.μ m.𝓕 m.hμ a
    (fun y' : Mx D ρ p => Wz M m ψ b₀ f (M.sh y' * M.emb h * g) * conj (Ω h y'))]
  have hnr : (n : ℂ) = ρ + p := by rw [← hn]; push_cast; ring
  have hs : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (p : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (((ρ / 2 : ℝ) : ℂ)) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(ρ : ℂ)) := by
    rw [← npow_add' hne, ← npow_add' hne]
    congr 1
    rw [hnr]; push_cast; ring
  have hc : conj (npow (absA D (Matrix.GeneralLinearGroup.det a)) ((ρ : ℂ) / 2)) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (((ρ / 2 : ℝ) : ℂ)) := by
    have := conj_npow_ofReal (absA D (Matrix.GeneralLinearGroup.det a)) (ρ / 2 : ℝ)
    push_cast at this ⊢
    exact this
  rw [hs, map_mul, hc, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul,
    Circle.coe_inv_eq_conj]
  ring

theorem rsec_unip (hψ : IsCharAF D.host.F ψ) {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (g : G D n) (g₁ : G D p) (b : Mx D p p)
    (hb : mat g₁ = blk4 1 b 0 1) (h : G D p) : Rsec M m ψ b₀ f g Ω (g₁ * h) = Rsec M m ψ b₀ f g Ω h := by
  unfold Rsec
  refine integral_congr_ae (.of_forall fun y => ?_)
  obtain ⟨z₀, x₀, e1, e2⟩ := GlobalTheory.T.shift_unipotent_levi_commutator D n ρ p hn M g₁ b hb y
  have e3 : M.sh y * M.emb (g₁ * h) * g = M.nzx z₀ x₀ * M.emb g₁ * (M.sh y * M.emb h * g) := by
    rw [map_mul, ← mul_assoc, e1]
    simp only [mul_assoc]
  show Wz M m ψ b₀ f (M.sh y * M.emb (g₁ * h) * g) * conj (Ω (g₁ * h) y) =
    Wz M m ψ b₀ f (M.sh y * M.emb h * g) * conj (Ω h y)
  rw [e3, GlobalTheory.T.coefficient_unipotent_levi_invariance D n ρ p hn M m ψ hψ b₀ χ z f hf g₁ b hb, hΩ.unip g₁ b hb h y, GlobalTheory.T.centre_character_quadratic_trace D ρ p ψ b₀ b y z₀ e2, map_mul]
  have hu : ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p))) *
      conj (ψ (halfTr (Matrix.trace (HMul.hMul b (pr b₀ y y) : Mx D p p)))) = 1 := by
    rw [Complex.mul_conj', hψ.2.1]; simp
  linear_combination (Wz M m ψ b₀ f (M.sh y * M.emb h * g) * conj (Ω h y)) * hu

theorem rsec_law (hψ : IsCharAF D.host.F ψ) {χ χ' : (AE D)ˣ →* Circle} {θ : InfFam D} {Ω : G D p → Mx D ρ p → ℂ}
    (hΩ : IsTh ψ χ' θ b₀ m.μ Ω) {z : ℂ} {f : G D n → ℂ} (hf : IsLaw χ z f) (g : G D n) :
    IsLaw (χ * χ'⁻¹) z (Rsec M m ψ b₀ f g Ω) := by
  intro q hq a ha h
  obtain ⟨g₁, g₂, b, rfl, h1, h2⟩ := GlobalTheory.T.parabolic_unipotent_levi_factor D p q hq a ha
  rw [mul_assoc, rsec_unip M m b₀ hψ hΩ hf g g₁ b h1, rsec_levi M m b₀ hΩ hf g g₂ a h2]

end Law

theorem rSec_of_htExist : HtExist → RSec := by
  intro hHt D n ρ p hn M m ψ hψ b₀ _ χ χ' _ _ θ hθ Ω hΩ H hH s₁ φ hφ hlaw g
  obtain ⟨h1, h2⟩ := rsec_family M m b₀ hψ hθ hΩ hH (hHt D n).2 hφ hlaw g
  exact ⟨h1, h2, fun z _ => rsec_law M m b₀ hψ hΩ (isLaw_fam hH hlaw z) g⟩

end GlobalTheory.CompanionTheory.RSecPf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeightsStatement
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_of_heights : HtExist → RSec := by
  first | exact @GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | exact GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist | (intros; apply GlobalTheory.CompanionTheory.RSecPf.rSec_of_htExist <;> assumption)
end
