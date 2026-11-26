module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenB
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem g_ext {n : ℕ} {g h : G D n} (e : mat g = mat h) : g = h := by
  unfold mat at e
  exact Subtype.ext (Units.ext e)

theorem exists_slice {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (x0 : Mx D m n)
    (z : Matrix (Fin m) (Fin n) ℂ) : ∃ x : Mx D m n, compAt θ τ x = z ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x0) ∧ x.map (finPart D) = x0.map (finPart D) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.AdForm.RatMove.realPt_spec hθ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0)
  refine ⟨x0 + GlobalTheory.AdForm.realPt θ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0), ?_, ?_, ?_⟩
  · rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp
  · intro τ' h
    rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp [h]
  · rw [Matrix.map_add _ (map_add (finPart D)), h1, add_zero]

theorem tens_at {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) (x : Mx D m n) (u : Matrix (Fin m) (Fin n) ℂ)
    (hx : compAt θ τ x = fr * u) : tens θ τ fr f Ψ x = f u * Ψ x := by
  simp only [tens, hx, Matrix.nonsing_inv_mul_cancel_left _ _ hfr]

theorem awayCls_zero {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    AwayCls θ τ fr (0 : Mx D m n → ℂ) := by
  refine ⟨fun _ _ _ _ => rfl, fun f _ => ?_⟩
  have : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
    funext x
    simp [tens]
  rw [this]
  exact zero_mem _

theorem exists_nU (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : ∃ y : GR n, mR y = nU b := by
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨nU b, nU (-b), by simp [nU, Matrix.fromBlocks_multiply], by simp [nU, Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ GR n := by
    show InG (nU b)
    simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
    simp
  exact ⟨⟨u, hu⟩, rfl⟩

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem finite_part_block_matrix {n : ℕ} (a b c d : Mx D n n) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem neg_block_matrix {R : Type} [CommRing R] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_neg]
  rfl

theorem jsq {R : Type} [CommRing R] {n : ℕ} :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  rw [GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, ← GlobalTheory.StdUnn.Frame.block_matrix_one, neg_block_matrix]
  simp

theorem mat_inv_w {n : ℕ} (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat w⁻¹ = -blk4 0 1 (-1) 0 := by
  have h1 : mat w⁻¹ * mat w = 1 := by
    show mat (w⁻¹ * w) = 1
    rw [inv_mul_cancel]
    rfl
  have h2 : mat w * (-mat w) = 1 := by rw [mul_neg, hw, jsq, neg_neg]
  calc mat w⁻¹ = mat w⁻¹ * (mat w * (-mat w)) := by rw [h2, mul_one]
    _ = -mat w := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [hw]

end PositivityTheory.Rg.Sw.Glob.OG
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem compAt_zero' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j
  simp [compAt]

theorem compAt_one' (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} : compAt θ τ (1 : Mx D n n) = 1 := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem compAt_J (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} :
    compAt θ τ (blk4 (0 : Mx D n n) 1 (-1) 0) = blk4 0 1 (-1) 0 := by
  rw [component_block_matrix, GlobalTheory.RealParamSize.compAt_neg, compAt_zero', compAt_one']

theorem fin_J {n : ℕ} : (blk4 (0 : Mx D n n) 1 (-1) 0).map (finPart D) = blk4 0 1 (-1) 0 := by
  rw [finite_part_block_matrix, Matrix.map_neg _ (map_neg (finPart D)), Matrix.map_zero _ (map_zero (finPart D)),
    Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))]

theorem iota_conj {θ : InfFam D} {τ : D.what₂.Tau} {n : ℕ} {ι : GR n →* G D n} (hθ : IsInfFam θ)
    (hι : IsPlaceEmb θ τ ι) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (y yn : GR n) (c : Matrix (Fin n) (Fin n) ℂ)
    (hyc : mR y = nbar c) (hyn : mR yn = nU (-c)) : ι yn = w⁻¹ * ι y * w := by
  apply g_ext
  have hm : mat (w⁻¹ * ι y * w) = mat w⁻¹ * mat (ι y) * mat w := rfl
  rw [hm, mat_inv_w w hw, hw]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 yn).2.2, (hι.2 y).2.2, Matrix.map_neg _ (map_neg (finPart D)), fin_J, mul_one,
      neg_mul, jsq, neg_neg]
  · intro τ'
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.RealParamSize.compAt_neg, compAt_J]
    by_cases h : τ' = τ
    · subst h
      rw [(hι.2 yn).1, (hι.2 y).1, hyn, hyc]
      change blk4 1 (-c) 0 1 = -blk4 0 1 (-1) 0 * blk4 1 0 c 1 * blk4 0 1 (-1) 0
      rw [neg_block_matrix, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul]
      simp
    · rw [(hι.2 yn).2.1 τ' h, (hι.2 y).2.1 τ' h, mul_one, neg_mul, jsq, neg_neg]

end PositivityTheory.Rg.Sw.Glob.OG
