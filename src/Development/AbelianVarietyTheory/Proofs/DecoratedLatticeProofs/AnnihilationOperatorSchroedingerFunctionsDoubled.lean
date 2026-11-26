module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivativeDiagonalHalfEqSchrodingerDer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumRealEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerDualHalfDerivativeLinearForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerDualHalfDerivativeLinearForm
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

theorem gramAt_conjTranspose {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, HSpace.gram]
  rw [← h1]
  exact (NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem conj_complexPlace_traceZero_element (D : D7) (τ : D.what₂.Tau) : conj (tauE D τ D.host.xi0) = -tauE D τ D.host.xi0 := by
  have hcm := D.host.isCMField_hostE
  rw [← NumberField.IsCMField.complexEmbedding_complexConj _ (tauE D τ) _]
  have h := GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D
  change tauE D τ (star D.host.xi0) = _
  rw [h, map_neg]

theorem re_trace_swap {n m : ℕ} (c : ℂ) (hc : conj c = -c) (G : Matrix (Fin n) (Fin n) ℂ) (hG : Gᴴ = G)
    (X Y : Matrix (Fin n) (Fin m) ℂ) :
    (c * Matrix.trace (Xᴴ * G * Y)).re = -(c * Matrix.trace (Yᴴ * G * X)).re := by
  have ht : Matrix.trace (Xᴴ * G * Y) = conj (Matrix.trace (Yᴴ * G * X)) := by
    have h := Matrix.trace_conjTranspose (Yᴴ * G * X)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      ← Matrix.mul_assoc] at h
    exact h
  rw [ht]
  have hre : c.re = 0 := by
    have := congrArg Complex.re hc
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hre]
  ring

end GlobalTheory.StdUnn


open GlobalTheory.Unf in
theorem GlobalTheory.StdUnn.sch_dRho_dualHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν f hf τ Y x
  let d := dblDec A
  let v : VolM D B.rank A.rank := ⟨ν, 𝓨, hν⟩
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := B.rank) (n := A.rank) hθ τ Y
  have hq : compAt θ τ d.pY = d.qY.map (tauE D τ) := by
    ext i j
    exact (hθ τ).1 _
  have hL' : IsLineAt θ τ (Y * compAt θ τ d.pY) ((d.extY B).comp (lineAt θ τ Y)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ Y t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ Y t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY B (lineAt θ τ Y t) = lineAt θ τ (Y * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := GlobalTheory.Unf.hasDerivAt_mixS_extY D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank d v f hf
    (lineAt θ τ Y) hL.1 hL.2.1 x 0
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (d.extY B (lineAt θ τ Y t)) f p) 0) =
      dRho (heisO ψ (dblSp A) B) θ τ (Y * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  change HasDerivAt (fun t : ℝ => ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) * d.mixS B ψ v.μ v.𝓕 f x 0) (d.mixS B ψ v.μ v.𝓕 (fun p => deriv (fun t : ℝ => heisO ψ (dblSp A) B (d.extY B (lineAt θ τ Y t)) f p) 0) x 0) 0 at hder
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
      Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D A.rank) B x τ Y t
    have e2 : symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t)) =
        symplOH (GlobalTheory.Size.posSp D A.rank) B x (lineAt θ τ Y t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (hO_posSp D B A.rank x _)).symm
    have e3 : ψ (symplOH (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    rw [symplO_eq_two_half, AddChar.map_add_eq_mul, e3, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun2 : (fun t : ℝ => ψ (symplO (dblSp A) B (d.extX B x) (d.extY B (lineAt θ τ Y t))) *
      d.mixS B ψ v.μ v.𝓕 f x 0) =
      fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I *
        (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) : ℂ)) * t) *
          d.mixS B ψ v.μ v.𝓕 f x 0 :=
    funext fun t => by rw [hphase]
  rw [hfun2] at hder
  set a : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D A.rank) B τ Y (compAt θ τ x) with ha_def
  set M := d.mixS B ψ v.μ v.𝓕 f x 0 with hM
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * t) * M)
      ((2 * Real.pi * Complex.I * (a : ℂ)) * M) 0 := by
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * u) * M)
        (Complex.exp ((2 * Real.pi * Complex.I * (a : ℂ)) * ((0:ℝ):ℂ)) * ((2 * Real.pi * Complex.I * (a : ℂ)) * 1) * M)
        ((0:ℝ):ℂ) :=
      (((hasDerivAt_id _).const_mul (2 * Real.pi * Complex.I * (a : ℂ))).cexp).mul_const M
    have h3 := h2.comp_ofReal
    refine h3.congr_deriv ?_
    simp
  have heq := hder.unique hexp
  have ha : a = -(2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re) := by
    rw [ha_def]
    refine (GlobalTheory.Unf.symplAt_posSp D B A.rank τ Y (compAt θ τ x)).trans ?_
    rw [GlobalTheory.StdUnn.re_trace_swap _ (GlobalTheory.StdUnn.conj_complexPlace_traceZero_element D τ) _ (GlobalTheory.StdUnn.gramAt_conjTranspose B τ)]
    ring
  show d.mixS B ψ ν 𝓨 _ x 0 = _ * d.mixS B ψ ν 𝓨 f x 0
  rw [← hq]
  change d.mixS B ψ v.μ v.𝓕 _ x 0 = _ * M
  rw [heq, ha]
  push_cast
  ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerDualHalfDerivativeLinearFormStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_dualHalf_derivative_linear_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (Y * (dblDec A).qY.map (tauE D τ)) f) x = -(2 * Real.pi * Complex.I) * ((2 * (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re : ℝ) : ℂ) * sch ψ A B ν 𝓨 f x := by
  first | exact @GlobalTheory.StdUnn.sch_dRho_dualHalf | exact GlobalTheory.StdUnn.sch_dRho_dualHalf | (intros; apply GlobalTheory.StdUnn.sch_dRho_dualHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivativeDiagonalHalfEqSchrodingerDerStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_diagonalHalf_eq_schrodingerDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (X * (dblDec A).qX.map (tauE D τ)) f) x = deriv (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) 0 := by
  first | exact @GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag | exact GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag | (intros; apply GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubled
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnih

theorem blockMatrix_swap_mul_top_rows_eq_bottom_rows {n k : ℕ} (M : Matrix (Fin (n + n)) (Fin k) ℂ) :
    (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0 * M).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      M.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  have hM : M = (M.submatrix finSumFinEquiv id).submatrix finSumFinEquiv.symm id := by ext; simp
  rw [hM, blk4, Matrix.submatrix_mul_equiv]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem row_sub_mul {a b k l : ℕ} (M : Matrix (Fin a) (Fin k) ℂ) (N : Matrix (Fin k) (Fin l) ℂ) (r : Fin b → Fin a) :
    M.submatrix r id * N = (M * N).submatrix r id := by
  ext i j
  simp [Matrix.mul_apply]

variable {D : D7}

theorem qX_mul_stdInv (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (s : RealMat (dblSp A)) (hs : IsStdInv A μ s)
    (τ : D.what₂.Tau) :
    (dblDec A).qX.map (tauE D τ) * s τ = ((‖tauE D τ μ‖ : ℂ)⁻¹) • (dblDec A).qY.map (tauE D τ) := by
  obtain ⟨-, hdet, hinv⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hRT : (Tm A μ)⁻¹ * Tm A μ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1 : ((Tm A μ)⁻¹).map (tauE D τ) * (Tm A μ).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hRT, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have h2 : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have hqX : (dblDec A).qX.map (tauE D τ) =
      (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hqY : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) =
      (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  have hsτ : s τ * (Tm A μ).map (tauE D τ) = (Tm A μ).map (tauE D τ) * stdInv A.rank μ τ := hs τ
  have hsR : ((Tm A μ)⁻¹).map (tauE D τ) * s τ = stdInv A.rank μ τ * ((Tm A μ)⁻¹).map (tauE D τ) := by
    calc ((Tm A μ)⁻¹).map (tauE D τ) * s τ
          = ((Tm A μ)⁻¹).map (tauE D τ) * (s τ * ((Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ))) := by
          rw [h2, Matrix.mul_one]
      _ = ((Tm A μ)⁻¹).map (tauE D τ) * ((Tm A μ).map (tauE D τ) * stdInv A.rank μ τ) *
            ((Tm A μ)⁻¹).map (tauE D τ) := by
          rw [← Matrix.mul_assoc (s τ), hsτ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hqX, row_sub_mul, hsR, stdInv, Matrix.smul_mul]
  have hb := blockMatrix_swap_mul_top_rows_eq_bottom_rows (((Tm A μ)⁻¹).map (tauE D τ))
  rw [← hqY] at hb
  ext i j
  have hij := congrFun (congrFun hb i) j
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, id] at hij ⊢
  rw [hij]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  field_simp

end GlobalTheory.StdUnnAnnih

namespace GlobalTheory.StdUnnAnnih

theorem re_imaginary_mul_neg_I_div_mul {a w : ℂ} (hre : a.re = 0) (him : 0 < a.im) (r : ℝ) :
    (a * (-(Complex.I / (r : ℂ))) * w).re = ‖a‖ / r * w.re := by
  have hn : ‖a‖ = a.im := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, zero_mul, zero_add, Real.sqrt_mul_self him.le]
  have ha : a = (a.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
  rw [hn, ha]
  have : (a.im : ℂ) * Complex.I * (-(Complex.I / (r : ℂ))) = ((a.im / r : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(a.im : ℂ) * (r : ℂ)⁻¹) * Complex.I_sq
  rw [this, Complex.re_ofReal_mul]
  simp

theorem annih_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ), sch ψ A B ν 𝓨 (annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f) = annS B l sB θ τ X (sch ψ A B ν 𝓨 f) := by
  intro D ψ hψ θ hθ A B ν 𝓨 hcov μ hμ s' sB hs hsB l hl f hf τ X
  have hJ : cplxO (s' τ) (sB τ) (X * (dblDec A).qX.map (tauE D τ)) =
      ((Complex.I / (‖tauE D τ μ‖ : ℂ)) • (sB τ * X)) * (dblDec A).qY.map (tauE D τ) := by
    unfold cplxO
    rw [Matrix.mul_assoc (sB τ), Matrix.mul_assoc X, qX_mul_stdInv A μ hμ s' hs τ, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, div_eq_mul_inv]
  set Y := (Complex.I / (‖tauE D τ μ‖ : ℂ)) • (sB τ * X) with hY
  have hd1 := GlobalTheory.OrientedHeis.theta_dRho (S := dblSp A) (T := B) hθ hψ τ (X * (dblDec A).qX.map (tauE D τ)) hf
  have hd2 := GlobalTheory.OrientedHeis.theta_dRho (S := dblSp A) (T := B) hθ hψ τ (Y * (dblDec A).qY.map (tauE D τ)) hf
  obtain ⟨-, hsm, -, hsmul⟩ := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hcov _ _ hd2 hd2 Complex.I
  obtain ⟨-, -, hadd, -⟩ := GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hcov _ _ hd1 hsm 0
  funext x
  rw [annih, hJ, hadd, hsmul, Pi.add_apply, Pi.smul_apply, GlobalTheory.T.heisenbergDerivative_diagonalHalf_eq_schrodingerDerivative D ψ hψ θ hθ A B ν 𝓨 hcov f hf τ X x,
    GlobalTheory.T.schrodinger_dualHalf_derivative_linear_form D ψ hψ θ hθ A B ν 𝓨 hcov f hf τ Y x]
  unfold annS linF
  congr 1
  obtain ⟨hss, hiso, -⟩ := hsB τ
  have hsG : (sB τ)ᴴ * gramAt D B τ = gramAt D B τ * sB τ := by
    calc (sB τ)ᴴ * gramAt D B τ = (sB τ)ᴴ * gramAt D B τ * (sB τ * sB τ) := by rw [hss, Matrix.mul_one]
      _ = gramAt D B τ * sB τ := by rw [← Matrix.mul_assoc, hiso]
  have htr : Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x) =
      -(Complex.I / (‖tauE D τ μ‖ : ℂ)) * Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x) := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc Xᴴ, hsG]
    congr 1
    simp [Complex.conj_ofReal, div_eq_mul_inv]
  have key : (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re =
      |l τ| * (Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x)).re := by
    rw [htr, ← mul_assoc, re_imaginary_mul_neg_I_div_mul (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ) (Formalism.L2.Theta.xi_zero_im_pos D τ), hl τ]
  rw [key, smul_eq_mul]
  push_cast
  linear_combination (-(4 : ℂ) * Real.pi * ((|l τ| : ℝ) : ℂ) *
    ((Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x)).re : ℂ) * sch ψ A B ν 𝓨 f x) * Complex.I_sq

end GlobalTheory.StdUnnAnnih
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubledStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ), sch ψ A B ν 𝓨 (annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f) = annS B l sB θ τ X (sch ψ A B ν 𝓨 f) := by
  first | exact @GlobalTheory.StdUnnAnnih.annih_sch | exact GlobalTheory.StdUnnAnnih.annih_sch | (intros; apply GlobalTheory.StdUnnAnnih.annih_sch <;> assumption)
end
