module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SectionSumIntegralExpand
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplitW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cw_iota_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) :
    d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have h0 := Krd.zeta_ne R.hζ
  have e := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) (R.at_w w y)
  simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at e
  exact e
theorem law_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have hx : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  have hw := congrArg (d.cw w) hx
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at hw
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  set b := d.b.1.map (d.B.emb w).1 with hb
  set bi := (d.b⁻¹).1.map (d.B.emb w).1 with hbi
  set D := (dbl d.Y.J).map (d.B.emb w).1 with hD
  have hbbi : b * bi = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hbib : bi * b = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ' : biᵀ * Krd.Qc d.n R.ε * bi.map star = D := by
    rw [← hQ]
    calc biᵀ * (bᵀ * D * b.map star) * bi.map star = (b * bi)ᵀ * D * (b * bi).map star := by
          rw [Matrix.transpose_mul, Krd.mapStar_mul]; simp only [Matrix.mul_assoc]
      _ = D := by rw [hbbi, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
  have hZ : d.cw w (inFrame d.b x) = bi * d.cw w (mat2 x) * b := by
    simp only [inFrame, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, hb, hbi]
  rw [hZ]
  exact Krd.conj_unit bi b (d.cw w (mat2 x)) _ _ hbib hQ' hw
theorem cw_inFrame_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : d.cw w (inFrame d.b (1 : d.G)) = 1 := by
  rw [SiegelEisensteinSeries.Grp.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
theorem decompW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (g : d.G) :
    ∃ (x : d.G) (y : GR d.n), g = x * R.ι w y ∧ d.cw w (inFrame d.b x) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  set Zw := d.cw w (inFrame d.b g) with hZw
  let y : GR d.n := Krd.DM.mkG (dZ d.n R.ζ * Zw * dZ d.n R.ζ⁻¹) (Krd.inG_conj R.hζ Zw (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.law_w_k d R w g))
  refine ⟨g * (R.ι w y)⁻¹, y, by rw [inv_mul_cancel_right], ?_⟩
  have hy : d.cw w (inFrame d.b (R.ι w y)) = Zw := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, Krd.DM.mR_mkG]
    simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul]
    rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
  have hinv : Zw * d.cw w (inFrame d.b g⁻¹) = 1 := by
    rw [hZw, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_inFrame_one_k]
  have e : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * Zw = Zw := by
    have e0 : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * d.cw w (inFrame d.b (R.ι w y)) = Zw := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, inv_mul_cancel_right]
    rwa [hy] at e0
  calc d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) = d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * (Zw * d.cw w (inFrame d.b g⁻¹)) := by
        rw [hinv, Matrix.mul_one]
    _ = 1 := by rw [← Matrix.mul_assoc, e, hinv]
theorem commW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases h : w' = w
    · subst h; rw [hx, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y h, Matrix.one_mul, Matrix.mul_one]
  · rw [Krd.fin_mul, Krd.fin_mul, R.off_f]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
theorem finOne_one_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) i j ∈ intHat F E := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact finOne_mem
  · rw [Matrix.one_apply_ne h, smul_zero]; exact zero_mem _
theorem iota_mem_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  have h0 := Krd.zeta_ne R.hζ
  rw [d.ok.stdK]
  refine ⟨fun w' => ?_, fun k' hk' i j => ?_⟩
  · change d.cw w' (inFrame d.b (R.ι w y)) * (d.cw w' (inFrame d.b (R.ι w y)))ᴴ = 1
    by_cases h : w' = w
    · subst h
      have hM : mR y * (mR y)ᴴ = 1 := mul_eq_one_comm.1 hy.2
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, dZ_inv_ct R.hζ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
      calc (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ * ((dZ d.n R.ζ)ᴴ * ((mR y)ᴴ * dZ d.n R.ζ))
          = (dZ d.n R.ζ)ᴴ * (mR y * (dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ) * (mR y)ᴴ) * dZ d.n R.ζ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD, Matrix.mul_one, hM, Matrix.mul_one, ← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
    · rw [R.off_w w w' y h, Matrix.conjTranspose_one, Matrix.mul_one]
  · have hk'' : ∃ z, k' = R.ι w z := by
      rcases hk' with rfl | hk'
      · exact ⟨y, rfl⟩
      · rw [Set.mem_singleton_iff] at hk'
        exact ⟨y⁻¹, by rw [hk', map_inv]⟩
    obtain ⟨z, rfl⟩ := hk''
    have e := congrFun (congrFun (R.off_f w z) i) j
    rw [Matrix.smul_apply, Matrix.smul_apply] at e
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
theorem kSplit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  obtain ⟨x, y, hxy, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w k
  have hkx : (R.ι w y)⁻¹ * k = x := by rw [hxy, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x hx y, inv_mul_cancel_left]
  have hU : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1 := ((d.ok.stdK k).1 hk).1 w
  have hkw : d.cw w (inFrame d.b k) = (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ := by
    rw [hxy, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hx, Matrix.one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, dZ_inv_ct R.hζ]
  have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
  have hD' : (dZ d.n R.ζ)ᴴ * dZ d.n R.ζ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
  have hM : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ := by
    rw [hkw]; simp only [← Matrix.mul_assoc]; rw [hD, Matrix.one_mul, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hU' : (d.cw w (inFrame d.b k))ᴴ * d.cw w (inFrame d.b k) = 1 := mul_eq_one_comm.1 hU
  have hK : InK (mR y) := by
    refine ⟨y.2, ?_⟩
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * (dZ d.n R.ζ)ᴴ) * (dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ)
        = dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * ((dZ d.n R.ζ)ᴴ * dZ d.n R.ζ) * d.cw w (inFrame d.b k)) *
          (dZ d.n R.ζ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD', Matrix.mul_one, hU', Matrix.mul_one, hD]
  refine ⟨y, ?_, by rw [hkx]; exact hx⟩
  exact (d.K).mul_mem ((d.K).inv_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w y hK)) hk
end PositivityTheory.SiegelWeilFormula.KSplitW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRel
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf h
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.nbar_conj' {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ :=
  R.nbar_conj_pf w h
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.frame_diag (y : GR d.n) (A D : Matrix (Fin d.n) (Fin d.n) ℂ) (hy : mR y = Matrix.fromBlocks A 0 0 D) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (inFrame d.b (R.ι w y)).toBlocks₁₁ 0 0 (inFrame d.b (R.ι w y)).toBlocks₂₂ ∧
    d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₁ = A ∧ d.cw w (inFrame d.b (R.ι w y)).toBlocks₂₂ = D ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₁ = 1 ∧ d.cw w' (inFrame d.b (R.ι w y)).toBlocks₂₂ = 1) ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₁ = finOne F • 1 ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₂₂ = finOne F • 1 := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set M := inFrame d.b (R.ι w y) with hM
  have hw : d.cw w M = Matrix.fromBlocks A 0 0 D := by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_diag hζ0]
  have ho : ∀ w', w' ≠ w → d.cw w' M = 1 := fun w' h => R.off_w w w' y h
  have hf : finOne F • M = finOne F • 1 := R.off_f w y
  have o1 := one_blocks (n := d.n) (1 : ℂ)
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  simp only [one_smul] at o1
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
    rw [hf, smul_one_smul]
  have z0 : ∀ w', d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0 := fun w' => Matrix.map_zero _ (map_zero _)
  have e12 : M.toBlocks₁₂ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [z0]
      show (d.cw w' M).toBlocks₁₂ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp
      · rw [ho w' h]; exact o1.2.1
    · show (finOne F • M).toBlocks₁₂ = _
      rw [hf', of.2.1, smul_zero]
  have e21 : M.toBlocks₂₁ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [z0]
      show (d.cw w' M).toBlocks₂₁ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp
      · rw [ho w' h]; exact o1.2.2.1
    · show (finOne F • M).toBlocks₂₁ = _
      rw [hf', of.2.2.1, smul_zero]
  refine ⟨?_, ?_, ?_, fun w' h => ⟨?_, ?_⟩, ?_, ?_⟩
  · conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [e12, e21]
  · show (d.cw w M).toBlocks₁₁ = _
    rw [hw]; simp
  · show (d.cw w M).toBlocks₂₂ = _
    rw [hw]; simp
  · show (d.cw w' M).toBlocks₁₁ = _
    rw [ho w' h]; exact o1.1
  · show (d.cw w' M).toBlocks₂₂ = _
    rw [ho w' h]; exact o1.2.2.2
  · show (finOne F • M).toBlocks₁₁ = _
    rw [hf', of.1, smul_one_smul]
  · show (finOne F • M).toBlocks₂₂ = _
    rw [hf', of.2.2.2, smul_one_smul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ c : ℂ, c ≠ 0 ∧ R.StepOK w (R.ι w y) (fun f u => c * f (Matrix.of u * a)) id := by
  intro y a ha hy
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1
      rw [mul_inv_cancel]; rfl
    have h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]
    calc mR y⁻¹ = (Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y) * mR y⁻¹ := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨hM, -, -, -, -, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y) with hMdef
  set M' := inFrame d.b (R.ι w y⁻¹) with hM'def
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)},
      P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ →
      P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    intro P Q hP hQ hPQ
    rw [hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hPQ
    exact ⟨h1, h4⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM
  obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩
  let u : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  have hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1 := hM
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  refine ⟨c, ?_, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · rw [hc]
    refine mul_ne_zero (Circle.coe_ne_zero _) ?_
    rw [Complex.ofReal_ne_zero]
    exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne _).symm) _).ne'
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ
    exact ⟨ψ, hψ⟩
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]
    have hui : (u⁻¹).1 = M'.toBlocks₂₂ := rfl
    rw [hui]
    set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ
    have hZo : ∀ w', w' ≠ w → d.cw w' Z = 0 := by
      intro w' h
      rw [hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by
        rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]; exact Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,
        Matrix.mul_one, sub_self]
    have hZf : finOne F • Z = 0 := by
      rw [hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, sub_self]
    have hX : X * (M'.toBlocks₂₂)ᵀ = X + Z := by rw [hZ]; abel
    have hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a := by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
      rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, hD', ← Matrix.mul_assoc, mapStar_mulR]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    rw [hloc, hX, hΨ X Z hZo hZf, hc]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isW_eps (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε := by
  have hmem : (mat2 w₀)ᵀ * dbl (incM F d.Y.J) * (mat2 w₀).map (cA σ) = dbl (incM F d.Y.J) := w₀.2
  have hmat : mat2 w₀ = incM F d.b.1 * inFrame d.b w₀ * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  have hc := congrArg (d.cw w) hmem
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, hmat,
    _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h w] at hc
  set P := d.b.1.map (d.B.emb w).1
  set Pi := (d.b⁻¹).1.map (d.B.emb w).1
  set D := (dbl d.Y.J).map (d.B.emb w).1
  set Wc := wM d.n ((ε : ℤ) : ℂ)
  have hPiP : Pi * P = 1 := by
    simp only [Pi, P]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  apply eps_of_unit d.ok.hn ε R.ε
  calc Wcᵀ * Krd.Qc d.n R.ε * Wc.map star
      = (Pi * P)ᵀ * Wcᵀ * (Pᵀ * D * P.map star) * Wc.map star * (Pi * P).map star := by
        rw [hPiP, hQ, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    _ = Pᵀ * ((P * Wc * Pi)ᵀ * D * (P * Wc * Pi).map star) * P.map star := by
        simp only [Matrix.transpose_mul, Krd.mapStar_mul, Matrix.mul_assoc]
    _ = Krd.Qc d.n R.ε := by rw [hc, hQ]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCosM
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem inStabilizer_parabolic_mul {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p γ : d.G} (hp : p ∈ par2 σ d.Y) (hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (p * γ) := by
  intro i
  have hP := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have e1 : ∀ j, inFrame d.b p (Sum.inr i) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP i) j
    simpa [Matrix.toBlocks₂₁] using this
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [e1, hγ _]
theorem inStabilizer_smallerGroupEmbed {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (L.j g) := by
  intro i
  exact (L.j_out g (Sum.inl L.i₀) (by simp) (Sum.inr i)).2.trans (by simp [Matrix.one_apply])
theorem par_of_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {g : G2 σ L.Y} (h : L.j g ∈ par2 σ d.Y) : g ∈ par2 σ L.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k] at h
  refine Matrix.ext fun a c => ?_
  have h1 := congrFun (congrFun h (L.em a)) (L.em c)
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L (inFrame L.b g) (Sum.inr a) (Sum.inl c)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h2
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at h1 ⊢
  rw [← h2]
  exact h1
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepWN
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW_exp (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C : ℂ) (B : d.MF → d.MF), C ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  intro ε w₀ hw
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', hC, -, hfact⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.intFact_k F E σ d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero ε)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero (R.sg w))
  refine ⟨(C : ℂ), fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', by exact_mod_cast hC.ne',
    fun f hf => KW.locFT_sw _ _ hs f hf, fun Ψ hΨ => ⟨?_, ?_⟩⟩
  · intro X Z hZ1 hZ2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z₀ => ?_)
    simp only
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, _root_.PositivityTheory.SiegelWeilFormula.KW.psi_zero_gram_k, mul_one]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
    let Ψ' : Mx F E d.m d.n → ℂ := fun Z =>
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)))) * Ψ Z
    have hΨ' : ∀ X' Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ' (X' + Z) = Ψ' X' := by
      intro X' Z hZ1 hZ2
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
    have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
        R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' := by
      funext Z
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Ψ']
      have h := _root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_right_k d ε X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z))
      rw [add_sub_cancel] at h
      rw [h]
      ring
    rw [e, hfact _ Ψ' hΨ']
    have e2 : ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w Z.2, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_zero_k, sub_zero]
    rw [e2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KW.kernel_k R w ε X]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitSectionIntegral
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def th_k (T : nF σ d.Y d.b) (β : nA σ d.Y d.b) : ℂ := d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
def th'_k (T' : nF σ L.Y L.b) (β : nA σ L.Y L.b) : ℂ :=
  d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1))))
theorem second_orbit_section_integral {f : d.G → ℂ} {s₁ z : ℂ} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)} {T : nF σ d.Y d.b}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x =
        ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) ∧
      ∫⁻ p, ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ
        ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) < ⊤ := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  let g : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} → (Fin L.n → AE F E) × nA σ d.Y d.b → ℂ :=
    fun q => _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
  have hgi : ∀ q, Integrable (g q) μ := fun q => hi q.1
  have hgs : Summable fun q => ∫ p, ‖g q p‖ ∂μ := hs.subtype _
  have htm : ∀ q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x = ∫ p, g q p ∂μ := by
    intro q
    rw [hμ, integral_prod _ (hgi q)]
    rfl
  constructor
  · unfold _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection
    simp_rw [htm]
    rw [(hasSum_integral_of_summable_integral_norm hgi hgs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [g, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k]
    rw [tsum_mul_right]
  · have hm : ∀ q, AEMeasurable (fun p => ‖g q p‖ₑ) μ := fun q => (hgi q).aemeasurable.enorm
    have e1 : ∫⁻ p, ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂μ =
        ∑' q, ENNReal.ofReal (∫ p, ‖g q p‖ ∂μ) := by
      rw [show (fun p => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
          ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ) = fun p => ∑' q, ‖g q p‖ₑ from rfl,
        lintegral_tsum hm]
      exact tsum_congr fun q => (ofReal_integral_norm_eq_lintegral_enorm (hgi q)).symm
    rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg fun p => norm_nonneg _) hgs]
    exact ENNReal.ofReal_lt_top
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCosB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem blockH_form_k {ε : ℤˣ} {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hM : Mᵀ * QE d.n ε * M.map σ = QE d.n ε)
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0) :
    (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L))ᵀ * QE L.n ε * (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L)).map σ = QE L.n ε := by
  have hQx : ∀ r, r ≠ Sum.inr L.i₀ → QE (E := E) d.n ε r (Sum.inl L.i₀) = 0 := by
    intro r hr
    rcases r with i | i
    · simp [QE]
    · have hi : i ≠ L.i₀ := fun h => hr (by rw [h])
      simp [QE, Matrix.one_apply, hi]
  have hQx' : ∀ a', QE (E := E) d.n ε (Sum.inl L.i₀) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = 0 := by
    intro a'
    rcases a' with k | k
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k)]
  have hne : ∀ a', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' ≠ Sum.inr L.i₀ := by
    intro a'
    rcases a' with k | k
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k]
  have hQQ : ∀ a' c', QE (E := E) d.n ε (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = QE L.n ε a' c' := by
    intro a' c'
    rcases a' with k | k <;> rcases c' with k' | k' <;> simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, L.inj.eq_iff]
  refine Matrix.ext fun a c => ?_
  have h := congrFun (congrFun hM (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c)
  rw [← hQQ, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Finset.sum_mul]
  symm
  rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
    · exact Finset.sum_congr rfl fun a' _ => by rw [hQQ]
    · intro r hr
      have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · rw [hQx', mul_zero, zero_mul]
      · rw [hy _ (hne a), zero_mul, zero_mul]
  · intro s hs
    have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = Sum.inr L.i₀
      · subst hr
        rw [hy _ (hne a), zero_mul, zero_mul]
      · rw [hQx r hr, mul_zero, zero_mul]
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [hy _ (hne c), map_zero, mul_zero]
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCosA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
open Matrix
theorem padE_emS_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = N a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_left h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padE_out_row_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padE_out_col_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem nq_E_k {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0)
    {H' : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E} (hH : M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * H' = 1) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
  have hxo : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl L.i₀ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L L.i₀ rfl
  have hyo : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr L.i₀ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L L.i₀ rfl
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · have : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') k (Sum.inl L.i₀) = (M * (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) k (Sum.inl L.i₀) := by
      simp only [Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_out_col_k L H' _ hxo]
    rw [Matrix.sub_apply, this, Matrix.mul_one, hx k, sub_self]
  · have hl : ∃ c', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c' = l := by
      by_contra hc
      rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hc with h | h
      · exact hlx h
      · exact hly h
    obtain ⟨c', rfl⟩ := hl
    have hsum : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') k (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = ∑ a', M k (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') * H' a' c' := by
      rw [Matrix.mul_apply, sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
      · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_emS_k]
      · intro m hm
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_out_row_k L H' (fun h => hm (by obtain ⟨a, ha⟩ := h; exact ⟨a, ha⟩)), Matrix.one_apply_ne, mul_zero]
        rintro rfl
        exact hm ⟨c', rfl⟩
    rw [Matrix.sub_apply, hsum]
    by_cases hk : ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = k
    · obtain ⟨a, rfl⟩ := hk
      have := congrFun (congrFun hH a) c'
      rw [Matrix.mul_apply] at this
      simp only [Matrix.submatrix_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp [(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L).eq_iff]
    · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hk with h | h
      · exact (hkx h).elim
      · have h' : k = Sum.inr L.i₀ := h
        subst h'
        rw [Finset.sum_eq_zero fun a' _ => by rw [hy _ (fun he => hyo ⟨a', he⟩), zero_mul], Matrix.one_apply_ne, sub_self]
        intro he
        exact hyo ⟨c', he.symm⟩
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepW
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepWPf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C s : ℂ) (B : d.MF → d.MF), s ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  intro ε w₀ hw
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', -, -, hfact⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.intFact_k F E σ d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero ε)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero (R.sg w))
  refine ⟨(C : ℂ), _, fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', hs,
    fun f hf => KW.locFT_sw _ _ hs f hf, fun Ψ hΨ => ⟨?_, ?_⟩⟩
  · intro X Z hZ1 hZ2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z₀ => ?_)
    simp only
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, _root_.PositivityTheory.SiegelWeilFormula.KW.psi_zero_gram_k, mul_one]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
    let Ψ' : Mx F E d.m d.n → ℂ := fun Z =>
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)))) * Ψ Z
    have hΨ' : ∀ X' Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ' (X' + Z) = Ψ' X' := by
      intro X' Z hZ1 hZ2
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
    have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
        R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' := by
      funext Z
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Ψ']
      have h := _root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_right_k d ε X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z))
      rw [add_sub_cancel] at h
      rw [h]
      ring
    rw [e, hfact _ Ψ' hΨ']
    have e2 : ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w Z.2, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_zero_k, sub_zero]
    rw [e2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KW.kernel_k R w ε X]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C s : ℂ) (B : d.MF → d.MF), s ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B :=
  R.stepW_pf w hT hA
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
theorem ratV_inc_k {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
theorem neg_incV_k (v : Fin L.n → E) : -GlobalTheory.ThK.incV F v = GlobalTheory.ThK.incV F (-v) := funext fun i => by simp [GlobalTheory.ThK.incV]
def unipotentFirstMatrix (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (v j)
theorem Au_inc_k (v : Fin L.n → E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (GlobalTheory.ThK.incV F v) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]
theorem Apc_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by
  have h1 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ = 1 := mul_eq_one_comm.1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU u))
  have h2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ = 1 := by rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.transpose_one]
  calc (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
theorem Ap_inc_k (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v) = incM F M := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm, Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) ?_⟩
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm)).map (cA σ)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k, kunf.incM_map_cA, Matrix.map_map, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl
theorem uM_rat_k (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) 0 0 M) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hM]
  simp [incM, Matrix.fromBlocks_map]
theorem cj_rat_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v) * T * M, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hT, hM, kunf.incM_mul', kunf.incM_mul']
theorem mul_Au_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]
theorem AuT_mul_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]
theorem trace_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = T.1.1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.mul_Au_k _ (fun a => (hT.1 a).2) _
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d)
    show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.AuT_mul_k _ (fun b => by simp [(hT.1 b).1]) _
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end
