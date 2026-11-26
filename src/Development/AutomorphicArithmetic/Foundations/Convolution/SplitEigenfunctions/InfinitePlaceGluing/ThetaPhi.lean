module

public import Development.AutomorphicArithmetic.WhittakerHecke.NormThetaSeriesSiegelSetLeExp
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
public import Development.AutomorphicArithmetic.WhittakerHecke.IsCompactIntegralIdeleUnitsAndAbsEqOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesPoissonFunctionalEquation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompMulVec
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.LtrFourier

noncomputable section

theorem map_mulVec_fin {k : Type} [Field k] [NumberField k] {n : ℕ} (A : GL (Fin n) 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : Fin n → 𝔸[k] => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := Fin n) := by
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi (tInv (A⁻¹))
  have hdet : Matrix.GeneralLinearGroup.det (tInv (A⁻¹)) = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    change (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ.det = _
    rw [Matrix.det_transpose, inv_inv]
  have hfun : (fun x : Fin n → 𝔸[k] =>
      x ᵥ* ((tInv (A⁻¹) : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])) =
      fun x => (A : Matrix (Fin n) (Fin n) 𝔸[k]) *ᵥ x := by
    funext x
    change x ᵥ* (((A⁻¹)⁻¹ : GL (Fin n) 𝔸[k]) : Matrix (Fin n) (Fin n) 𝔸[k])ᵀ = _
    rw [inv_inv]
    exact Matrix.vecMul_transpose _ x
  rwa [hdet, hfun] at hmap

theorem map_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) :
    (adeleMeasurePi k).map (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      ENNReal.ofReal ((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ •
        adeleMeasurePi k (ι := ι) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let P : GL (Fin (Fintype.card ι)) 𝔸[k] :=
    ⟨(A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv]⟩
  have hdet : Matrix.GeneralLinearGroup.det P = Matrix.GeneralLinearGroup.det A := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_submatrix_equiv_self _ _
  have h1 : MeasurePreserving (fun x : ι → 𝔸[k] => x ∘ e.symm) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e.symm
  have h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[k] => x ∘ e) (adeleMeasurePi k)
      (adeleMeasurePi k) := GroundTheory.Heights₂.Theta.measurePreserving_comp_equiv (adeleMeasure k) e
  have hP : Measurable fun x : Fin (Fintype.card ι) → 𝔸[k] =>
      (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hfun : (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) =
      (fun x => x ∘ e) ∘
        (fun x => (P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝔸[k]) *ᵥ x) ∘
          (fun x => x ∘ e.symm) := by
    funext x
    simp only [Function.comp_apply]
    change _ = ((A : Matrix ι ι 𝔸[k]).submatrix e.symm e.symm *ᵥ (x ∘ e.symm)) ∘ e
    have hx : (x ∘ e.symm) ∘ e = x := by
      funext j
      simp
    rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, hx]
    funext i
    simp
  rw [hfun, ← Measure.map_map h3.measurable (hP.comp h1.measurable),
    ← Measure.map_map hP h1.measurable, h1.map_eq, map_mulVec_fin P, hdet, Measure.map_smul,
    h3.map_eq]
  exact h3.measurable.aemeasurable

def mulVecHomeo {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : GL ι 𝔸[k]) : (ι → 𝔸[k]) ≃ₜ (ι → 𝔸[k]) where
  toFun x := (A : Matrix ι ι 𝔸[k]) *ᵥ x
  invFun x := ((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem integral_comp_mulVec {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : GL ι 𝔸[k]) (f : (ι → 𝔸[k]) → ℂ) :
    ∫ x, f ((A : Matrix ι ι 𝔸[k]) *ᵥ x) ∂adeleMeasurePi k =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) *
        ∫ x, f x ∂adeleMeasurePi k := by
  have hemb : MeasurableEmbedding (fun x : ι → 𝔸[k] => (A : Matrix ι ι 𝔸[k]) *ᵥ x) :=
    (mulVecHomeo A).measurableEmbedding
  rw [← hemb.integral_map, map_mulVec, integral_smul_measure, ENNReal.toReal_ofReal
      (inv_nonneg.2 (ideleModule k (Matrix.GeneralLinearGroup.det A)).2.le),
    Complex.real_smul, Complex.ofReal_inv]

theorem adelicFourierPi_ltr : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ), adelicFourierPi k (ltr A F) =
      (((ideleModule k (Matrix.GeneralLinearGroup.det A) : ℝ))⁻¹ : ℂ) •
        ltr (tInv A) (adelicFourierPi k F) := by
  intro k _ _ ι _ _ A F
  funext y
  have h := integral_comp_mulVec A (fun z => F z *
    (adelicChar k (∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i) : ℂ))
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  have hp : ∀ z : ι → 𝔸[k], ∑ i, (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) i * y i =
      ∑ i, z i * (((tInv A : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ y) i := by
    intro z
    change (((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ z) ⬝ᵥ y =
      z ⬝ᵥ ((((A⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]))ᵀ *ᵥ y)
    rw [Matrix.mulVec_transpose, dotProduct_comm _ y, Matrix.dotProduct_mulVec,
      dotProduct_comm]
  simp only [hp] at h
  simpa only [adelicFourierPi, ltr, Pi.smul_apply, smul_eq_mul] using h

end

end GlobalTheory.CompanionTheory.LtrFourier
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable abbrev rv (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ := fun i => rt (ξ i)

private noncomputable abbrev sc (a : (A ℚ)ˣ) : GL (Fin 2) (A ℚ) := Matrix.GeneralLinearGroup.scalar (Fin 2) a

private theorem tInv_tInv (x : GL (Fin 2) (A ℚ)) : PositivityTheory.RgEis.tInv (PositivityTheory.RgEis.tInv x) = x := by
  apply Units.ext
  show ((x : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ)ᵀ = x
  rw [Matrix.transpose_transpose]

private theorem tInv_sc (a : (A ℚ)ˣ) : PositivityTheory.RgEis.tInv (sc a) = sc a⁻¹ := by
  apply Units.ext
  show (((sc a)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  rw [← map_inv]
  have e : ((sc a⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = Matrix.diagonal fun _ => ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    rfl
  rw [e, Matrix.diagonal_transpose]

private theorem sc_mulVec (a : (A ℚ)ˣ) (x : GL (Fin 2) (A ℚ)) (v : Fin 2 → A ℚ) :
    ((sc a * x : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ v =
      fun j => (a : A ℚ) * ((x : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ v) j := by
  funext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem det_sc (a : (A ℚ)ˣ) : Matrix.GeneralLinearGroup.det (sc a) = a * a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [Matrix.det_fin_two, sq]

private theorem det_tInv (x : GL (Fin 2) (A ℚ)) :
    Matrix.GeneralLinearGroup.det (PositivityTheory.RgEis.tInv x) = (Matrix.GeneralLinearGroup.det x)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

private theorem iy_inv (y : ℝ) (h : y ≠ 0) : iy y⁻¹ = (iy y)⁻¹ := by
  unfold iy
  rw [dite_eq_right h, dite_eq_right (inv_ne_zero h), ← map_inv]
  congr 1
  apply Units.ext
  funext _
  rfl

private theorem ab_iy (y : ℝ) (h : y ≠ 0) : ab (iy y) = |y| := by
  unfold ab iy
  rw [dite_eq_right h]
  have := GlobalTheory.HenQ.DetSplit.ideleModule_infId (K := ℚ) ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩
  rw [this]
  simp

private theorem tsum_split {f : (Fin 2 → ℚ) → ℂ} (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + ∑' ξ : Rw ℚ, f ξ.1 := by
  rw [← hf.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton]
  rfl

private theorem poisson_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) (a : (A ℚ)ˣ)
    (h : GL (Fin 2) (A ℚ)) :
    Summable (fun ξ : Fin 2 → ℚ => Φ fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j) ∧
    Summable (fun ξ : Fin 2 → ℚ => adelicFourierPi ℚ Φ fun j =>
      ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j) ∧
    ∑' ξ : Fin 2 → ℚ, Φ (fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j) =
      ((ab (a * a * Matrix.GeneralLinearGroup.det h) : ℝ) : ℂ)⁻¹ * ∑' ξ : Fin 2 → ℚ, adelicFourierPi ℚ Φ fun j =>
        ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j := by
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 2) (A ℚ), B = sc a * PositivityTheory.RgEis.tInv h⁻¹ := ⟨_, rfl⟩
  have hl := GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem hΦ B
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi hl
  have hf := GlobalTheory.CompanionTheory.LtrFourier.adelicFourierPi_ltr B Φ
  have hdet : Matrix.GeneralLinearGroup.det B = a * a * Matrix.GeneralLinearGroup.det h := by
    rw [hB, map_mul, det_sc, det_tInv, map_inv, inv_inv]
  have e1 : ∀ ξ : Fin 2 → ℚ, PositivityTheory.He2M1.ltr B Φ (fun i => algebraMap ℚ (A ℚ) (ξ i)) =
      Φ fun j => (a : A ℚ) * (rv ξ ᵥ* h.val) j := by
    intro ξ
    show Φ ((B : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ _) = _
    congr 1
    rw [hB, sc_mulVec]
    funext j
    have e : ((PositivityTheory.RgEis.tInv h⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = (h.val)ᵀ := by
      show (((h⁻¹)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
      rw [inv_inv]
    rw [e, Matrix.mulVec_transpose]
  have hBi : PositivityTheory.RgEis.tInv B = sc a⁻¹ * h⁻¹ := by
    rw [hB, map_mul, tInv_sc, tInv_tInv]
  have e2 : ∀ ξ : Fin 2 → ℚ, PositivityTheory.He2M1.ltr (PositivityTheory.RgEis.tInv B) (adelicFourierPi ℚ Φ) (fun i => algebraMap ℚ (A ℚ) (ξ i)) =
      adelicFourierPi ℚ Φ fun j => ((a⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ ᵥ* (PositivityTheory.RgEis.tInv h).val) j := by
    intro ξ
    show adelicFourierPi ℚ Φ (((PositivityTheory.RgEis.tInv B : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) *ᵥ _) = _
    congr 1
    rw [hBi, sc_mulVec]
    funext j
    have e : ((PositivityTheory.RgEis.tInv h : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) =
        ((h⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ := rfl
    rw [e, Matrix.vecMul_transpose]
  have hc : ((ab (Matrix.GeneralLinearGroup.det B) : ℝ) : ℂ)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < ab (Matrix.GeneralLinearGroup.det B) := (IdeleGroup.ideleModule ℚ _).2
    exact inv_ne_zero (Complex.ofReal_ne_zero.2 this.ne')
  rw [hf] at h2 h3
  simp only [Pi.smul_apply, smul_eq_mul, e1, e2] at h1 h2 h3
  rw [← hdet]
  refine ⟨h1.of_norm, (summable_mul_left_iff hc).1 h2.of_norm, ?_⟩
  rw [h3, tsum_mul_left]
  rfl

private theorem tInv_dM (u : (A ℚ)ˣ) : PositivityTheory.RgEis.tInv (dM u) = dM u⁻¹ := by
  apply Units.ext
  show (((dM u)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  have e : (((dM u)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![1, 0; 0, ((u⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [e]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

private theorem tInv_gl (g : G1 ℚ) : PositivityTheory.RgEis.tInv (gl g) = gl (wW ℚ) * (gl g * (gl (wW ℚ))⁻¹) := by
  have e1 : (gl g)⁻¹ = gl g⁻¹ := (map_inv Matrix.SpecialLinearGroup.toGL g).symm
  have e2 : (gl (wW ℚ))⁻¹ = gl (wW ℚ)⁻¹ := (map_inv Matrix.SpecialLinearGroup.toGL (wW ℚ)).symm
  apply Units.ext
  show (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))ᵀ = _
  have hw : ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, 1; -1, 0] := rfl
  have hwi : (((gl (wW ℚ))⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, -1; 1, 0] := by
    rw [e2]
    show Matrix.adjugate (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (A ℚ)) = _
    rw [Matrix.adjugate_fin_two]
    simp
  have hgi : (((gl g)⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
    rw [e1]
    show Matrix.adjugate g.1 = _
    rw [Matrix.adjugate_fin_two]
  have hg : ((gl g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![g 0 0, g 0 1; g 1 0, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Units.val_mul, Units.val_mul, hw, hwi, hgi, hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem tInv_h (g : G1 ℚ) (u : (A ℚ)ˣ) :
    PositivityTheory.RgEis.tInv (gl g * dM u) = gl (wW ℚ) * (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
  rw [map_mul, tInv_gl, tInv_dM]
  simp only [mul_assoc]

private theorem det_h (g : G1 ℚ) (u : (A ℚ)ˣ) : Matrix.GeneralLinearGroup.det (gl g * dM u) = u := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul]
  have : ((gl g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)).det = 1 := g.det_coe
  rw [this, one_mul]
  simp [dM, Matrix.det_fin_two]

private def eW : Rw ℚ ≃ Rw ℚ where
  toFun r := ⟨![-(r.1 1), r.1 0], fun h => r.2 (by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1])⟩
  invFun r := ⟨![r.1 1, -(r.1 0)], fun h => r.2 (by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    ext i
    fin_cases i <;> simp [h0, h1])⟩
  left_inv r := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv r := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp

private theorem rv_w (ξ : Fin 2 → ℚ) :
    rv ξ ᵥ* ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = rv ![-(ξ 1), ξ 0] := by
  have hw : ((gl (wW ℚ) : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) = !![0, 1; -1, 0] := rfl
  rw [hw]
  funext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, UpperTheory.ConvolutionTheory.R2.rt]
  exact (map_neg (algebraMap ℚ (A ℚ)) (ξ 1)).symm

theorem UpperTheory.thetaSeries_poisson_functional_equation :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∃ Ψ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (g : G1 ℚ) (u : (A ℚ)ˣ), ab u = 1 →
        ThR Φ t (gl g * dM u) = -Φ 0 + (Real.exp (-(2 * t)) : ℂ) * Ψ 0 + (Real.exp (-(2 * t)) : ℂ) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
  intro Φ hΦ
  refine ⟨adelicFourierPi ℚ Φ, adelicFourierPi_mem_schwartzBruhatPi hΦ, ?_⟩
  intro t g u hu
  have hne : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  obtain ⟨s1, s2, s3⟩ := poisson_row hΦ (iy (Real.exp t)) (gl g * dM u)
  rw [tsum_split s1, tsum_split s2] at s3
  have hz : rv 0 = 0 := by
    funext i
    show UpperTheory.ConvolutionTheory.R2.rt ((0 : Fin 2 → ℚ) i) = 0
    simp [UpperTheory.ConvolutionTheory.R2.rt]
  have z1 : (fun j => ((iy (Real.exp t) : (A ℚ)ˣ) : A ℚ) * (rv 0 ᵥ* (gl g * dM u).val) j) = 0 := by
    funext j
    simp [hz]
  have z2 : (fun j => (((iy (Real.exp t))⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv 0 ᵥ* (PositivityTheory.RgEis.tInv (gl g * dM u)).val) j) = 0 := by
    funext j
    simp [hz]
  have hd : ab (iy (Real.exp t) * iy (Real.exp t) * Matrix.GeneralLinearGroup.det (gl g * dM u)) = Real.exp (2 * t) := by
    rw [det_h, UpperTheory.ConvolutionTheory.R2.ab_mul, UpperTheory.ConvolutionTheory.R2.ab_mul, hu, ab_iy _ hne, abs_of_pos (Real.exp_pos t), mul_one, ← Real.exp_add, two_mul]
  have hR : ∑' ξ : Rw ℚ, adelicFourierPi ℚ Φ (fun j =>
      (((iy (Real.exp t))⁻¹ : (A ℚ)ˣ) : A ℚ) * (rv ξ.1 ᵥ* (PositivityTheory.RgEis.tInv (gl g * dM u)).val) j) =
      ThR (adelicFourierPi ℚ Φ) (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) := by
    unfold ThR
    refine Eq.trans ?_ (eW.tsum_eq _)
    refine tsum_congr fun ξ => ?_
    congr 1
    funext j
    rw [tInv_h, Units.val_mul, ← Matrix.vecMul_vecMul, rv_w, Real.exp_neg, iy_inv _ hne]
    rfl
  have hL : ∑' ξ : Rw ℚ, Φ (fun j => ((iy (Real.exp t) : (A ℚ)ˣ) : A ℚ) * (rv ξ.1 ᵥ* (gl g * dM u).val) j) =
      ThR Φ t (gl g * dM u) := rfl
  simp only [z1, z2, hR, hL, hd] at s3
  have hexp : ((Real.exp (-(2 * t)) : ℝ) : ℂ) = ((Real.exp (2 * t) : ℝ) : ℂ)⁻¹ := by
    rw [Real.exp_neg, Complex.ofReal_inv]
  rw [hexp]
  linear_combination s3
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.NormIntegralUnitaryHeckeCharFundDomainLe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le :
    ∀ (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (f : IdeleGroup ℚ → G1 ℚ → ℂ) (B : ℝ), (∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) → Measurable (Function.uncurry f) →
        (∀ u ∈ UU, ∀ g, ‖f u g‖ ≤ B) →
        (∀ u ∈ UU, IntegrableOn (f u) M.D M.μ) ∧ Integrable (fun u => ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ) U.υ ∧
          ‖∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ ∂U.υ‖ ≤ B * M.μ.real M.D := by
  intro M U χ f B hχ hf hB
  haveI := U.prob
  have hD : M.μ M.D < ⊤ := UpperTheory.ConvolutionTheory.R2.M.volD ℚ M
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hD⟩
  have hfu : ∀ u, Measurable (f u) := fun u => hf.comp measurable_prodMk_left
  have hae : ∀ᵐ u ∂U.υ, u ∈ (UU : Set (A ℚ)ˣ) := mem_ae_iff.mpr U.supp
  have hI : StronglyMeasurable (fun u => ∫ g in M.D, f u g ∂M.μ) :=
    (hf.stronglyMeasurable).integral_prod_right
  have hχm : Measurable (fun u : IdeleGroup ℚ => ((χ.1 u : ℂˣ) : ℂ)) :=
    (Units.continuous_val.comp χ.2.1).measurable
  have hbd : ∀ᵐ u ∂U.υ, ‖((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D, f u g ∂M.μ‖ ≤ B * M.μ.real M.D := by
    filter_upwards [hae] with u hu
    rw [norm_mul, hχ, one_mul]
    exact norm_setIntegral_le_of_norm_le_const hD (fun g _ => hB u hu g)
  refine ⟨fun u hu => Integrable.of_bound (hfu u).aestronglyMeasurable B (Eventually.of_forall (hB u hu)), ?_, ?_⟩
  · exact Integrable.of_bound (hχm.aestronglyMeasurable.mul hI.aestronglyMeasurable) _ hbd
  · simpa using norm_integral_le_of_norm_le_const hbd
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.MeasurableThetaSeriesCompContinuous
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem sb_le : schwartzBruhatPi (K := ℚ) (ι := Fin 2) ≤ GroundTheory.Automorphic.Adele2.schwartzBruhat2 ℚ := by
  refine Submodule.span_le.mpr ?_
  rintro F ⟨φ, g, hg, rfl⟩
  exact GroundTheory.Automorphic.Adele2.schwartzBruhatTensor2_mem φ
    (show _ ∧ _ from (mem_finiteSchwartzBruhatPi ℚ).mp hg)

private theorem cont_iy : Continuous fun t : ℝ => iy (Real.exp t) := by
  let u : ℝ → (TR.Rinf ℚ)ˣ := fun t => ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
    funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t), funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
  have hu : Continuous u := by
    refine Units.continuous_iff.mpr ⟨continuous_pi fun _ => Real.continuous_exp, continuous_pi fun _ => ?_⟩
    exact Real.continuous_exp.inv₀ Real.exp_ne_zero
  have e : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
    funext t
    exact dite_eq_right (Real.exp_ne_zero t)
  rw [e]
  exact (TR.continuous_infId ℚ).comp hu

private theorem summable_row {Φ : (Fin 2 → A ℚ) → ℂ} (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (a : (A ℚ)ˣ) (g : GL (Fin 2) (A ℚ)) :
    Summable fun ξ : Rw ℚ => Φ fun j => (a : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* g.val) j := by
  have hs := (GroundTheory.Automorphic.Adele2.poisson_rightTranslate (sb_le hΦ)
    (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g)).1.of_norm
  have hv : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ))
      = (a : A ℚ) • g.val := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_apply]
  refine (hs.comp_injective (Subtype.val_injective (p := fun r : Fin 2 → ℚ => r ≠ 0))).congr fun ξ => ?_
  simp only [Function.comp_apply]
  rw [hv, Matrix.vecMul_smul]
  rfl

theorem UpperTheory.measurable_thetaSeries_comp_continuous :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
        (τ : X → ℝ) (h : X → GL (Fin 2) (A ℚ)), Continuous τ → Continuous h → Measurable fun x => ThR Φ (τ x) (h x) := by
  intro Φ hΦ X _ _ _ τ h hτ hh
  have hc := continuous_of_mem_schwartzBruhatPi hΦ
  have ha : Continuous fun x => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) :=
    Units.continuous_val.comp (cont_iy.comp hτ)
  have hg : Continuous fun x => (h x).val := Units.continuous_val.comp hh
  have hterm : ∀ ξ : Rw ℚ, Continuous fun x =>
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j := fun ξ =>
    hc.comp (continuous_pi fun j => ha.mul
      ((continuous_apply j).comp (continuous_const.matrix_vecMul hg)))
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Rw ℚ)))
    (f := fun (s : Finset (Rw ℚ)) x => ∑ ξ ∈ s,
      Φ fun j => ((iy (Real.exp (τ x)) : (A ℚ)ˣ) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (h x).val) j)
    (fun s => (continuous_finsetSum s fun ξ _ => hterm ξ).measurable) ?_
  exact tendsto_pi_nhds.mpr fun x => (summable_row hΦ (iy (Real.exp (τ x))) (h x)).hasSum
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.DifferentiableIntegralExpMulOfRapidDecay
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.differentiable_integral_exp_mul_of_rapid_decay :
    ∀ I : ℝ → ℂ, AEStronglyMeasurable I volume → (∀ n : ℕ, ∃ B : ℝ, ∀ t, ‖I t‖ ≤ B * Real.exp (-((n : ℝ) * |t|))) →
        Differentiable ℂ fun s : ℂ => ∫ t : ℝ, Complex.exp (2 * s * t) * I t := by
  intro I hI hdec s₀
  have hexp : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_exp_Iic (0 : ℝ)).congr_fun (fun t ht => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.mp ht)]
    · refine (exp_neg_integrableOn_Ioi 0 (zero_lt_one (α := ℝ))).congr_fun (fun t ht => ?_)
        measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.mp ht)]
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|s₀.re| + 1) + 2)
  obtain ⟨B, hB⟩ := hdec n
  have hB0 : 0 ≤ B := by
    have h := hB 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have key : ∀ s : ℂ, s ∈ Metric.ball s₀ 1 → ∀ t : ℝ,
      ‖Complex.exp (2 * s * t)‖ * ‖I t‖ ≤ B * Real.exp (-(2 * |t|)) := by
    intro s hs t
    have hre : |s.re| ≤ |s₀.re| + 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h3 := abs_sub_abs_le_abs_sub s.re s₀.re
      rw [Complex.sub_re] at h1
      linarith
    have hn1 : ‖Complex.exp (2 * s * t)‖ = Real.exp (2 * s.re * t) := by
      rw [Complex.norm_exp]
      simp
    have ht : 2 * s.re * t ≤ 2 * (|s₀.re| + 1) * |t| := by
      have h1 : s.re * t ≤ |s.re| * |t| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 : |s.re| * |t| ≤ (|s₀.re| + 1) * |t| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg t)
      linarith
    have hnt : (2 * (|s₀.re| + 1) + 2) * |t| ≤ (n : ℝ) * |t| :=
      mul_le_mul_of_nonneg_right hn.le (abs_nonneg t)
    calc ‖Complex.exp (2 * s * t)‖ * ‖I t‖
        ≤ Real.exp (2 * (|s₀.re| + 1) * |t|) * (B * Real.exp (-((n : ℝ) * |t|))) := by
          rw [hn1]
          exact mul_le_mul (Real.exp_le_exp.mpr ht) (hB t) (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (2 * (|s₀.re| + 1) * |t| + -((n : ℝ) * |t|)) := by
          rw [Real.exp_add]
          ring
      _ ≤ B * Real.exp (-(2 * |t|)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0
          linarith
  have hcont : ∀ s : ℂ, Continuous fun t : ℝ => Complex.exp (2 * s * t) := fun s => by
    fun_prop
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (2 * s * t) * I t) volume :=
    fun s => (hcont s).aestronglyMeasurable.mul hI
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) * I t) volume := by
    have hc : Continuous fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul hI
  have hF_int : Integrable (fun t : ℝ => Complex.exp (2 * s₀ * t) * I t) volume := by
    refine (hexp.const_mul B).mono' (hmeas s₀) (ae_of_all _ fun t => ?_)
    rw [norm_mul]
    refine (key s₀ (Metric.mem_ball_self one_pos) t).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0)
    linarith [abs_nonneg t]
  have h_bound : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖ ≤ 2 * B * Real.exp (-|t|) := by
    refine ae_of_all _ fun t s hs => ?_
    have hk := key s hs t
    have hnorm : ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖
        = 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [Complex.norm_ofNat]
      ring
    have habs : |t| ≤ Real.exp |t| := by
      linarith [Real.add_one_le_exp |t|]
    rw [hnorm]
    calc 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖)
        ≤ 2 * Real.exp |t| * (B * Real.exp (-(2 * |t|))) :=
          mul_le_mul (by linarith) hk (by positivity) (by positivity)
      _ = 2 * B * (Real.exp |t| * Real.exp (-(2 * |t|))) := by ring
      _ = 2 * B * Real.exp (-|t|) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have h_diff : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt (fun x : ℂ => Complex.exp (2 * x * t) * I t)
        ((2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t) s := by
    refine ae_of_all _ fun t s _ => ?_
    have h1 : HasDerivAt (fun x : ℂ => 2 * x * (t : ℂ)) (2 * (t : ℂ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).mul_const (t : ℂ)
    have h2 := h1.cexp.mul_const (I t)
    rwa [show Complex.exp (2 * s * t) * (2 * (t : ℂ)) * I t
        = (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t by ring] at h2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t : ℝ => 2 * B * Real.exp (-|t|))
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (2 * s * t) * I t)
    (F' := fun (s : ℂ) (t : ℝ) => (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t)
    (Metric.ball_mem_nhds s₀ one_pos) (Eventually.of_forall hmeas) hF_int hmeas' h_bound
    (hexp.const_mul (2 * B)) h_diff).2.differentiableAt
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.NormAdmissibleBaseChangeSiegelSetLe
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.EmbeddingGeneralLinear

variable {E : Type} [Field E] [NumberField E]

private theorem ab_emb (D : Dat ℚ E) (a : (A ℚ)ˣ) :
    ab (ideleEmbedding ℚ E a : (A E)ˣ) = ab a ^ 2 := by
  have hfr : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  have h := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (L := E)
    (ideleEmbedding ℚ E a)
  rw [ideleNorm_ideleEmbedding, hfr, map_pow] at h
  simp only [ab]
  rw [← h]
  rfl

private theorem em_gl (b : A ℚ) (a : (A ℚ)ˣ) :
    em E (gl (nU b * mD a)) =
      gl (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ)) := by
  have hinv : (((ideleEmbedding ℚ E a : (A E)ˣ)⁻¹ : (A E)ˣ) : A E) =
      AdeleBaseChange.adeleMap ℚ E ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    rw [← map_inv]; rfl
  apply Units.ext
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((nU b * mD a : G1 ℚ).1 i j) =
    (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ) : G1 E).1 i j
  have hL : (nU b * mD a : G1 ℚ).1 = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  have hR : (nU (AdeleBaseChange.adeleMap ℚ E b) * mD (ideleEmbedding ℚ E a : (A E)ˣ) : G1 E).1 =
      !![1, AdeleBaseChange.adeleMap ℚ E b; 0, 1] *
        !![AdeleBaseChange.adeleMap ℚ E (a : A ℚ), 0; 0, AdeleBaseChange.adeleMap ℚ E ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := by
    rw [← hinv]; rfl
  rw [hL, hR]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem continuous_em : Continuous (em E) :=
  Continuous.units_map _ (continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap)

end UpperTheory.EmbeddingGeneralLinear

open UpperTheory.EmbeddingGeneralLinear in
theorem UpperTheory.norm_admissible_baseChange_siegelSet_le :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ r : ℕ,
        ∃ B : ℝ, ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a → ‖φ (em E (gl (nU b * mD a) * k))‖ ≤ B * (ab a)⁻¹ ^ r := by
  intro E _ _ D ω φ hφ C hC c hc r
  obtain ⟨B, hB⟩ := hφ.decay (em E '' C) (hC.image continuous_em) (c ^ 2) (by positivity) r
  refine ⟨|B| * c⁻¹ ^ r, fun b a k hk hca => ?_⟩
  have ha : 0 < ab a := hc.trans_le hca
  have h1 := hB (AdeleBaseChange.adeleMap ℚ E b) (ideleEmbedding ℚ E a : (A E)ˣ) (em E k) ⟨k, hk, rfl⟩
    (by rw [ab_emb D]; gcongr)
  rw [ab_emb D] at h1
  rw [map_mul, em_gl]
  refine h1.trans ?_
  have h2 : ((ab a ^ 2)⁻¹) ^ r = (ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r := by
    rw [← mul_pow, sq, mul_inv]
  have h3 : (ab a)⁻¹ ^ r ≤ c⁻¹ ^ r := by gcongr
  have h4 : 0 ≤ (ab a)⁻¹ ^ r := by positivity
  rw [h2]
  calc B * ((ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r) ≤ |B| * ((ab a)⁻¹ ^ r * (ab a)⁻¹ ^ r) := by
        gcongr; exact le_abs_self B
    _ ≤ |B| * (c⁻¹ ^ r * (ab a)⁻¹ ^ r) := by gcongr
    _ = |B| * c⁻¹ ^ r * (ab a)⁻¹ ^ r := by ring
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ThetaSeriesRatSL2MulInvariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem vm_mul_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* γ.1) ᵥ* (γ⁻¹).1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private theorem vm_inv_mul (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (x ᵥ* (γ⁻¹).1) ᵥ* γ.1 = x := by
  rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

private def rowE (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨ξ.1 ᵥ* γ.1, fun h => ξ.2 (by
    have := vm_mul_inv γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  invFun ξ := ⟨ξ.1 ᵥ* (γ⁻¹).1, fun h => ξ.2 (by
    have := vm_inv_mul γ ξ.1
    rw [h, Matrix.zero_vecMul] at this
    exact this.symm)⟩
  left_inv ξ := Subtype.ext (vm_mul_inv γ ξ.1)
  right_inv ξ := Subtype.ext (vm_inv_mul γ ξ.1)

private theorem row_rat (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (x : Fin 2 → ℚ) :
    (fun i => rt (x i)) ᵥ* (ratS ℚ γ).1 = fun i => rt ((x ᵥ* γ.1) i) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, ratS, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_add, map_mul]

theorem UpperTheory.thetaSeries_ratSL2_mul_invariant :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (t : ℝ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)),
        ThR Φ t (gl (ratS ℚ γ * g) * h) = ThR Φ t (gl g * h) := by
  intro Φ t γ g h
  unfold ThR
  rw [← (rowE γ).tsum_eq (fun ξ : Rw ℚ => Φ fun j => (iy (Real.exp t) : A ℚ) * ((fun i => rt (ξ.1 i)) ᵥ* (gl g * h).val) j)]
  refine tsum_congr fun ξ => ?_
  have key : (fun i => rt (ξ.1 i)) ᵥ* (gl (ratS ℚ γ * g) * h).val
      = (fun i => rt ((rowE γ ξ).1 i)) ᵥ* (gl g * h).val := by
    have e : (gl (ratS ℚ γ * g) * h).val = (ratS ℚ γ).1 * (gl g * h).val := by
      simp [gl, Matrix.SpecialLinearGroup.toGL, Matrix.mul_assoc]
    rw [e, ← Matrix.vecMul_vecMul, row_rat]
    rfl
  rw [key]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.AutomorphicFormBaseChangeRatSL2MulInvariant
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant :
    ∀ {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℚ) (g : G1 ℚ) (h : GL (Fin 2) (A ℚ)), φ (em E (gl (ratS ℚ γ * g) * h)) = φ (em E (gl g * h)) := by
  intro E _ _ D ω φ hφ γ g h
  have key : em E (gl (ratS ℚ γ)) =
      ratGL E 2 (Matrix.GeneralLinearGroup.map (algebraMap ℚ E) (Matrix.SpecialLinearGroup.toGL γ)) := by
    apply Units.ext
    ext i j
    simpa [UpperTheory.ConvolutionTheory.RankTwoDescent.em, gl, ratS, ratGL, Matrix.GeneralLinearGroup.map, Matrix.SpecialLinearGroup.map, Matrix.SpecialLinearGroup.toGL] using
      (AdeleBaseChange.adeleMap_algebraMap (K := ℚ) (L := E) (γ.1 i j))
  have e : gl (ratS ℚ γ * g) * h = gl (ratS ℚ γ) * (gl g * h) := by
    rw [gl, gl, map_mul, mul_assoc]
  rw [e, map_mul, key]
  exact hφ.left _ _
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ContinuousGL2BaseChangeDiagUnitInfiniteIdele
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele :
    ∀ (E : Type) [Field E] [NumberField E], Continuous (em E) ∧ Continuous (dM : (A ℚ)ˣ → GL (Fin 2) (A ℚ)) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) := by
  intro E _ _
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map hc
    · exact Units.continuous_coe_inv.matrix_map hc
  · refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_val
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact continuous_const
      · exact continuous_const
      · exact continuous_const
      · exact Units.continuous_coe_inv
  · let u : ℝ → (TR.Rinf ℚ)ˣ := fun t =>
      ⟨fun _ => Real.exp t, fun _ => (Real.exp t)⁻¹,
        funext fun _ => mul_inv_cancel₀ (Real.exp_ne_zero t),
        funext fun _ => inv_mul_cancel₀ (Real.exp_ne_zero t)⟩
    have hu : Continuous u := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => (Real.continuous_exp.inv₀ Real.exp_ne_zero)
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (u t) := by
      funext t
      simp only [iy, dif_neg (Real.exp_ne_zero t)]
      rfl
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem thetaPhi (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2))
    (C C' : Set (GL (Fin 2) (A ℚ))) (hC : IsCompact C) (hC' : IsCompact C') (n : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ g : G1 ℚ, ∀ k ∈ C, ∀ k' ∈ C',
      ‖φ (em E (gl g * k)) * ThR Φ t (gl g * k')‖ ≤ B * Real.exp (-((n : ℝ) * t)) := by
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red ℚ
  have hK : IsCompact (KK ℚ) := (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2
  have cpt : ∀ S : Set (GL (Fin 2) (A ℚ)), IsCompact S →
      IsCompact ((fun p : G1 ℚ × GL (Fin 2) (A ℚ) => gl p.1 * p.2) '' (KK ℚ ×ˢ S)) := fun S hS =>
    (hK.prod hS).image ((UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_fst).mul continuous_snd)
  obtain ⟨r, B₁, h₁⟩ := UpperTheory.norm_thetaSeries_siegelSet_le_exp Φ hΦ _ (cpt C' hC') c hc n
  obtain ⟨B₂, h₂⟩ := UpperTheory.norm_admissible_baseChange_siegelSet_le D ω φ hφ _ (cpt C hC) c hc r
  refine ⟨B₂ * B₁, fun t ht g k hk k' hk' => ?_⟩
  obtain ⟨γ, b, a, κ, hκ, hg, hca⟩ := hred g
  have ea : ∀ h : GL (Fin 2) (A ℚ), gl (nU b * mD a * κ) * h = gl (nU b * mD a) * (gl κ * h) := fun h => by
    have hm : gl (nU b * mD a * κ) = gl (nU b * mD a) * gl κ := map_mul _ _ _
    rw [hm, mul_assoc]
  have e1 : φ (em E (gl g * k)) = φ (em E (gl (nU b * mD a) * (gl κ * k))) := by
    rw [← ea, ← hg, UpperTheory.automorphicForm_baseChange_ratSL2_mul_invariant D ω φ hφ]
  have e2 : ThR Φ t (gl g * k') = ThR Φ t (gl (nU b * mD a) * (gl κ * k')) := by
    rw [← ea, ← hg, UpperTheory.thetaSeries_ratSL2_mul_invariant]
  have p₂ := h₂ b a _ ⟨(κ, k), ⟨hκ, hk⟩, rfl⟩ hca
  have p₁ := h₁ t ht b a _ ⟨(κ, k'), ⟨hκ, hk'⟩, rfl⟩ hca
  have hab : 0 < ab a := UpperTheory.ConvolutionTheory.R2.M.ab_pos a
  rw [e1, e2, norm_mul]
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ r) * (B₁ * Real.exp (-((n : ℝ) * t)) * ab a ^ r) :=
        mul_le_mul p₂ p₁ (norm_nonneg _) ((norm_nonneg _).trans p₂)
    _ = B₂ * B₁ * Real.exp (-((n : ℝ) * t)) := by
        rw [inv_pow]; field_simp

private theorem measPhi (ω : HChar ℚ) (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ) {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (h : X → GL (Fin 2) (A ℚ)) (hh : Continuous h) : Measurable fun x => φ (em E (h x)) :=
  (hφ.cont.comp ((UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).1.comp hh)).measurable

private theorem irMeas (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) : StronglyMeasurable (Ir M U χ φ Φ) := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  have hc : Continuous fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ => gl p.2 * dM p.1.2 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp (continuous_snd.comp continuous_fst))
  have h1 : StronglyMeasurable fun p : (ℝ × IdeleGroup ℚ) × G1 ℚ =>
      φ (em E (gl p.2 * dM p.1.2)) * ThR Φ p.1.1 (gl p.2 * dM p.1.2) :=
    ((measPhi ω D φ hφ _ hc).mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ (continuous_fst.comp continuous_fst) hc)).stronglyMeasurable
  have h2 := h1.integral_prod_right' (ν := M.μ.restrict M.D)
  have hχ : StronglyMeasurable fun x : ℝ × IdeleGroup ℚ => ((χ.1 x.2 : ℂˣ) : ℂ) :=
    (Units.continuous_val.comp (χ.2.1.comp continuous_snd)).stronglyMeasurable
  exact (hχ.mul h2).integral_prod_right' (ν := U.υ)

private theorem irDecay (D : Dat ℚ E) (ω χ : HChar ℚ) (M : Meas ℚ) (U : UMeas) (φ : GL (Fin 2) (A E) → ℂ) (hφ : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (hP : Per M U χ φ = 0)
    (Φ : (Fin 2 → A ℚ) → ℂ) (hΦ : Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2)) (n : ℕ) :
    ∃ B : ℝ, ∀ t, ‖Ir M U χ φ Φ t‖ ≤ B * Real.exp (-((n : ℝ) * |t|)) := by
  haveI := U.prob
  obtain ⟨hUc, hU1⟩ := UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one
  have hdM := (UpperTheory.continuous_GL2BaseChange_diagUnit_infiniteIdele E).2.1
  obtain ⟨Ψ, hΨ, hpois⟩ := UpperTheory.thetaSeries_poisson_functional_equation Φ hΦ
  set C : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => dM u) '' UU with hCdef
  set C' : Set (GL (Fin 2) (A ℚ)) := (fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹) '' UU with hC'def
  have hC : IsCompact C := hUc.image hdM
  have hc' : Continuous fun u : (A ℚ)ˣ => (gl (wW ℚ))⁻¹ * dM u⁻¹ := continuous_const.mul (hdM.comp continuous_inv)
  have hC' : IsCompact C' := hUc.image hc'
  obtain ⟨Bp, hBp⟩ := thetaPhi D ω φ hφ Φ hΦ C C hC hC n
  obtain ⟨Bm, hBm⟩ := thetaPhi D ω φ hφ Ψ hΨ C C' hC hC' (n + 2)
  set V : ℝ := M.μ.real M.D with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  obtain ⟨Bφ, hBφ⟩ := hφ.bdd
  have hcu : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * dM p.1 :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hdM.comp continuous_fst)
  have hcu' : Continuous fun p : IdeleGroup ℚ × G1 ℚ => gl p.2 * ((gl (wW ℚ))⁻¹ * dM p.1⁻¹) :=
    (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd).mul (hc'.comp continuous_fst)
  have mφ : Measurable fun p : IdeleGroup ℚ × G1 ℚ => φ (em E (gl p.2 * dM p.1)) := measPhi ω D φ hφ _ hcu
  refine ⟨(|Bp| + |Bm|) * V, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  ·
    have hb : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)‖ ≤ Bp * Real.exp (-((n : ℝ) * t)) :=
      fun u hu g => hBp t ht g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u)) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Φ hΦ _ _ continuous_const hcu)
    have := (UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm hb).2.2
    rw [abs_of_nonneg ht]
    refine le_trans this ?_
    have hex := Real.exp_pos (-((n : ℝ) * t))
    have : Bp ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
    calc Bp * Real.exp (-((n : ℝ) * t)) * V ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * t)) * V := by gcongr
      _ = _ := by ring
  ·
    set e : ℂ := (Real.exp (-(2 * t)) : ℂ) with he
    set c₀ : ℂ := -Φ 0 + e * Ψ 0 with hc₀
    have hb1 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u))‖ ≤ Bφ := fun _ _ _ => hBφ _
    have hb2 : ∀ u ∈ UU, ∀ g : G1 ℚ, ‖φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))‖ ≤
        Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) :=
      fun u hu g => hBm (-t) (by linarith) g _ ⟨u, hu, rfl⟩ _ ⟨u, hu, rfl⟩
    have hm1 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) => φ (em E (gl g * dM u))) := mφ
    have hm2 : Measurable (Function.uncurry fun (u : IdeleGroup ℚ) (g : G1 ℚ) =>
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹))) :=
      mφ.mul (UpperTheory.measurable_thetaSeries_comp_continuous Ψ hΨ _ _ continuous_const hcu')
    obtain ⟨i1, j1, -⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm1 hb1
    obtain ⟨i2, j2, n2⟩ := UpperTheory.norm_integral_unitaryHeckeChar_fundDomain_le M U χ _ _ hχ hm2 hb2
    have hae : ∀ᵐ u ∂U.υ, u ∈ UU := by
      have := U.supp
      exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun u hu => by simpa using hu
    have key : Ir M U χ φ Φ t = c₀ * Per M U χ φ + e * ∫ u, ((χ.1 u : ℂˣ) : ℂ) * ∫ g in M.D,
        φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ ∂U.υ := by
      unfold Per
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _) (j2.const_mul _)]
      unfold Ir
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      have hin : ∫ g in M.D, φ (em E (gl g * dM u)) * ThR Φ t (gl g * dM u) ∂M.μ =
          c₀ * (∫ g in M.D, φ (em E (gl g * dM u)) ∂M.μ) + e * ∫ g in M.D,
            φ (em E (gl g * dM u)) * ThR Ψ (-t) (gl g * ((gl (wW ℚ))⁻¹ * dM u⁻¹)) ∂M.μ := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((i1 u hu).const_mul _) ((i2 u hu).const_mul _)]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        simp only []
        rw [hpois t g u (hU1 u hu)]
        ring
      simp only []
      rw [hin]
      ring
    rw [key, hP, mul_zero, zero_add, norm_mul, he, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, abs_of_neg ht]
    refine (mul_le_mul_of_nonneg_left n2 (Real.exp_pos _).le).trans ?_
    have hex : Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) = Real.exp (-((n : ℝ) * -t)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have : Bm ≤ |Bp| + |Bm| := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
    have hpos := Real.exp_pos (-((n : ℝ) * -t))
    calc Real.exp (-(2 * t)) * (Bm * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t))) * V)
        = Bm * (Real.exp (-(2 * t)) * Real.exp (-(((n + 2 : ℕ) : ℝ) * (-t)))) * V := by ring
      _ = Bm * Real.exp (-((n : ℝ) * -t)) * V := by rw [hex]
      _ ≤ (|Bp| + |Bm|) * Real.exp (-((n : ℝ) * -t)) * V := by gcongr
      _ = _ := by ring

theorem ent_of :
    Ent := by
  intro E _ _ _ D P ω χ _ hω hχ M U φ hφ hP Φ hΦ
  have hχ1 : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := fun a => by
    have h := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hχ a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one] at h
    rw [show ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 from hω a, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  exact UpperTheory.differentiable_integral_exp_mul_of_rapid_decay _ (irMeas D ω χ M U φ hφ Φ hΦ).aestronglyMeasurable fun n => irDecay D ω χ M U φ hφ hχ1 hP Φ hΦ n

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
