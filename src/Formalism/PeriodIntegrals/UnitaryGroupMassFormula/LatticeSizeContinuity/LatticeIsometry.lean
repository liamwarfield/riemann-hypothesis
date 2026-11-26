module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatticeIsometry
noncomputable section

open NumberField
open scoped TensorProduct
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

namespace LatIs

theorem lamAf_eq (I : Formalism.MainNotions.S.AutInst) :
    I.Lf = Formalism.UG.latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.MainNotions.S.IntAf I.F I.E) I.L := by
  show Formalism.MainNotions.S.lamAf (F := I.F) I.L = _
  unfold Formalism.MainNotions.S.lamAf Formalism.UG.latS
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem latSet_eq (I : Formalism.MainNotions.S.AutInst) (x : I.GA) :
    Size.latSet I x = (Formalism.UG.CS.globLat (F := I.F)
      (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) I.L : Set (Fin I.n → I.E)) := by
  ext u
  simp only [Size.latSet, Set.mem_setOf_eq, SetLike.mem_coe]
  rw [lamAf_eq]
  rfl

end LatIs

theorem lattice_isometry : LatIs := by
  intro I x
  have hL := Formalism.UG.P.csGlob_lattice (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
  letI : Submodule.IsFullLattice I.E _ := hL
  exact ⟨_, hL.fg, Submodule.IsFullLattice.span_eq_top, LatIs.latSet_eq I x⟩

end PI.UnitaryGroupMassFormula.LSC
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermDefON
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDefiniteOrthonormal.Imports
namespace PI.UnitaryGroupMassFormula.HermDefON

open Matrix
open scoped ComplexOrder

private theorem exists_unitary_diagonal_pos_of_posDef {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℝ), Uᴴ * U = 1 ∧ (∀ i, 0 < μ i) ∧
      G = U * diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
  refine ⟨(hG.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hG.1.eigenvalues, ?_,
    fun i => hG.eigenvalues_pos i, ?_⟩
  · have h := hG.1.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    simpa [Matrix.star_eq_conjTranspose] using h
  · have h := hG.1.spectral_theorem
    refine h.trans ?_
    rfl

theorem exists_congr_one {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∃ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y.det ∧ yᴴ * G * y = 1 := by
  classical
  obtain ⟨U, μ, hUU, hμ, hG'⟩ := exists_unitary_diagonal_pos_of_posDef G hG
  have hr : ∀ i, Real.sqrt (μ i) * (Real.sqrt (μ i))⁻¹ = 1 := fun i =>
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (hμ i)).ne'
  have hr2 : ∀ i, (Real.sqrt (μ i))⁻¹ * μ i * (Real.sqrt (μ i))⁻¹ = 1 := by
    intro i
    have hs : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr (hμ i)).ne'
    have hsq : Real.sqrt (μ i) * Real.sqrt (μ i) = μ i := Real.mul_self_sqrt (hμ i).le
    calc (Real.sqrt (μ i))⁻¹ * μ i * (Real.sqrt (μ i))⁻¹
        = (Real.sqrt (μ i))⁻¹ * (Real.sqrt (μ i) * Real.sqrt (μ i)) * (Real.sqrt (μ i))⁻¹ := by
          rw [hsq]
      _ = 1 := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul, mul_inv_cancel₀ hs]
  let d : Fin n → ℂ := fun i => (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ)
  let e : Fin n → ℂ := fun i => ((Real.sqrt (μ i) : ℝ) : ℂ)
  have hde : ∀ i, e i * d i = 1 := by
    intro i
    show ((Real.sqrt (μ i) : ℝ) : ℂ) * (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, hr i, Complex.ofReal_one]
  have hdd : ∀ i, d i * (μ i : ℂ) * d i = 1 := by
    intro i
    show (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) * (μ i : ℂ) * (((Real.sqrt (μ i))⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hr2 i, Complex.ofReal_one]
  have hdH : (diagonal d)ᴴ = diagonal d := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [d]
  refine ⟨U * diagonal d, ?_, ?_⟩
  · have h : diagonal e * Uᴴ * (U * diagonal d) = 1 := by
      calc diagonal e * Uᴴ * (U * diagonal d) = diagonal e * (Uᴴ * U) * diagonal d := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          simp only [hde]
          exact Matrix.diagonal_one
    exact Matrix.isUnit_det_of_left_inverse h
  · rw [Matrix.conjTranspose_mul, hdH, hG']
    calc diagonal d * Uᴴ * (U * diagonal (fun i => (μ i : ℂ)) * Uᴴ) * (U * diagonal d)
        = diagonal d * (Uᴴ * U) * diagonal (fun i => (μ i : ℂ)) * (Uᴴ * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hUU, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal]
        simp only [hdd]
        exact Matrix.diagonal_one

end PI.UnitaryGroupMassFormula.HermDefON
end

theorem posDefCongruentOne : Formalism.L2.Props.HermDefON := fun _ G hG => PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG
end

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

lemma star_dot_self {n : ℕ} (w : Fin n → ℂ) : star w ⬝ᵥ w = ((nsq w : ℝ) : ℂ) := by
  unfold nsq dotProduct
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.conj_mul']

lemma quad {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (z : Fin j → ℂ) :
    star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = ((nsq (C *ᵥ z) : ℝ) : ℂ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self]

lemma sandwich {j : ℕ} (y X : Matrix (Fin j) (Fin j) ℂ) (v : Fin j → ℂ) :
    star v ⬝ᵥ ((yᴴ * X * y) *ᵥ v) = star (y *ᵥ v) ⬝ᵥ (X *ᵥ (y *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

lemma nsq_nonneg {n : ℕ} (w : Fin n → ℂ) : 0 ≤ nsq w :=
  Finset.sum_nonneg fun _ _ => by positivity

end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

namespace PI.UnitaryGroupMassFormula.LSC

open DeterminantMonotonicity in
theorem determinant_monotone : DetMono := by
  intro n j C M κ hκ hM
  classical
  have hB : (Cᴴ * C).PosSemidef := posSemidef_conjTranspose_mul_self C
  have hA : ((M * C)ᴴ * (M * C)).PosSemidef := posSemidef_conjTranspose_mul_self (M * C)
  have hBre : 0 ≤ ((Cᴴ * C).det).re := by
    simpa using (Complex.le_def.mp hB.det_nonneg).1
  refine ⟨hBre, ?_⟩
  have hqA : ∀ z : Fin j → ℂ, star z ⬝ᵥ (((M * C)ᴴ * (M * C)) *ᵥ z) = ((nsq (M *ᵥ (C *ᵥ z)) : ℝ) : ℂ) := by
    intro z; rw [quad, mulVec_mulVec]
  by_cases h0 : (Cᴴ * C).det = 0
  · obtain ⟨z, hz, hBz⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : nsq (C *ᵥ z) = 0 := by
      have := quad C z
      rw [hBz, dotProduct_zero] at this
      exact_mod_cast this.symm
    have h2 : nsq (M *ᵥ (C *ᵥ z)) = 0 :=
      le_antisymm (by simpa [h1] using hM (C *ᵥ z)) (nsq_nonneg _)
    have h3 : ((M * C)ᴴ * (M * C)) *ᵥ z = 0 := by
      rw [← hA.dotProduct_mulVec_zero_iff, hqA, h2]; simp
    have h4 : ((M * C)ᴴ * (M * C)).det = 0 := exists_mulVec_eq_zero_iff.mp ⟨z, hz, h3⟩
    rw [h4, h0]; simp
  · have hPD : (Cᴴ * C).PosDef := hB.posDef_iff_det_ne_zero.mpr h0
    obtain ⟨y, hy, hyB⟩ := posDefCongruentOne j _ hPD
    have hN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).PosSemidef := hA.conjTranspose_mul_mul_same y
    have hev : ∀ i, hN.1.eigenvalues i ≤ κ := by
      intro i
      have hv1 : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ ⇑(hN.1.eigenvectorBasis i) = 1 := by
        rw [dotProduct_comm]
        simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
          hN.1.eigenvectorBasis.orthonormal.1 i]
        simp
      have hBv : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ
          ((yᴴ * (Cᴴ * C) * y) *ᵥ ⇑(hN.1.eigenvectorBasis i)) = 1 := by
        rw [hyB, one_mulVec, hv1]
      rw [sandwich, quad] at hBv
      have hn1 : nsq (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i))) = 1 := by exact_mod_cast hBv
      rw [hN.1.eigenvalues_eq, sandwich, hqA]
      have := hM (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i)))
      rw [hn1, mul_one] at this
      simpa using this
    have hdetN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).det = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hN.1.det_eq_prod_eigenvalues]; push_cast; rfl
    have hP : ∏ i, hN.1.eigenvalues i ≤ κ ^ j := by
      calc ∏ i, hN.1.eigenvalues i ≤ ∏ _i : Fin j, κ :=
            Finset.prod_le_prod₀ (fun i _ => hN.eigenvalues_nonneg i) (fun i _ => hev i)
        _ = κ ^ j := by simp
    have hd0 : y.det ≠ 0 := hy.ne_zero
    have hnd : 0 < Complex.normSq y.det := Complex.normSq_pos.mpr hd0
    have e1 : ((Complex.normSq y.det : ℝ) : ℂ) * ((M * C)ᴴ * (M * C)).det
        = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [← hdetN, det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
      simp only [Complex.star_def]; ring
    have e2 : ((Complex.normSq y.det : ℝ) : ℂ) * (Cᴴ * C).det = 1 := by
      have := congrArg Matrix.det hyB
      rw [det_mul, det_mul, det_conjTranspose, det_one] at this
      rw [Complex.normSq_eq_conj_mul_self, ← this]
      simp only [Complex.star_def]; ring
    have r1 := congrArg Complex.re e1
    have r2 := congrArg Complex.re e2
    rw [Complex.re_ofReal_mul, Complex.ofReal_re] at r1
    rw [Complex.re_ofReal_mul, Complex.one_re] at r2
    refine le_of_mul_le_mul_left ?_ hnd
    calc Complex.normSq y.det * (((M * C)ᴴ * (M * C)).det).re = ∏ i, hN.1.eigenvalues i := r1
      _ ≤ κ ^ j := hP
      _ = κ ^ j * (Complex.normSq y.det * ((Cᴴ * C).det).re) := by rw [r2, mul_one]
      _ = Complex.normSq y.det * (κ ^ j * ((Cᴴ * C).det).re) := by ring

end PI.UnitaryGroupMassFormula.LSC
end
end
