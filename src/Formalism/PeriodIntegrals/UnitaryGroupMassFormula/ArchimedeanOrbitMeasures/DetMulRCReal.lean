module

public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.TupPlace
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

def reim {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : EuclideanSpace ℝ (Fin n × Fin m × Bool) :=
  (WithLp.equiv 2 (Fin n × Fin m × Bool → ℝ)).symm fun p => if p.2.2 then (Y p.1 p.2.1).re else (Y p.1 p.2.1).im

def PlaceJac : Prop := ∀ (n m : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (w : Matrix (Fin n) (Fin m) ℂ)
    {ι η : Type} [Fintype ι] [Fintype η]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ),
    n = m + S.card → (∀ i ∈ S, ∀ b, w i b = 0) → (wᴴ * Formalism.REAL.Jm ε * w).det ≠ 0 →
    (∀ x, (L x)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L x = 0 ∧ ∀ i ∈ S, ∀ j ∈ S, L x i j = 0) →
    (∀ x, ∑ i, ∑ j, ‖L x i j‖ ^ 2 = ‖x‖ ^ 2) →
    (∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * M = 0 →
      (∀ i ∈ S, ∀ j ∈ S, M i j = 0) → ∃ x, L x = M) →
    (∀ t, (H t)ᴴ = H t) → (∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) →
    (∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) →
    (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map
        (fun z => reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2))) =
      ENNReal.ofReal (2 ^ (n * m) / ‖(wᴴ * Formalism.REAL.Jm ε * w).det‖ ^ S.card) • volume

end PI.AprimeInfW
end
end

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

section MulR

variable {r m : ℕ}

def mulRC (A : Matrix (Fin m) (Fin m) ℂ) : (Fin r → Fin m → ℂ) →ₗ[ℂ] (Fin r → Fin m → ℂ) :=
  LinearMap.pi fun i => A.vecMulLinear.comp (LinearMap.proj i)

theorem mulRC_apply (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin r → Fin m → ℂ) :
    mulRC A Y = (Matrix.of Y * A : Matrix (Fin r) (Fin m) ℂ) := by
  ext i j
  simp [mulRC, Matrix.vecMul, Matrix.mul_apply, dotProduct]

theorem det_mulRC (A : Matrix (Fin m) (Fin m) ℂ) : (mulRC (r := r) A).det = A.det ^ r := by
  rw [mulRC, LinearMap.det_pi]
  have h : A.vecMulLinear = Matrix.toLin' Aᵀ := by
    ext v i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  simp [h, LinearMap.det_toLin', Matrix.det_transpose]

theorem det_mulRC_real (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulRC (r := r) A).restrictScalars ℝ).det = Complex.normSq A.det ^ r := by
  rw [LinearMap.det_restrictScalars, det_mulRC, map_pow, Algebra.norm_complex_apply]

def reimE : (Fin r → Fin m → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin r × Fin m × Bool) where
  toFun Y := reim (Matrix.of Y)
  invFun y := fun i j => ⟨y (i, j, true), y (i, j, false)⟩
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  left_inv Y := by
    funext i j
    apply Complex.ext <;> simp [reim]
  right_inv y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]

theorem map_mulR (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool))).map
        (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) =
      ENNReal.ofReal (Complex.normSq A.det ^ r)⁻¹ • volume := by
  set F : EuclideanSpace ℝ (Fin r × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin r × Fin m × Bool) :=
    (reimE (r := r)).toLinearMap ∘ₗ ((mulRC (r := r) A).restrictScalars ℝ) ∘ₗ (reimE (r := r)).symm.toLinearMap
    with hF
  have hdet : F.det = Complex.normSq A.det ^ r := by
    rw [hF, LinearMap.det_conj, det_mulRC_real]
  have hpos : 0 < Complex.normSq A.det ^ r := pow_pos (Complex.normSq_pos.2 hA) _
  have hfun : (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) = F := by
    funext y
    simp only [hF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulRC_apply]
    rfl
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool)))) (f := F) (by rw [hdet]; exact hpos.ne')
  rw [hfun, h, hdet, abs_of_pos (inv_pos.2 hpos)]

def trC {c : ℕ} : (Fin c → Fin m → ℂ) ≃ₗ[ℂ] (Fin m → Fin c → ℂ) where
  toFun Y := fun j i => Y i j
  invFun Z := fun i j => Z j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def mulLC {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin c → ℂ) →ₗ[ℂ] (Fin m → Fin c → ℂ) :=
  (trC (m := m) (c := c)).toLinearMap ∘ₗ mulRC (r := c) Aᵀ ∘ₗ (trC (m := m) (c := c)).symm.toLinearMap

theorem mulLC_apply {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → Fin c → ℂ) :
    mulLC A Y = (A * Matrix.of Y : Matrix (Fin m) (Fin c) ℂ) := by
  ext j i
  simp [mulLC, trC, mulRC, Matrix.vecMul, Matrix.mulVec, Matrix.mul_apply, dotProduct, mul_comm]

theorem det_mulLC_real {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulLC (c := c) A).restrictScalars ℝ).det = Complex.normSq A.det ^ c := by
  rw [LinearMap.det_restrictScalars, mulLC, LinearMap.det_conj, det_mulRC, Matrix.det_transpose, map_pow,
    Algebra.norm_complex_apply]

theorem map_mulL {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin m × Fin c × Bool))).map
        (fun y => reim (A * Matrix.of ((reimE (r := m) (m := c)).symm y))) =
      ENNReal.ofReal (Complex.normSq A.det ^ c)⁻¹ • volume := by
  set F : EuclideanSpace ℝ (Fin m × Fin c × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin c × Bool) :=
    (reimE (r := m) (m := c)).toLinearMap ∘ₗ ((mulLC (c := c) A).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := c)).symm.toLinearMap with hF
  have hdet : F.det = Complex.normSq A.det ^ c := by
    rw [hF, LinearMap.det_conj, det_mulLC_real]
  have hpos : 0 < Complex.normSq A.det ^ c := pow_pos (Complex.normSq_pos.2 hA) _
  have hfun : (fun y => reim (A * Matrix.of ((reimE (r := m) (m := c)).symm y))) = ⇑F := by
    funext y
    simp only [hF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulLC_apply]
    rfl
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin m × Fin c × Bool)))) (f := F) (by rw [hdet]; exact hpos.ne')
  rw [hfun, h, hdet, abs_of_pos (inv_pos.2 hpos)]

end MulR

end PI.AprimeInfW
