module

public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsHermFormCompare

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory
open scoped FourierTransform

noncomputable section

def gaussLattice {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin g)) :=
  Submodule.span ℤ (Set.range fun i : Fin g => WithLp.toLp 2 (B *ᵥ Pi.single i 1))

def gaussShellConst (n : ℕ) : ℝ :=
  3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π))

def GaussSqrt.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → ∃ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ * B = Y

def GaussLatticeIsLattice.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    DiscreteTopology (gaussLattice B) ∧ ∀ [DiscreteTopology (gaussLattice B)], IsZLattice ℝ (gaussLattice B)

def GaussLatticeCovolume.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ZLattice.covolume (gaussLattice B) = |B.det|

def GaussLatticeCoords.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    (∀ k : Fin g → ℤ, WithLp.toLp 2 (B *ᵥ intVec k) ∈ gaussLattice B) ∧
    (∀ x ∈ gaussLattice B, ∃ k : Fin g → ℤ, x = WithLp.toLp 2 (B *ᵥ intVec k)) ∧
    Function.Injective fun k : Fin g → ℤ => B *ᵥ intVec k

def GaussFourierSelf.Statement : Prop :=
  ∀ (g : ℕ) (w : EuclideanSpace ℝ (Fin g)),
    𝓕 (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) w =
      ((Real.exp (-π * ‖w‖ ^ 2) : ℝ) : ℂ)

def GaussPoissonBound.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 → ∀ a : Fin g → ℝ,
    Summable (fun k : Fin g → ℤ =>
      Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a))))) ∧
    Summable (fun μ : GroundTheory.Global.dualLattice (gaussLattice B) =>
      Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)) ∧
    ∑' k : Fin g → ℤ, Real.exp (-π * ((B *ᵥ (intVec k + a)) ⬝ᵥ (B *ᵥ (intVec k + a)))) ≤
      |B.det|⁻¹ * ∑' μ : GroundTheory.Global.dualLattice (gaussLattice B),
        Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussDualMin.Statement : Prop :=
  ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℝ), B.det ≠ 0 →
    ∀ μ ∈ GroundTheory.Global.dualLattice (gaussLattice B), μ ≠ 0 →
      ∃ l : Fin g → ℤ, l ≠ 0 ∧ qf (Bᵀ * B)⁻¹ (intVec l) ≤ ‖μ‖ ^ 2

def GaussDetFactor.Statement : Prop :=
  ∀ (g : ℕ) (Y B : Matrix (Fin g) (Fin g) ℝ), Y.PosDef → Bᵀ * B = (1 / 2 : ℝ) • Y →
    |B.det|⁻¹ = √2 ^ g * Y.det ^ (-(1 / 2 : ℝ))

def GaussPoissonDual.Statement : Prop :=
  ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ), Y.PosDef → 0 < ρ →
    (∀ l : Fin g → ℤ, l ≠ 0 → ρ ^ 2 ≤ qf Y⁻¹ (intVec l)) → ∀ u : Fin g → ℝ,
      Summable (fun k : Fin g → ℤ => Real.exp (-(π / 2) * qf Y (intVec k + u))) ∧
      ∃ Λ : Submodule ℤ (EuclideanSpace ℝ (Fin g)), (∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖) ∧
        ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u)) ≤
          √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2)

def GaussPacking.Statement : Prop :=
  ∀ (n : ℕ) (s : Finset (EuclideanSpace ℝ (Fin n))) (δ r : ℝ), 0 < δ → 0 ≤ r →
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) → (∀ x ∈ s, ‖x‖ ≤ r) →
    (s.card : ℝ) ≤ (1 + 2 * r / δ) ^ n

def GaussTermBound.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
    ((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2) ≤
      √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))

def GaussShell.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) → ∀ (F : Finset Λ) (m : ℕ),
      ∑ μ ∈ F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m),
          Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ))

def GaussShellSum.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) (δ : ℝ), 0 < δ →
    (∀ v ∈ Λ, v ≠ 0 → δ ≤ ‖v‖) →
      Summable (fun μ : Λ => Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)) ∧
      ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
        2 * gaussShellConst n * (1 + 1 / δ) ^ n

def GaussConstant.Statement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → √2 ^ n * (2 * gaussShellConst n) ≤ (72 * Real.exp 4 * n) ^ ((n : ℝ) / 2)

abbrev gaussUnit : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (Pi.single 0 1)

theorem gaussUnit_norm : ‖gaussUnit‖ = 1 := by
  simp [gaussUnit]

theorem mem_gaussLattice_one {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ) ↔ ∃ a : ℤ, a • gaussUnit = x := by
  have h : (Set.range fun i : Fin 1 => WithLp.toLp 2 ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ
      Pi.single i 1)) = {gaussUnit} := by
    rw [Set.range_unique, Matrix.one_mulVec]
    rfl
  rw [gaussLattice, h, Submodule.mem_span_singleton]

theorem gaussLattice_one_min : ∀ v ∈ gaussLattice (1 : Matrix (Fin 1) (Fin 1) ℝ), v ≠ 0 →
    (1 : ℝ) ≤ ‖v‖ := by
  intro v hv hv0
  obtain ⟨a, rfl⟩ := mem_gaussLattice_one.1 hv
  have ha : a ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, gaussUnit_norm, mul_one, Real.norm_eq_abs]
  exact_mod_cast Int.one_le_abs ha

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (y : Fin e → ℂ) : ℝ :=
  Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ
    (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re)

def chartMass {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y : Fin e → ℂ, maDensity (fun _ : Fin e => hermChartPot M) y

def ChartMassInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    chartMass M = chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace HermitianFormComparison

theorem sum_norm_sq_unitary {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * star U = 1)
    (x : Fin n → ℂ) : ∑ k, ‖(star U *ᵥ x) k‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have h1 : star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, star_eq_conjTranspose,
      conjTranspose_conjTranspose, ← star_eq_conjTranspose, hU, vecMul_one]
  rw [← h1]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem re_quad_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re = ∑ k, hA.eigenvalues k *
      ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) k‖ ^ 2 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (↑hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hspec : A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * star U := by
    have h := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set y : Fin n → ℂ := star U *ᵥ x with hy
  have hq : star x ⬝ᵥ (A *ᵥ x) = star y ⬝ᵥ (diagonal (fun k => (hA.eigenvalues k : ℂ)) *ᵥ y) := by
    conv_lhs => rw [hspec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hy, star_mulVec,
      star_eq_conjTranspose U, conjTranspose_conjTranspose]
  rw [hq]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem eigenvectorUnitary_mul_star {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2

theorem re_quad_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ (1 + ∑ k, hM.1.eigenvalues k) * (star x ⬝ᵥ x).re := by
  rw [re_quad_eq hM.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hM.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hle : hM.1.eigenvalues k ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (f := hM.1.eigenvalues) (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ k)
  linarith

theorem re_quad_ge {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef) (x : Fin n → ℂ) :
    (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (N *ᵥ x)).re := by
  rw [re_quad_eq hN.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hN.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hpos := hN.eigenvalues_pos k
  have hle : (hN.1.eigenvalues k)⁻¹ ≤ ∑ j, (hN.1.eigenvalues j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (hN.1.eigenvalues j)⁻¹)
      (fun j _ => (inv_pos.mpr (hN.eigenvalues_pos j)).le) (Finset.mem_univ k)
  rw [inv_le_comm₀ (by linarith [inv_pos.mpr hpos]) hpos]
  linarith

end HermitianFormComparison


open HermitianFormComparison in
theorem HermFormCompare.proof : HermFormCompare.Statement := by
  intro n M N hM hN
  set L : ℝ := 1 + ∑ k, hM.1.eigenvalues k with hL
  set m : ℝ := (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ with hm
  have hL0 : 0 < L := by
    have : 0 ≤ ∑ k, hM.1.eigenvalues k := Finset.sum_nonneg fun k _ => (hM.eigenvalues_pos k).le
    linarith
  have hm0 : 0 < m := by
    have : 0 ≤ ∑ k, (hN.1.eigenvalues k)⁻¹ :=
      Finset.sum_nonneg fun k _ => (inv_pos.mpr (hN.eigenvalues_pos k)).le
    exact inv_pos.mpr (by linarith)
  refine ⟨L / m, div_pos hL0 hm0, fun x => ?_⟩
  have hup := re_quad_le hM.posSemidef x
  have hlo := re_quad_ge hN x
  calc (star x ⬝ᵥ (M *ᵥ x)).re ≤ L * (star x ⬝ᵥ x).re := hup
    _ = L / m * (m * (star x ⬝ᵥ x).re) := by field_simp
    _ ≤ L / m * (star x ⬝ᵥ (N *ᵥ x)).re :=
        mul_le_mul_of_nonneg_left hlo (div_pos hL0 hm0).le

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

variable {m n : Type*} [Fintype m] [Fintype n]

theorem posDef_fromBlocks_diag {A : Matrix m m ℝ} {D : Matrix n n ℝ} (hA : A.PosDef)
    (hD : D.PosDef) : (fromBlocks A 0 0 D).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (hA.1.fromBlocks (by simp) hD.1) fun x hx => ?_
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
    simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  have h1 := hA.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := hD.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  by_cases hl : x ∘ Sum.inl = 0
  · have hr : x ∘ Sum.inr ≠ 0 := by
      intro hr
      apply hx
      funext i
      cases i with
      | inl i => exact congrFun hl i
      | inr i => exact congrFun hr i
    have := hD.dotProduct_mulVec_pos hr
    linarith
  · have := hA.dotProduct_mulVec_pos hl
    linarith

end KCoord

variable {g : ℕ}

namespace KCoord

def unip (X : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks 1 X 0 1

noncomputable def diagInv (Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ 0 0 Y

theorem siegelGram_eq (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    siegelGram X Y = (unip X)ᵀ * diagInv Y * unip X := by
  have hXt : Xᵀ = X := hX
  simp [siegelGram, unip, diagInv, fromBlocks_transpose, fromBlocks_multiply, hXt, add_comm]

theorem unip_mem (X : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) :
    unip X ∈ symplecticGroup (Fin g) ℝ := by
  have hXt : Xᵀ = X := hX
  rw [SymplecticGroup.mem_iff]
  simp [unip, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hXt]

theorem diagInv_mem (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosDef) :
    diagInv Y ∈ symplecticGroup (Fin g) ℝ := by
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hYt : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hYit : Y⁻¹ᵀ = Y⁻¹ := by rw [Matrix.transpose_nonsing_inv, hYt]
  rw [SymplecticGroup.mem_iff]
  simp [diagInv, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, hYt, hYit,
    Matrix.nonsing_inv_mul _ hdet, Matrix.mul_nonsing_inv _ hdet]

theorem unip_isUnit (X : Matrix (Fin g) (Fin g) ℝ) : IsUnit (unip X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [unip]

theorem siegelGram_mem_posDef (X Y : Matrix (Fin g) (Fin g) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    siegelGram X Y ∈ symplecticGroup (Fin g) ℝ ∧ (siegelGram X Y).PosDef := by
  rw [siegelGram_eq X Y hX]
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _
    (SymplecticGroup.transpose_mem (unip_mem X hX)) (diagInv_mem Y hY)) (unip_mem X hX), ?_⟩
  have hD : (diagInv Y).PosDef := posDef_fromBlocks_diag hY.inv hY
  have hinj : Function.Injective (unip X).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (unip_isUnit X)
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

end KCoord

namespace KCoord

theorem existsUnique_siegelGram (G : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ)
    (hS : G ∈ symplecticGroup (Fin g) ℝ) (hG : G.PosDef) :
    ∃! XY : Matrix (Fin g) (Fin g) ℝ × Matrix (Fin g) (Fin g) ℝ,
      XY.1.IsSymm ∧ XY.2.PosDef ∧ G = siegelGram XY.1 XY.2 := by
  have hGt : Gᵀ = G := by
    have := hG.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hS' := hS
  rw [SymplecticGroup.mem_iff, hGt] at hS'
  have hGb := Matrix.fromBlocks_toBlocks G
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGt' := hGt
  rw [← hGb] at hS' hGt'
  simp only [fromBlocks_transpose, Matrix.J, fromBlocks_multiply] at hS' hGt'
  obtain ⟨e1, e2, -, -⟩ := Matrix.fromBlocks_inj.mp hS'
  obtain ⟨t1, -, t3, -⟩ := Matrix.fromBlocks_inj.mp hGt'
  simp at e1 e2
  have hBA : B * A = A * C := by
    have := e1
    rwa [add_neg_eq_zero] at this
  have hAD : A * D = 1 + B * B := by
    have h1 : A * D = B * B - (B * B + -(A * D)) := by abel
    rw [h1, e2]; abel
  have hA : A.PosDef := hG.submatrix Sum.inl_injective
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
  have hAAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  have hAit : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, t1]
  have hCt : Bᵀ = C := t3
  have k : A⁻¹ * B = C * A⁻¹ := by
    calc A⁻¹ * B = A⁻¹ * B * (A * A⁻¹) := by rw [hAAi, Matrix.mul_one]
      _ = A⁻¹ * (B * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * C) * A⁻¹ := by rw [hBA]
      _ = C * A⁻¹ := by rw [← Matrix.mul_assoc A⁻¹ A C, hAiA, Matrix.one_mul]
  have hX : (A⁻¹ * B).IsSymm := by
    show (A⁻¹ * B)ᵀ = A⁻¹ * B
    rw [Matrix.transpose_mul, hAit, hCt, k]
  have hY : (A⁻¹).PosDef := hA.inv
  have hYinv : (A⁻¹)⁻¹ = A := Matrix.nonsing_inv_nonsing_inv A hAdet
  refine ⟨(A⁻¹ * B, A⁻¹), ⟨hX, hY, ?_⟩, ?_⟩
  · show G = siegelGram (A⁻¹ * B) A⁻¹
    rw [siegelGram, hYinv]
    conv_lhs => rw [← hGb]
    congr 1
    · rw [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    · rw [k, Matrix.mul_assoc, hAiA, Matrix.mul_one]
    · have hD : D = A⁻¹ * (1 + B * B) := by
        rw [← hAD, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
      rw [hD, k, Matrix.mul_add, Matrix.mul_one]
      congr 1
      calc A⁻¹ * (B * B) = A⁻¹ * B * (A * A⁻¹) * B := by
            rw [hAAi, Matrix.mul_one, Matrix.mul_assoc]
        _ = C * A⁻¹ * A * A⁻¹ * B := by rw [← k]; simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (A⁻¹ * B) := by simp only [Matrix.mul_assoc]
        _ = C * A⁻¹ * A * (C * A⁻¹) := by rw [k]
  · rintro ⟨X', Y'⟩ ⟨hX', hY', hG'⟩
    have hY'det : IsUnit Y'.det := (Matrix.isUnit_iff_isUnit_det Y').1 hY'.isUnit
    have h11 : A = Y'⁻¹ := by
      rw [hAdef, hG']; simp [siegelGram]
    have h12 : B = Y'⁻¹ * X' := by
      rw [hBdef, hG']; simp [siegelGram]
    have hYY : Y' = A⁻¹ := by
      rw [h11, Matrix.nonsing_inv_nonsing_inv Y' hY'det]
    have hXX : X' = A⁻¹ * B := by
      rw [h12, ← hYY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Y' hY'det, Matrix.one_mul]
    simp only [Prod.mk.injEq]
    exact ⟨hXX, hYY⟩

end KCoord

theorem SiegelCoordinates.intersectionNumber_baseChange : SiegelCoordinates.Statement := fun _ =>
  ⟨fun X Y hX hY => KCoord.siegelGram_mem_posDef X Y hX hY,
    fun G hS hG => KCoord.existsUnique_siegelGram G hS hG⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def symplOmega {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) : R :=
  u ⬝ᵥ (J l R *ᵥ v)

def symplCons {R : Type*} {n : ℕ} (p q : R) (w : Fin n ⊕ Fin n → R) :
    Fin (n + 1) ⊕ Fin (n + 1) → R :=
  Sum.elim (vecCons p fun j => w (Sum.inl j)) (vecCons q fun j => w (Sum.inr j))

def symplTail {R : Type*} {n : ℕ} (u : Fin (n + 1) ⊕ Fin (n + 1) → R) : Fin n ⊕ Fin n → R :=
  fun x => u (Sum.map Fin.succ Fin.succ x)

def symplExt {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R :=
  Matrix.of (Sum.elim (vecCons (symplCons α β 0) fun i => symplCons 0 0 (Q (Sum.inl i)))
    (vecCons (symplCons γ δ 0) fun i => symplCons 0 0 (Q (Sum.inr i))))

def symplReduce {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun a b => H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
    H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
      H (Sum.inl 0) (Sum.inl 0)

def symplGram {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) : Matrix l l ℝ :=
  P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ

def SymplOmegaMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l : Type) [Fintype l] [DecidableEq l]
    (M : Matrix (l ⊕ l) (l ⊕ l) R),
    M ∈ symplecticGroup l R ↔ ∀ x y, symplOmega (M x) (M y) = J l R x y

def SymplCons.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    (∀ u : Fin (n + 1) ⊕ Fin (n + 1) → R,
      symplCons (u (Sum.inl 0)) (u (Sum.inr 0)) (symplTail u) = u) ∧
    ∀ (p q p' q' : R) (w w' : Fin n ⊕ Fin n → R),
      symplOmega (symplCons p q w) (symplCons p' q' w') = q * p' - p * q' + symplOmega w w'

def SymplExtMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    α * δ - β * γ = 1 → Q ∈ symplecticGroup (Fin n) R →
    symplExt α β γ δ Q ∈ symplecticGroup (Fin (n + 1)) R

def SymplExtVecMul.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ p q : R)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (w : Fin n ⊕ Fin n → R),
    symplCons p q w ᵥ* symplExt α β γ δ Q = symplCons (p * α + q * γ) (p * β + q * δ) (w ᵥ* Q)

def SymplTwoRow.Statement : Prop :=
  ∀ (n : ℕ) (c d x y : ℤ), x * c + y * d = 1 →
    ∃ P ∈ symplecticGroup (Fin (n + 1 + 1)) ℤ, P (Sum.inl 0) = symplCons c 0 (symplCons d 0 0)

def SymplGcd.Statement : Prop :=
  ∀ a b : ℤ, ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1

def SymplOrbit.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ),
    ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, ∃ m : ℤ, v = m • P (Sum.inl 0)

def SymplQuadDiag.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ (O : Matrix ι ι ℝ) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧ |O.det| = 1 ∧ ∏ i, lam i = G.det ∧
      ∀ x : ι → ℝ, qf G x = ∑ i, lam i * (O *ᵥ x) i ^ 2

def SymplBoxVolume.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), A.det ≠ 0 →
    (∀ i, 0 < a i) →
    MeasureTheory.volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      ENNReal.ofReal ((∏ i, 2 * a i) / |A.det|)

def SymplMinkowskiBox.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), |A.det| = 1 →
    (∀ i, 0 < a i) → 1 < ∏ i, a i →
    ∃ v : ι → ℤ, v ≠ 0 ∧ ∀ i, |(A *ᵥ intVec v) i| < a i

def SymplMinExists.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m

def SymplMinBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef → G.det = 1 →
    ∀ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m → m ≤ Fintype.card ι

def SymplShortPrim.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∀ (v w : ι → ℤ) (m : ℤ), v = m • w → v ≠ 0 →
    (∀ u : ι → ℤ, u ≠ 0 → qf G (intVec v) ≤ qf G (intVec u)) → m = 1 ∨ m = -1

def SymplGramMem.Statement : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    P ∈ symplecticGroup (Fin n) ℤ → G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    symplGram P G ∈ symplecticGroup (Fin n) ℝ ∧ (symplGram P G).PosDef ∧
      (∀ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ,
        symplGram (Q * P) G = symplGram Q (symplGram P G)) ∧
      ∀ x, symplGram P G x x = qf G (intVec (P x))

def SymplFirstRow.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq

def SymplReduceMem.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H ∈ symplecticGroup (Fin (n + 1)) ℝ → H (Sum.inl 0) (Sum.inl 0) ≠ 0 →
    symplReduce H ∈ symplecticGroup (Fin n) ℝ

def SymplReducePosDef.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H.PosDef → (symplReduce H).PosDef

def SymplReduceConj.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
        H (Sum.inl 0) (Sum.inl 0) ∧
      symplReduce (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) = Q * symplReduce H * Qᵀ

def SymplDetSchur.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A 0 0 ≠ 0 →
    A.det = A 0 0 * (Matrix.of fun i j : Fin n => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0).det

def SymplReduceStep.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
    H (Sum.inl 0) (Sum.inl 0) ≠ 0 → Q ∈ symplecticGroup (Fin n) ℤ →
    ∃ Q' ∈ symplecticGroup (Fin (n + 1)) ℤ,
      symplGram Q' H (Sum.inl 0) (Sum.inl 0) = H (Sum.inl 0) (Sum.inl 0) ∧
      (symplGram Q' H).toBlocks₁₁.det =
        H (Sum.inl 0) (Sum.inl 0) * (symplGram Q (symplReduce H)).toBlocks₁₁.det

def SymplStep.Statement : Prop :=
  ∀ (n : ℕ) (B : ℝ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    (∀ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, H ∈ symplecticGroup (Fin n) ℝ → H.PosDef →
      ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P H).toBlocks₁₁.det ≤ B) →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (symplGram P G).toBlocks₁₁.det ≤ ρsq * B

def SymplDetBound.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P G).toBlocks₁₁.det ≤ (2 * (n : ℝ)) ^ n

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

noncomputable section

def thetaSummand {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ) (z : Fin g → ℂ)
    (k : Fin g → ℤ) : ℂ :=
  Complex.exp (π * Complex.I *
      ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ fun i => ((intVec k i + a i : ℝ) : ℂ))) +
    2 * π * Complex.I * ((fun i => ((intVec k i + a i : ℝ) : ℂ)) ⬝ᵥ (z + fun i => (b i : ℂ))))

def torusChar {g : ℕ} (m : Fin g → ℤ) (u : Fin g → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ i, (m i : ℂ) * (u i : ℂ))

def ThetaSummandNorm.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ) (k : Fin g → ℤ), Y.IsSymm →
    ‖thetaSummand X Y a b (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) k‖ *
        exp (-π * qf Y u₁) = exp (-π * qf Y (intVec k + a + u₁))

def ThetaNormMajorant.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ u₂ : Fin g → ℝ), Y.PosDef →
    thetaNorm X Y a b u₁ u₂ ≤ ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁))

def ThetaCharIntegral.Statement : Prop :=
  ∀ (g : ℕ) (m : Fin g → ℤ),
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, torusChar m u = if m = 0 then 1 else 0

def ThetaCubeParseval.Statement : Prop :=
  ∀ (g : ℕ) (c : (Fin g → ℤ) → ℂ), Summable (fun k => ‖c k‖) →
    ∫ u in Set.Icc (0 : Fin g → ℝ) 1, ‖∑' k, c k * torusChar k u‖ ^ 2 = ∑' k, ‖c k‖ ^ 2

def ThetaInnerMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b u₁ : Fin g → ℝ), Y.PosDef →
    ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
      ∑' k : Fin g → ℤ, exp (-(2 * π) * qf Y (intVec k + a + u₁))

def ThetaMean.Statement : Prop :=
  ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a b : Fin g → ℝ), Y.PosDef →
    (∫ u₁ in Set.Icc (0 : Fin g → ℝ) 1, ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1,
        thetaNorm X Y a b u₁ u₂ ^ 2) = ((2 : ℝ) ^ g * Y.det) ^ (-(1 / 2 : ℝ))

def ThetaFirstCoordSplit.Statement : Prop :=
  ∀ (g : ℕ) [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ), Y.PosDef → 0 < ρ →
    Y⁻¹ 0 0 = ρ ^ 2 →
    ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        ∑' k : Fin g → ℤ, exp (-(π / 2) * qf Y (intVec k + (a + u₁)))

def ThetaConstants.Statement : Prop :=
  ∀ C₃ : ℝ, 0 < C₃ → ∃ C : ℝ, 0 < C ∧
    ∀ (g : ℕ) (ρ d : ℝ), 1 ≤ g → 0 < ρ → 0 < d → ρ ^ 2 ≤ 2 * g → d⁻¹ ≤ ρ ^ 2 * (2 * g) ^ (g - 1) →
      (C₃ * g) ^ ((g : ℝ) / 2) * d ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g ≤
        ((2 : ℝ) ^ g * d) ^ (-(1 / 4 : ℝ)) * exp (g * log (1 + 1 / ρ) + C * g * log (2 * g))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def InvertibleIdealIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
      (Module.finrank ℚ L : ℝ) * Real.log (genIndex M B.toAddSubgroup) =
        (Module.finrank ℤ B : ℝ) *
          Real.log (genIndex (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup
            (1 : Submodule (𝓞 L) L).toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Equiv

namespace CauchyBinetAlt

variable {R : Type*} [CommRing R] {j N : ℕ}

theorem det_mul_eq_sum (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R) :
    (A * B).det = ∑ p : Fin j → Fin N, (∏ i, B (p i) i) * (A.submatrix id p).det := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [prod_mul_distrib]
  ring

theorem det_submatrix_eq_zero (A : Matrix (Fin j) (Fin N) R) {p : Fin j → Fin N}
    (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall, exists_prop] at hp
  obtain ⟨a, b, hab, hne⟩ := hp
  exact det_zero_of_column_eq hne fun k => by simp [hab]

theorem minor_mul (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) :
    (colsOf A I).det * (rowsOf B I).det =
      ∑ w : Perm (Fin j), (∏ i, B (I.1.orderEmbOfFin I.2 (w i)) i) *
        (A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w)).det := by
  rw [det_apply' (rowsOf B I), mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w) = (colsOf A I).submatrix id w := by
    ext a b
    rfl
  rw [h, det_permute']
  simp only [rowsOf, submatrix_apply, id]
  ring

theorem sum_reindex {M : Type*} [AddCommMonoid M] (g : (Fin j → Fin N) → M)
    (hg : ∀ p, ¬ Function.Injective p → g p = 0) :
    ∑ p, g p = ∑ I : {I : Finset (Fin N) // I.card = j}, ∑ w : Perm (Fin j),
      g (I.1.orderEmbOfFin I.2 ∘ w) := by
  rw [← Finset.sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hg p hp))]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij (fun x _ => x.1.1.orderEmbOfFin x.1.2 ∘ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨I, w⟩ _
    simp only [mem_filter, mem_univ, true_and]
    exact (I.1.orderEmbOfFin I.2).injective.comp w.injective
  · rintro ⟨I, w⟩ _ ⟨J, w'⟩ _ h
    simp only at h
    have key : ∀ (K : {I : Finset (Fin N) // I.card = j}) (v : Perm (Fin j)) (x : Fin N),
        x ∈ K.1 ↔ ∃ a, (K.1.orderEmbOfFin K.2 ∘ v) a = x := by
      intro K v x
      rw [← Finset.mem_coe, ← range_orderEmbOfFin K.1 K.2, Set.mem_range]
      exact ⟨fun ⟨a, ha⟩ => ⟨v.symm a, by simpa using ha⟩, fun ⟨a, ha⟩ => ⟨v a, ha⟩⟩
    have hIJ : I = J := by
      apply Subtype.ext
      ext x
      rw [key I w x, key J w' x, h]
    subst hIJ
    have hw : w = w' := Equiv.ext fun a => (I.1.orderEmbOfFin I.2).injective (congrFun h a)
    rw [hw]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hI : (univ.image p).card = j := by
      rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
    let w0 : Fin j → Fin j := fun a =>
      ((univ.image p).orderIsoOfFin hI).symm ⟨p a, mem_image_of_mem p (mem_univ a)⟩
    have hw0 : Function.Injective w0 := by
      intro a b hab
      exact hp (congrArg Subtype.val (((univ.image p).orderIsoOfFin hI).symm.injective hab))
    refine ⟨(⟨univ.image p, hI⟩, Equiv.ofBijective w0 (Finite.injective_iff_bijective.mp hw0)),
      mem_univ _, ?_⟩
    funext a
    show ((univ.image p).orderEmbOfFin hI) (w0 a) = p a
    rw [← coe_orderIsoOfFin_apply]
    simp only [w0, OrderIso.apply_symm_apply]
  · intro x _
    rfl

end CauchyBinetAlt

theorem CauchyBinet.proof : CauchyBinet.Statement := by
  intro R _ j N A B
  rw [CauchyBinetAlt.det_mul_eq_sum, CauchyBinetAlt.sum_reindex _ (fun p hp => by
    rw [CauchyBinetAlt.det_submatrix_eq_zero A hp, mul_zero])]
  exact Finset.sum_congr rfl fun I _ => (CauchyBinetAlt.minor_mul A B I).symm

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KCoord

theorem sq_coord_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (i : ι) (v : ι → ℝ) : v i ^ 2 ≤ Y⁻¹ i i * qf Y v := by
  have hU : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).1 hY.isUnit
  have hsymm : Yᵀ = Y := by
    have := hY.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set w : ι → ℝ := Y⁻¹ *ᵥ Pi.single i 1 with hw
  have hYw : Y *ᵥ w = Pi.single i 1 := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hwY : ∀ x : ι → ℝ, w ⬝ᵥ (Y *ᵥ x) = x i := by
    intro x
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hYw]
    simp [dotProduct, Pi.single_apply]
  have hxY : ∀ x : ι → ℝ, x ⬝ᵥ (Y *ᵥ w) = x i := by
    intro x
    rw [hYw]
    simp [dotProduct, Pi.single_apply]
  have hwi : w i = Y⁻¹ i i := by
    rw [hw]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hpos : 0 < Y⁻¹ i i := hY.inv.diag_pos
  have hnn : ∀ t : ℝ, 0 ≤ qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
    intro t
    have h0 : 0 ≤ (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) := by
      have := hY.posSemidef.dotProduct_mulVec_nonneg (v - t • w)
      simpa using this
    have hexp : (v - t • w) ⬝ᵥ (Y *ᵥ (v - t • w)) =
        qf Y v - 2 * t * v i + t ^ 2 * Y⁻¹ i i := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hwY, hwY, hxY, hwi]
      simp only [qf]
      ring
    linarith
  have h := hnn (v i / Y⁻¹ i i)
  have hne : Y⁻¹ i i ≠ 0 := ne_of_gt hpos
  have e : qf Y v - 2 * (v i / Y⁻¹ i i) * v i + (v i / Y⁻¹ i i) ^ 2 * Y⁻¹ i i =
      qf Y v - v i ^ 2 / Y⁻¹ i i := by
    field_simp
    ring
  rw [e] at h
  have h2 : v i ^ 2 / Y⁻¹ i i ≤ qf Y v := by linarith
  rwa [div_le_iff₀ hpos, mul_comm] at h2

end KCoord

end GroundTheory.Heights₂.Heights
end
