module

public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ContinuousMultilinearOfFiniteDimensional
public import GroundTheory.AutomorphicForms.HarishChandraRegularity

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Weights
section -- merged from GroundTheory.AutomorphicForms.ArchimedeanWhittaker.FiltrationCocycleLiftCriterion
namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

abbrev FiltrationCocycleLiftCriterion : Subgroup (GL (Fin 2) ℝ) := ⊤

abbrev gl2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) := ⊤

theorem hGL2 : IsExpLieAlgebra FiltrationCocycleLiftCriterion gl2 := isExpLieAlgebra_top

noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) : FiltrationCocycleLiftCriterion :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, Subgroup.mem_top _⟩

@[simp] theorem coe_toGL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) :
    (((toGL A hA : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A := rfl

theorem GL2_ext {g g' : FiltrationCocycleLiftCriterion}
    (h : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ((g' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
    g = g' := Subtype.ext (Units.ext h)

noncomputable def kMat (θ : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    simp [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ])

@[simp] theorem coe_kMat (θ : ℝ) : (((kMat θ : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

theorem kMat_add (a b : ℝ) : kMat (a + b) = kMat a * kMat b := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_kMat]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem kMat_zero : kMat 0 = 1 := by
  apply GL2_ext; simp only [coe_kMat, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem kMat_two_pi : kMat (2 * Real.pi) = 1 := by
  apply GL2_ext; simp only [coe_kMat, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def lW : gl2 := ⟨!![0, 1; -1, 0], Submodule.mem_top⟩

@[simp] theorem coe_lW : ((lW : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; -1, 0] := rfl

theorem exp_eq_of_hasDerivAt {X : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ t, HasDerivAt c (X * c t) t) (h0 : c 0 = 1) (t : ℝ) : exp (t • X) = c t := by
  have hcomm : ∀ s : ℝ, exp (s • X) * X = X * exp (s • X) := fun s =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).unique (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s)
  set D : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => exp ((-s) • X) * c s with hD
  have hDd : ∀ s, HasDerivAt D 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => exp ((-s) • X)) ((-1 : ℝ) • (X * exp ((-s) • X))) s :=
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-s)).scomp s (hasDerivAt_neg s)
    have h2 := h1.mul (hc s)
    refine h2.congr_deriv ?_
    rw [neg_one_smul, neg_mul, ← mul_assoc, hcomm, mul_assoc, neg_add_cancel]
  have hconst : D t = D 0 := is_const_of_deriv_eq_zero
    (fun s => (hDd s).differentiableAt) (fun s => (hDd s).deriv) t 0
  have hD0 : D 0 = 1 := by simp [hD, h0]
  have hinv : exp (t • X) * exp ((-t) • X) = 1 := by
    rw [← exp_add_of_commute' ℝ ((Commute.refl X).smul_left t |>.smul_right (-t)), ← add_smul,
      add_neg_cancel, zero_smul, exp_zero]
  calc exp (t • X) = exp (t • X) * D t := by rw [hconst, hD0, mul_one]
    _ = exp (t • X) * exp ((-t) • X) * c t := by simp [hD, mul_assoc]
    _ = c t := by rw [hinv, one_mul]

theorem expG_lW (θ : ℝ) : hGL2.expG (θ • lW) = kMat θ := by
  apply GL2_ext
  rw [IsExpLieAlgebra.coe_expG, coe_kMat, Submodule.coe_smul, coe_lW]
  have hc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Real.sin s • !![0, 1; -1, 0])
      (!![0, 1; -1, 0] * (Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin s • !![0, 1; -1, 0])) s := by
    intro s
    refine (((Real.hasDerivAt_cos s).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)).add
      ((Real.hasDerivAt_sin s).smul_const (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ))).congr_deriv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_of_hasDerivAt hc (by simp) θ]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

theorem kMat_inv (θ : ℝ) : (kMat θ)⁻¹ = kMat (-θ) := by
  rw [inv_eq_iff_mul_eq_one, ← kMat_add, add_neg_cancel, kMat_zero]

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

theorem exists_cos_sin {p r : ℝ} (h : p ^ 2 + r ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = p ∧ Real.sin θ = r := by
  set z : ℂ := ⟨p, r⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [hz]; nlinarith
  have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hn; norm_num at hn
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hn, div_one]
  · rw [Complex.sin_arg, hn, div_one]

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

theorem orthogonal_cases {O : Matrix (Fin 2) (Fin 2) ℝ} (hO : O ∈ Matrix.unitaryGroup (Fin 2) ℝ) :
    ∃ θ : ℝ, O = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] ∨
      O = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] * !![1, 0; 0, -1] := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hO
  set p := O 0 0
  set q := O 0 1
  set r := O 1 0
  set s := O 1 1
  have h00 := congrFun (congrFun hO 0) 0
  have h01 := congrFun (congrFun hO 0) 1
  have h11 := congrFun (congrFun hO 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11

  have e1 : p ^ 2 + r ^ 2 = 1 := by nlinarith
  have e2 : p * q + r * s = 0 := by nlinarith
  have e3 : q ^ 2 + s ^ 2 = 1 := by nlinarith
  obtain ⟨θ, hc, hs⟩ := exists_cos_sin (p := p) (r := -r) (by nlinarith)
  set μ := p * s - q * r with hμ
  have hq : q = -μ * r := by linear_combination p * e2 - q * e1 + r * hμ
  have hs' : s = μ * p := by linear_combination r * e2 - s * e1 - p * hμ
  have hμ2 : μ ^ 2 = 1 := by
    have : μ ^ 2 * (p ^ 2 + r ^ 2) = q ^ 2 + s ^ 2 := by rw [hq, hs']; ring
    rwa [e1, e3, mul_one] at this
  have hμ' : μ = 1 ∨ μ = -1 := by
    have : (μ - 1) * (μ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  refine ⟨θ, ?_⟩
  rcases hμ' with h1 | h1
  · left
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · exact hc.symm
    · show q = Real.sin θ; rw [hq, h1, hs]; ring
    · show r = -Real.sin θ; rw [hs]; ring
    · show s = Real.cos θ; rw [hs', h1, hc]; ring
  · right
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · exact hc.symm
    · show q = -Real.sin θ; rw [hq, h1, hs]; ring
    · show r = -Real.sin θ; rw [hs]; ring
    · show s = -Real.cos θ; rw [hs', h1, hc]; ring

def iotaMat (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1] * Aᵀ * !![1, 0; 0, -1]

theorem det_iotaMat (A : Matrix (Fin 2) (Fin 2) ℝ) : (iotaMat A).det = A.det := by
  rw [iotaMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp [Matrix.det_fin_two_of]

noncomputable def iotaG (g : FiltrationCocycleLiftCriterion) : FiltrationCocycleLiftCriterion :=
  toGL (iotaMat ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (by rw [det_iotaMat]; exact (Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin 2) ℝ)))

theorem iotaG_mul (g g' : FiltrationCocycleLiftCriterion) : iotaG (g * g') = iotaG g' * iotaG g := by
  apply GL2_ext
  simp only [iotaG, coe_toGL, Subgroup.coe_mul, Units.val_mul, iotaMat, Matrix.transpose_mul]
  have e : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, -1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) !![1, 0; 0, -1], e,
    Matrix.one_mul]

theorem iotaG_kMat (θ : ℝ) : iotaG (kMat θ) = kMat θ := by
  apply GL2_ext
  simp only [iotaG, coe_toGL, coe_kMat]
  ext i j
  simp only [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem iotaG_diag (d₁ d₂ : ℝ) (hd : (!![d₁, 0; 0, d₂] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0) :
    iotaG (toGL !![d₁, 0; 0, d₂] hd) = toGL !![d₁, 0; 0, d₂] hd := by
  apply GL2_ext
  simp only [iotaG, coe_toGL]
  ext i j
  simp only [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_kak (g : FiltrationCocycleLiftCriterion) : ∃ (α β : ℝ) (D : FiltrationCocycleLiftCriterion), iotaG D = D ∧ g = kMat α * D * kMat β := by
  obtain ⟨k₁, k₂, a, -, hg⟩ := exists_KAK (g : GL (Fin 2) ℝ)
  obtain ⟨θ₁, h₁⟩ := orthogonal_cases k₁.2
  obtain ⟨θ₂, h₂⟩ := orthogonal_cases k₂.2
  simp only [RCLike.ofReal_real_eq_id, id] at hg

  have key : ∀ (e₁ e₂ : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ),
      (e₁ = 1 ∨ e₁ = !![1, 0; 0, -1]) → (e₂ = 1 ∨ e₂ = !![1, 0; 0, -1]) →
      (k₁ : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ₁, Real.sin θ₁; -Real.sin θ₁, Real.cos θ₁] * e₁ →
      (k₂ : Matrix (Fin 2) (Fin 2) ℝ) = e₂ * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] →
      ∃ (α β : ℝ) (D : FiltrationCocycleLiftCriterion), iotaG D = D ∧ g = kMat α * D * kMat β := by
    intro e₁ e₂ θ he₁ he₂ hk₁ hk₂
    set M := e₁ * Matrix.diagonal (fun i => a i) * e₂ with hM
    have hMd : ∃ d₁ d₂ : ℝ, M = !![d₁, 0; 0, d₂] := by
      have h01 : M 0 1 = 0 := by
        rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;>
          simp only [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply] <;>
          simp
      have h10 : M 1 0 = 0 := by
        rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;>
          simp only [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply] <;>
          simp
      refine ⟨M 0 0, M 1 1, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10]
    obtain ⟨d₁, d₂, hd⟩ := hMd
    have hgM : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![Real.cos θ₁, Real.sin θ₁; -Real.sin θ₁, Real.cos θ₁] * !![d₁, 0; 0, d₂] *
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
      rw [hg, hk₁, hk₂, ← hd, hM]; simp only [Matrix.mul_assoc]
    have hdet : (!![d₁, 0; 0, d₂] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
      intro h0
      have := Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin 2) ℝ)
      rw [hgM, Matrix.det_mul, Matrix.det_mul, h0] at this
      simp at this
    refine ⟨θ₁, θ, toGL _ hdet, iotaG_diag d₁ d₂ hdet, ?_⟩
    apply GL2_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_kMat, coe_toGL]
    exact hgM
  have hε : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, -1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrot : ∀ θ : ℝ, !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] * (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; 0, -1] * !![Real.cos (-θ), Real.sin (-θ); -Real.sin (-θ), Real.cos (-θ)] := by
    intro θ; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact key 1 1 θ₂ (Or.inl rfl) (Or.inl rfl) (by rw [h₁, Matrix.mul_one]) (by rw [h₂, Matrix.one_mul])
  · exact key 1 _ (-θ₂) (Or.inl rfl) (Or.inr rfl) (by rw [h₁, Matrix.mul_one]) (by rw [h₂, hrot])
  · exact key _ 1 θ₂ (Or.inr rfl) (Or.inl rfl) h₁ (by rw [h₂, Matrix.one_mul])
  · exact key _ _ (-θ₂) (Or.inr rfl) (Or.inr rfl) h₁ (by rw [h₂, hrot])

end GroundTheory.Automorphic.ArchWhittaker
end

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral
open scoped Matrix.Norms.L2Operator Real InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem continuous_kMat : Continuous kMat := by
  have : kMat = fun θ : ℝ => hGL2.expG (θ • lW) := funext fun θ => (expG_lW θ).symm
  rw [this]
  exact hGL2.continuous_expG.comp (continuous_id.smul continuous_const)

theorem kMat_add_two_pi (θ : ℝ) : kMat (θ + 2 * π) = kMat θ := by
  rw [kMat_add, kMat_two_pi, mul_one]

noncomputable def chi (j : ℤ) (θ : ℝ) : ℂ := Complex.exp ((j : ℂ) * θ * I)

theorem chi_add (j : ℤ) (a b : ℝ) : chi j (a + b) = chi j a * chi j b := by
  simp only [chi, ofReal_add, ← Complex.exp_add]; ring_nf

theorem chi_neg (j : ℤ) (a : ℝ) : chi j (-a) = (chi j a)⁻¹ := by
  simp only [chi, ofReal_neg, ← Complex.exp_neg]; ring_nf

theorem chi_mul_chi_neg (j : ℤ) (a : ℝ) : chi j a * chi j (-a) = 1 := by
  rw [chi_neg, mul_inv_cancel₀ (by simp [chi, Complex.exp_ne_zero])]

theorem chi_two_pi (j : ℤ) : chi j (2 * π) = 1 := by
  simp only [chi]
  have := Complex.exp_int_mul_two_pi_mul_I j
  rw [← this]; congr 1; push_cast; ring

theorem continuous_chi (j : ℤ) : Continuous (chi j) := by
  unfold chi; fun_prop

theorem norm_chi (j : ℤ) (a : ℝ) : ‖chi j a‖ = 1 := by
  rw [chi, Complex.norm_exp]
  simp

theorem conj_chi (j : ℤ) (a : ℝ) : (starRingEnd ℂ) (chi j a) = chi j (-a) := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

def weightSpace (j : ℤ) : Submodule ℂ H where
  carrier := {v | ∀ θ : ℝ, σ (kMat θ) v = chi j θ • v}
  add_mem' {v w} hv hw θ := by simp [map_add (f := _), hv θ, hw θ, smul_add]
  zero_mem' θ := by simp
  smul_mem' c v hv θ := by simp [hv θ, smul_comm c]

noncomputable def wProj (j : ℤ) (x : H) : H :=
  ((2 * π : ℝ)⁻¹ : ℂ) • ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x

theorem continuous_orbit_kMat (x : H) : Continuous fun θ : ℝ => σ (kMat θ) x :=
  (σ.continuous_orbit x).comp continuous_kMat

theorem continuous_wIntegrand (j : ℤ) (x : H) :
    Continuous fun θ : ℝ => chi j (-θ) • σ (kMat θ) x :=
  ((continuous_chi j).comp continuous_neg).smul (continuous_orbit_kMat σ x)

theorem wProj_mem (j : ℤ) (x : H) : wProj σ j x ∈ weightSpace σ j := by
  intro φ
  have hper : Function.Periodic (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) (2 * π) := by
    intro θ
    simp only [kMat_add_two_pi, neg_add, chi_add, chi_neg j (2 * π), chi_two_pi, inv_one, mul_one]
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have h1 : σ (kMat φ) (∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j φ • (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) := by
    rw [← (σ (kMat φ)).intervalIntegral_comp_comm hint]
    congr 1; funext θ
    simp only [map_smul, ← UnitaryRep.map_mul_apply, ← kMat_add, smul_smul, neg_add, chi_add]
    congr 1
    rw [← mul_assoc, chi_mul_chi_neg, one_mul]
  have h2 : ∫ θ in (0 : ℝ)..(2 * π), (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x := by
    rw [intervalIntegral.integral_comp_add_left (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) φ, add_zero]
    have := hper.intervalIntegral_add_eq φ 0
    rw [zero_add] at this
    exact this
  unfold wProj
  rw [map_smul, h1, intervalIntegral.integral_smul, h2, smul_comm]

theorem inner_wProj (j : ℤ) (x y : H) :
    ⟪y, wProj σ j x⟫_ℂ = ((2 * π : ℝ)⁻¹ : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) * ⟪y, σ (kMat θ) x⟫_ℂ := by
  rw [wProj, inner_smul_right]
  congr 1
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have := (innerSL ℂ y).intervalIntegral_comp_comm hint
  simp only [innerSL_apply_apply, inner_smul_right] at this
  exact this.symm

theorem norm_wProj_le (j : ℤ) (x : H) : ‖wProj σ j x‖ ≤ ‖x‖ := by
  rw [wProj, norm_smul]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖ ≤ ‖x‖ * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_chi, one_mul, UnitaryRep.norm_map]
  rw [sub_zero, abs_of_pos (by positivity)] at hb
  have hn : ‖((2 * π : ℝ)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖
      ≤ (2 * π)⁻¹ * (‖x‖ * (2 * π)) := by gcongr
    _ = ‖x‖ := by field_simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

end GroundTheory.Automorphic.ArchWhittaker
end

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ComplexConjugate ComplexStarModule

section Schur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem eq_algebraMap_of_commute [Nontrivial V] {S : Set (V →L[ℂ] V)}
    (hirr : ∀ W : Submodule ℂ V, IsClosed (W : Set V) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {A : V →L[ℂ] V} (hsa : IsSelfAdjoint A) (hcomm : ∀ s ∈ S, Commute A s) :
    ∃ c : ℝ, A = algebraMap ℝ (V →L[ℂ] V) c := by
  have hnt : Nontrivial (V →L[ℂ] V) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : V →L[ℂ] V => T v) h)⟩⟩
  have hsub : (spectrum ℝ A).Subsingleton := by
    intro a ha b hb
    by_contra hab
    wlog hlt : a < b generalizing a b
    · exact this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
    set c := (a + b) / 2 with hc
    let f : ℝ → ℝ := fun x => max (x - c) 0
    let g : ℝ → ℝ := fun x => max (c - x) 0
    have hfc : Continuous f := by fun_prop
    have hgc : Continuous g := by fun_prop
    have hgf : (fun x => g x * f x) = (0 : ℝ → ℝ) := by
      funext x
      rcases le_total x c with h | h
      · simp [f, max_eq_right (sub_nonpos.mpr h)]
      · simp [g, max_eq_right (sub_nonpos.mpr h)]
    have hQP : cfc g A * cfc f A = 0 := by
      rw [← cfc_mul g f A hgc.continuousOn hfc.continuousOn, hgf, cfc_zero]
    have hne : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ x ∈ spectrum ℝ A, φ x ≠ 0 → cfc φ A ≠ 0 := by
      intro φ hφ x hx hφx h
      have hs : spectrum ℝ (cfc φ A) = φ '' spectrum ℝ A := cfc_map_spectrum φ A hsa hφ.continuousOn
      have hmem : φ x ∈ spectrum ℝ (cfc φ A) := hs ▸ ⟨x, hx, rfl⟩
      rw [h, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
      exact hφx hmem
    have hP0 : cfc f A ≠ 0 := hne f hfc b hb (by
      simp only [f]; rw [max_eq_left (by linarith)]; linarith)
    have hQ0 : cfc g A ≠ 0 := hne g hgc a ha (by
      simp only [g]; rw [max_eq_left (by linarith)]; linarith)
    have hPcomm : ∀ s ∈ S, Commute (cfc f A) s := fun s hs =>
      (hcomm s hs).cfc_real f
    set W := (LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V)).topologicalClosure with hW
    have hinv : ∀ s ∈ S, ∀ v ∈ W, s v ∈ W := by
      intro s hs v hv
      have hle : LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V) ≤
          W.comap ((s : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
        rintro _ ⟨u, rfl⟩
        simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
        have : s (cfc f A u) = cfc f A (s u) := by
          have := congrArg (fun T : V →L[ℂ] V => T u) (hPcomm s hs).eq
          simpa using this.symm
        rw [this]
        exact Submodule.le_topologicalClosure _ ⟨s u, rfl⟩
      have hcl : IsClosed ((W.comap ((s : V →L[ℂ] V) : V →ₗ[ℂ] V) : Submodule ℂ V) : Set V) :=
        (Submodule.isClosed_topologicalClosure _).preimage s.continuous
      exact Submodule.topologicalClosure_minimal _ hle hcl hv
    rcases hirr W (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
    · apply hP0
      ext v
      have : cfc f A v ∈ W := Submodule.le_topologicalClosure _ ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      simpa using this
    · apply hQ0
      have hle : LinearMap.range ((cfc f A : V →L[ℂ] V) : V →ₗ[ℂ] V) ≤
          LinearMap.ker ((cfc g A : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
        rintro _ ⟨v, rfl⟩
        simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
        have := congrArg (fun T : V →L[ℂ] V => T v) hQP
        simpa using this
      have hcl := Submodule.topologicalClosure_minimal _ hle (cfc g A).isClosed_ker
      rw [← hW, htop] at hcl
      ext v
      have : v ∈ LinearMap.ker ((cfc g A : V →L[ℂ] V) : V →ₗ[ℂ] V) := hcl Submodule.mem_top
      simpa using this
  have hne : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hsa
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hsa).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hsub hx hc
    _ = algebraMap ℝ _ c := cfc_const c A hsa

theorem eq_smul_one_of_commute [Nontrivial V] {S : Set (V →L[ℂ] V)}
    (hirr : ∀ W : Submodule ℂ V, IsClosed (W : Set V) → (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (hstar : ∀ s ∈ S, star s ∈ S) (hcomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t)
    {T : V →L[ℂ] V} (hT : T ∈ S) : ∃ c : ℂ, T = c • (1 : V →L[ℂ] V) := by
  have hre : ∀ s ∈ S, Commute (ℜ T : V →L[ℂ] V) s := by
    intro s hs
    rw [realPart_apply_coe]
    exact ((hcomm T hT s hs).add_left (hcomm _ (hstar T hT) s hs)).smul_left _
  have him : ∀ s ∈ S, Commute (ℑ T : V →L[ℂ] V) s := by
    intro s hs
    rw [imaginaryPart_apply_coe]
    exact (((hcomm T hT s hs).sub_left (hcomm _ (hstar T hT) s hs)).smul_left _).smul_left _
  obtain ⟨a, ha⟩ := eq_algebraMap_of_commute hirr (ℜ T).2 hre
  obtain ⟨b, hb⟩ := eq_algebraMap_of_commute hirr (ℑ T).2 him
  refine ⟨a + I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

end Schur

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ComplexConjugate ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem topologicalClosure_span_orbit {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : UnitaryRep G H} (hρ : ρ.IsIrreducible) {x : H} (hx : x ≠ 0) :
    (Submodule.span ℂ (range fun g => ρ g x)).topologicalClosure = ⊤ := by
  set U := (Submodule.span ℂ (range fun g => ρ g x)).topologicalClosure with hU
  have hinv : ρ.IsInvariant U := by
    intro g v hv
    have hle : Submodule.span ℂ (range fun g => ρ g x) ≤ U.comap ((ρ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
      rw [← UnitaryRep.map_mul_apply]
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g * h, rfl⟩)
    have hcl : IsClosed ((U.comap ((ρ g : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.isClosed_topologicalClosure _).preimage (ρ g).continuous
    exact Submodule.topologicalClosure_minimal _ hle hcl hv
  rcases hρ.2 U (Submodule.isClosed_topologicalClosure _) hinv with h | h
  · exfalso; apply hx
    have : x ∈ U := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, by simp⟩)
    rw [h, Submodule.mem_bot] at this
    exact this
  · exact h

theorem eq_zero_of_forall_inner_map {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : UnitaryRep G H} (hρ : ρ.IsIrreducible) {x y : H} (hx : x ≠ 0)
    (h : ∀ g, ⟪y, ρ g x⟫_ℂ = 0) : y = 0 := by
  have htop := topologicalClosure_span_orbit hρ hx
  have hle : Submodule.span ℂ (range fun g => ρ g x) ≤ (ℂ ∙ y)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h g
  have hcl := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
  rw [htop] at hcl
  have hy : y ∈ (ℂ ∙ y)ᗮ := hcl Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hy
  exact hy

variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem inner_map_kMat_of_mem {j : ℤ} {y : H} (hy : y ∈ weightSpace σ j) (θ : ℝ) (u : H) :
    ⟪y, σ (kMat θ) u⟫_ℂ = chi j θ * ⟪y, u⟫_ℂ := by
  rw [UnitaryRep.inner_map_right, kMat_inv, hy (-θ), inner_smul_left, conj_chi, neg_neg]

theorem inner_wProj_of_mem {j : ℤ} {y : H} (hy : y ∈ weightSpace σ j) (u : H) :
    ⟪y, wProj σ j u⟫_ℂ = ⟪y, u⟫_ℂ := by
  rw [inner_wProj]
  have : (fun θ : ℝ => chi j (-θ) * ⟪y, σ (kMat θ) u⟫_ℂ) = fun _ => ⟪y, u⟫_ℂ := by
    funext θ
    rw [inner_map_kMat_of_mem σ hy, ← mul_assoc, mul_comm (chi j (-θ)), chi_mul_chi_neg, one_mul]
  rw [this, intervalIntegral.integral_const, sub_zero, Complex.real_smul, ← mul_assoc]
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [inv_mul_cancel₀ hπ, one_mul]

theorem wProj_add (j : ℤ) (x y : H) : wProj σ j (x + y) = wProj σ j x + wProj σ j y := by
  simp only [wProj, map_add (f := _), smul_add]
  rw [intervalIntegral.integral_add ((continuous_wIntegrand σ j x).intervalIntegrable _ _)
    ((continuous_wIntegrand σ j y).intervalIntegrable _ _), smul_add]

theorem wProj_smul (j : ℤ) (c : ℂ) (x : H) : wProj σ j (c • x) = c • wProj σ j x := by
  simp only [wProj, map_smul, smul_comm _ c]
  rw [intervalIntegral.integral_smul, smul_comm]

noncomputable def wProjL (j : ℤ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := wProj σ j
      map_add' := wProj_add σ j
      map_smul' := wProj_smul σ j } 1 (fun x => by simpa using norm_wProj_le σ j x)

noncomputable def compr (j : ℤ) (g : FiltrationCocycleLiftCriterion) : weightSpace σ j →L[ℂ] weightSpace σ j :=
  ((wProjL σ j).comp ((σ g).comp (weightSpace σ j).subtypeL)).codRestrict (weightSpace σ j)
    (fun x => wProj_mem σ j _)

@[simp] theorem coe_compr_apply (j : ℤ) (g : FiltrationCocycleLiftCriterion) (v : weightSpace σ j) :
    ((compr σ j g v : weightSpace σ j) : H) = wProj σ j (σ g v) := rfl

theorem inner_compr (j : ℤ) (g : FiltrationCocycleLiftCriterion) (v w : weightSpace σ j) :
    ⟪(w : H), (compr σ j g v : H)⟫_ℂ = ⟪(w : H), σ g v⟫_ℂ := by
  rw [coe_compr_apply, inner_wProj_of_mem σ w.2]

theorem inner_map_iotaG {j : ℤ} {x y : H} (hx : x ∈ weightSpace σ j) (hy : y ∈ weightSpace σ j)
    (u : FiltrationCocycleLiftCriterion) : ⟪y, σ (iotaG u) x⟫_ℂ = ⟪y, σ u x⟫_ℂ := by
  have key : ∀ (a b : ℝ) (D : FiltrationCocycleLiftCriterion), ⟪y, σ (kMat a * D * kMat b) x⟫_ℂ =
      chi j a * chi j b * ⟪y, σ D x⟫_ℂ := by
    intro a b D
    rw [UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, hx b, map_smul, map_smul,
      inner_smul_right, inner_map_kMat_of_mem σ hy]
    ring
  obtain ⟨α, β, D, hD, rfl⟩ := exists_kak u
  rw [iotaG_mul, iotaG_mul, iotaG_kMat, iotaG_kMat, hD, ← mul_assoc, key, key]
  ring

theorem inner_compr_compr (j : ℤ) (g h : FiltrationCocycleLiftCriterion) (v w : weightSpace σ j) :
    ⟪(w : H), (compr σ j g (compr σ j h v) : H)⟫_ℂ = ((2 * π : ℝ)⁻¹ : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) * ⟪(w : H), σ (g * kMat θ * h) v⟫_ℂ := by
  rw [inner_compr, coe_compr_apply, UnitaryRep.inner_map_right, inner_wProj]
  congr 1
  congr 1; funext θ
  rw [UnitaryRep.inner_map_left, inv_inv, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply,
    mul_assoc]

theorem compr_iotaG (j : ℤ) (g : FiltrationCocycleLiftCriterion) : compr σ j (iotaG g) = compr σ j g := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  rw [Submodule.coe_inner, Submodule.coe_inner, inner_compr, inner_compr,
    inner_map_iotaG σ v.2 w.2]

theorem compr_comm (j : ℤ) (g h : FiltrationCocycleLiftCriterion) : compr σ j g * compr σ j h = compr σ j h * compr σ j g := by
  ext1 v
  apply ext_inner_left ℂ
  intro w
  rw [Submodule.coe_inner, Submodule.coe_inner, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, inner_compr_compr, ← compr_iotaG σ j h, ← compr_iotaG σ j g,
    inner_compr_compr]
  congr 1
  congr 1; funext θ
  rw [← inner_map_iotaG σ v.2 w.2 (g * kMat θ * h), iotaG_mul, iotaG_mul, iotaG_kMat, mul_assoc]

end GroundTheory.Automorphic.ArchWhittaker
