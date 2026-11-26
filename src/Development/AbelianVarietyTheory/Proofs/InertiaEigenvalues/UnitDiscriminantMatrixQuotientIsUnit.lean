module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixDecompose

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory

theorem norm_det_le_one_of_entries_le_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  intro E _ _ n x hx
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, x (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, norm_neg]; exact hp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOneStatement
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  first | exact @GlobalTheory.norm_det_le_one_of_entries_le_one | exact GlobalTheory.norm_det_le_one_of_entries_le_one | (intros; apply GlobalTheory.norm_det_le_one_of_entries_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitAndIntegInvOfNormDetEqOne
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg

theorem integ_det_le {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {m : ℕ}
    (y : Matrix (Fin m) (Fin m) E) (hy : ∀ i j, ‖y i j‖ ≤ 1) : ‖y.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : E)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hy _ _)

theorem isUnit_and_integ_inv_of_norm_det_eq_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ = 1 →
      IsUnit x ∧ ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro E _ _ n x hx hdet
  have hne : x.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hne)
  refine ⟨hu, fun i j => ?_⟩
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    hdet, inv_one, one_mul, Matrix.adjugate_apply]
  apply integ_det_le
  intro a b
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs <;> simp
  · exact hx a b

end GlobalTheory.UnitDiscAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnit
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg.QuotAlg

section Comm
variable {R : Type*} [CommRing R]

theorem eq_of_comp {e₁ e₂ e₃ x y : R} (hs : e₁ + e₂ + e₃ = 1)
    (h1 : x * e₁ = y * e₁) (h2 : x * e₂ = y * e₂) (h3 : x * e₃ = y * e₃) : x = y := by
  linear_combination h1 + h2 + h3 - (x - y) * hs

theorem cm_mul {e x y α β : R} (hx : x * e = α * e) (hy : y * e = β * e) :
    x * y * e = α * β * e := by
  linear_combination y * hx + α * hy

theorem comp1 {e₁ e₂ e₃ : R} (h11 : e₁ * e₁ = e₁) (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₁ = α * e₁ := by
  linear_combination α * h11 + β * h12 + γ * h13

theorem comp2 {e₁ e₂ e₃ : R} (h12 : e₁ * e₂ = 0) (h22 : e₂ * e₂ = e₂) (h23 : e₂ * e₃ = 0)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₂ = β * e₂ := by
  linear_combination α * h12 + β * h22 + γ * h23

theorem comp3 {e₁ e₂ e₃ : R} (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (h33 : e₃ * e₃ = e₃)
    (α β γ : R) : (α * e₁ + β * e₂ + γ * e₃) * e₃ = γ * e₃ := by
  linear_combination α * h13 + β * h23 + γ * h33

theorem core (p pi c ci u a₂ a₃ b e₁ e₂ e₃ k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 : R)
    (hp : p * pi = 1) (hci : c * ci = 1)
    (h11 : e₁ * e₁ = e₁) (h22 : e₂ * e₂ = e₂) (h33 : e₃ * e₃ = e₃)
    (h12 : e₁ * e₂ = 0) (h13 : e₁ * e₃ = 0) (h23 : e₂ * e₃ = 0) (hs : e₁ + e₂ + e₃ = 1)
    (hc1 : c * e₁ = u * e₁) (hc2 : c * e₂ = p * (a₂ * e₂)) (hc3 : ci * e₃ = p * (a₃ * e₃))
    (hk11 : (p + u ^ 2) * k11 = 1) (hk12 : (1 + p * a₂ ^ 2) * k12 = 1)
    (hk13 : (1 + p ^ 3 * a₃ ^ 2) * k13 = 1)
    (hk21 : (p + u ^ 3) * k21 = 1) (hk22 : (1 + p ^ 2 * a₂ ^ 3) * k22 = 1)
    (hk23 : (1 + p ^ 4 * a₃ ^ 3) * k23 = 1)
    (hk31 : (p * u ^ 2 + b ^ 2) * k31 = 1) (hk32 : (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 = 1)
    (hk33 : (1 + p * b ^ 2 * a₃ ^ 2) * k33 = 1)
    (hk41 : (p * u ^ 3 + b ^ 3) * k41 = 1) (hk42 : (b ^ 3 + p ^ 4 * a₂ ^ 3) * k42 = 1)
    (hk43 : (1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * k43 = 1) :
    (p + c ^ 2) * (k11 * e₁ + (pi * k12) * e₂ + (ci ^ 2 * k13) * e₃) = 1 ∧
    (p + c ^ 3) * (k21 * e₁ + (pi * k22) * e₂ + (ci ^ 3 * k23) * e₃) = 1 ∧
    (p * c ^ 2 + b ^ 2) * (k31 * e₁ + k32 * e₂ + (pi * ci ^ 2 * k33) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (k41 * e₁ + k42 * e₂ + (pi * ci ^ 3 * k43) * e₃) = 1 ∧
    (p * c ^ 3 + b ^ 3) * (p + c ^ 2) =
      (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃)
        * ((p + c ^ 3) * (p * c ^ 2 + b ^ 2)) ∧
    (((p * u ^ 3 + b ^ 3) * (p + u ^ 2) * k21 * k31) * e₁
        + ((b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * k22 * k32) * e₂
        + ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * k23 * k33) * e₃) *
      (((p + u ^ 3) * (p * u ^ 2 + b ^ 2) * k41 * k11) * e₁
        + ((1 + p ^ 2 * a₂ ^ 3) * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k42 * k12) * e₂
        + ((1 + p ^ 4 * a₃ ^ 3) * (1 + p * b ^ 2 * a₃ ^ 2) * k43 * k13) * e₃) = 1 := by
  have hd3 : e₃ = p * c * a₃ * e₃ := by linear_combination c * hc3 - e₃ * hci

  have LargeParameterEstimates : (p + c ^ 2) * e₁ = ((p + u ^ 2) * 1) * e₁ := by linear_combination (c + u) * hc1
  have F12 : (p + c ^ 2) * e₂ = ((1 + p * a₂ ^ 2) * p) * e₂ := by
    linear_combination (c + p * a₂) * hc2
  have InertPlaceConditions : (p + c ^ 2) * e₃ = ((1 + p ^ 3 * a₃ ^ 2) * c ^ 2) * e₃ := by
    linear_combination p * (1 + p * c * a₃) * hd3
  have F21 : (p + c ^ 3) * e₁ = ((p + u ^ 3) * 1) * e₁ := by
    linear_combination (c ^ 2 + c * u + u ^ 2) * hc1
  have F22 : (p + c ^ 3) * e₂ = ((1 + p ^ 2 * a₂ ^ 3) * p) * e₂ := by
    linear_combination (c ^ 2 + c * p * a₂ + p ^ 2 * a₂ ^ 2) * hc2
  have F23 : (p + c ^ 3) * e₃ = ((1 + p ^ 4 * a₃ ^ 3) * c ^ 3) * e₃ := by
    linear_combination p * (1 + p * c * a₃ + (p * c * a₃) ^ 2) * hd3
  have F31 : (p * c ^ 2 + b ^ 2) * e₁ = ((p * u ^ 2 + b ^ 2) * 1) * e₁ := by
    linear_combination p * (c + u) * hc1
  have F32 : (p * c ^ 2 + b ^ 2) * e₂ = ((b ^ 2 + p ^ 3 * a₂ ^ 2) * 1) * e₂ := by
    linear_combination p * (c + p * a₂) * hc2
  have F33 : (p * c ^ 2 + b ^ 2) * e₃ = ((1 + p * b ^ 2 * a₃ ^ 2) * (p * c ^ 2)) * e₃ := by
    linear_combination b ^ 2 * (1 + p * c * a₃) * hd3
  have F41 : (p * c ^ 3 + b ^ 3) * e₁ = ((p * u ^ 3 + b ^ 3) * 1) * e₁ := by
    linear_combination p * (c ^ 2 + c * u + u ^ 2) * hc1
  have F42 : (p * c ^ 3 + b ^ 3) * e₂ = ((b ^ 3 + p ^ 4 * a₂ ^ 3) * 1) * e₂ := by
    linear_combination p * (c ^ 2 + c * p * a₂ + p ^ 2 * a₂ ^ 2) * hc2
  have F43 : (p * c ^ 3 + b ^ 3) * e₃ = ((1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (p * c ^ 3)) * e₃ := by
    linear_combination b ^ 3 * (1 + p * c * a₃ + (p * c * a₃) ^ 2) * hd3
  have c1 := comp1 h11 h12 h13
  have c2 := comp2 h12 h22 h23
  have c3 := comp3 h13 h23 h33
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul LargeParameterEstimates (c1 _ _ _)]; linear_combination e₁ * hk11
    · rw [cm_mul F12 (c2 _ _ _)]; linear_combination e₂ * p * pi * hk12 + e₂ * hp
    · rw [cm_mul InertPlaceConditions (c3 _ _ _)]
      linear_combination e₃ * (c * ci) ^ 2 * hk13 + e₃ * (c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F21 (c1 _ _ _)]; linear_combination e₁ * hk21
    · rw [cm_mul F22 (c2 _ _ _)]; linear_combination e₂ * p * pi * hk22 + e₂ * hp
    · rw [cm_mul F23 (c3 _ _ _)]
      linear_combination e₃ * (c * ci) ^ 3 * hk23 + e₃ * ((c * ci) ^ 2 + c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F31 (c1 _ _ _)]; linear_combination e₁ * hk31
    · rw [cm_mul F32 (c2 _ _ _)]; linear_combination e₂ * hk32
    · rw [cm_mul F33 (c3 _ _ _)]
      linear_combination e₃ * p * pi * (c * ci) ^ 2 * hk33 + e₃ * (c * ci) ^ 2 * hp
        + e₃ * (c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F41 (c1 _ _ _)]; linear_combination e₁ * hk41
    · rw [cm_mul F42 (c2 _ _ _)]; linear_combination e₂ * hk42
    · rw [cm_mul F43 (c3 _ _ _)]
      linear_combination e₃ * p * pi * (c * ci) ^ 3 * hk43 + e₃ * (c * ci) ^ 3 * hp
        + e₃ * ((c * ci) ^ 2 + c * ci + 1) * hci
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul F41 LargeParameterEstimates, cm_mul (c1 _ _ _) (cm_mul F21 F31)]
      linear_combination (-(p * u ^ 3 + b ^ 3) * (p + u ^ 2) * e₁) * ((p * u ^ 2 + b ^ 2) * k31 * hk21 + hk31)
    · rw [cm_mul F42 F12, cm_mul (c2 _ _ _) (cm_mul F22 F32)]
      linear_combination (-(b ^ 3 + p ^ 4 * a₂ ^ 3) * (1 + p * a₂ ^ 2) * p * e₂) * ((b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * hk22 + hk32)
    · rw [cm_mul F43 InertPlaceConditions, cm_mul (c3 _ _ _) (cm_mul F23 F33)]
      linear_combination (-(1 + p ^ 2 * b ^ 3 * a₃ ^ 3) * (1 + p ^ 3 * a₃ ^ 2) * p * c ^ 5 * e₃) * ((1 + p * b ^ 2 * a₃ ^ 2) * k33 * hk23 + hk33)
  · refine eq_of_comp hs ?_ ?_ ?_
    · rw [cm_mul (c1 _ _ _) (c1 _ _ _)]
      linear_combination e₁ * ((p + u ^ 3) * k21 * (p * u ^ 2 + b ^ 2) * k31 * (p + u ^ 2) * k11 * hk41
        + (p + u ^ 3) * k21 * (p * u ^ 2 + b ^ 2) * k31 * hk11 + (p + u ^ 3) * k21 * hk31 + hk21)
    · rw [cm_mul (c2 _ _ _) (c2 _ _ _)]
      linear_combination e₂ * ((1 + p ^ 2 * a₂ ^ 3) * k22 * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * (1 + p * a₂ ^ 2) * k12 * hk42
        + (1 + p ^ 2 * a₂ ^ 3) * k22 * (b ^ 2 + p ^ 3 * a₂ ^ 2) * k32 * hk12 + (1 + p ^ 2 * a₂ ^ 3) * k22 * hk32 + hk22)
    · rw [cm_mul (c3 _ _ _) (c3 _ _ _)]
      linear_combination e₃ * ((1 + p ^ 4 * a₃ ^ 3) * k23 * (1 + p * b ^ 2 * a₃ ^ 2) * k33 * (1 + p ^ 3 * a₃ ^ 2) * k13 * hk43
        + (1 + p ^ 4 * a₃ ^ 3) * k23 * (1 + p * b ^ 2 * a₃ ^ 2) * k33 * hk13 + (1 + p ^ 4 * a₃ ^ 3) * k23 * hk33 + hk23)

end Comm
end GlobalTheory.UnitDiscAlg.QuotAlg

namespace GlobalTheory.UnitDiscAlg.QuotAlg

theorem eq_one_of_mul_eq_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hab : a * b = 1) : a = 1 := by nlinarith

theorem inv_comm {E : Type} [Field E] {n : ℕ} {x N : Matrix (Fin n) (Fin n) E}
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by
  by_cases hd : IsUnit x.det
  · calc x⁻¹ * N = x⁻¹ * N * (x * x⁻¹) := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = x⁻¹ * (x * N) * x⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
      _ = N * x⁻¹ := by rw [← Matrix.mul_assoc x⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]; simp

theorem quotient_integral_unit : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ n N c b e₁ e₂ e₃ u a₂ a₃ ϖ hϖ0 hϖ1 hcomm hcu hcN hbN hbI hbd hN hI hud h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3
  obtain ⟨he₁N, he₂N, he₃N, huN, ha₂N, ha₃N⟩ := hN
  have hϖne : ϖ ≠ 0 := norm_pos_iff.1 hϖ0
  have hϖle : ‖ϖ‖ ≤ 1 := hϖ1.le
  set S := Subalgebra.centralizer E ({N} : Set (Matrix (Fin n) (Fin n) E)) with hS
  have memN : ∀ x : S, x.1 * N = N * x.1 := fun x =>
    ((Subalgebra.mem_centralizer_iff E).1 x.2 N rfl).symm
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun x y => Subtype.ext (hcomm _ _ (memN x) (memN y)) }
  have mem : ∀ x : Matrix (Fin n) (Fin n) E, x * N = N * x → x ∈ S := fun x hx =>
    (Subalgebra.mem_centralizer_iff E).2
      (fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hx.symm)
  have I_mul : ∀ x y : S, (∀ i j, ‖x.1 i j‖ ≤ 1) → (∀ i j, ‖y.1 i j‖ ≤ 1) →
      ∀ i j, ‖(x * y).1 i j‖ ≤ 1 := fun x y hx hy => integ_mul hx hy
  have I_add : ∀ x y : S, (∀ i j, ‖x.1 i j‖ ≤ 1) → (∀ i j, ‖y.1 i j‖ ≤ 1) →
      ∀ i j, ‖(x + y).1 i j‖ ≤ 1 := fun x y hx hy => integ_add hx hy
  have I_pow : ∀ (x : S) (k : ℕ), (∀ i j, ‖x.1 i j‖ ≤ 1) → ∀ i j, ‖(x ^ k).1 i j‖ ≤ 1 :=
    fun x k hx => integ_pow hx k
  have I_one : ∀ i j, ‖(1 : S).1 i j‖ ≤ 1 := integ_one
  have isU : ∀ x y : S, x * y = 1 → IsUnit x.1 := fun x y h =>
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse
      (congrArg Subtype.val h : x.1 * y.1 = 1))

  have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hcu
  obtain ⟨hu, huiI⟩ :=
    isUnit_and_integ_inv_of_norm_det_eq_one E n u (fun i j => (hI i j).2.2.2.1) hud
  obtain ⟨hb, hbiI⟩ := isUnit_and_integ_inv_of_norm_det_eq_one E n b hbI hbd
  obtain ⟨C, hCv⟩ : ∃ X : S, X.1 = c := ⟨⟨c, mem c hcN⟩, rfl⟩
  obtain ⟨Ci, hCiv⟩ : ∃ X : S, X.1 = c⁻¹ := ⟨⟨c⁻¹, mem _ (inv_comm hcN)⟩, rfl⟩
  obtain ⟨U, hUv⟩ : ∃ X : S, X.1 = u := ⟨⟨u, mem u huN⟩, rfl⟩
  obtain ⟨Ui, hUiv⟩ : ∃ X : S, X.1 = u⁻¹ := ⟨⟨u⁻¹, mem _ (inv_comm huN)⟩, rfl⟩
  obtain ⟨B, hBv⟩ : ∃ X : S, X.1 = b := ⟨⟨b, mem b hbN⟩, rfl⟩
  obtain ⟨Bi, hBiv⟩ : ∃ X : S, X.1 = b⁻¹ := ⟨⟨b⁻¹, mem _ (inv_comm hbN)⟩, rfl⟩
  obtain ⟨A2, hA2v⟩ : ∃ X : S, X.1 = a₂ := ⟨⟨a₂, mem _ ha₂N⟩, rfl⟩
  obtain ⟨A3, hA3v⟩ : ∃ X : S, X.1 = a₃ := ⟨⟨a₃, mem _ ha₃N⟩, rfl⟩
  obtain ⟨E1, hE1v⟩ : ∃ X : S, X.1 = e₁ := ⟨⟨e₁, mem _ he₁N⟩, rfl⟩
  obtain ⟨E2, hE2v⟩ : ∃ X : S, X.1 = e₂ := ⟨⟨e₂, mem _ he₂N⟩, rfl⟩
  obtain ⟨E3, hE3v⟩ : ∃ X : S, X.1 = e₃ := ⟨⟨e₃, mem _ he₃N⟩, rfl⟩
  obtain ⟨P, hPv⟩ : ∃ X : S, X.1 = ϖ • 1 :=
    ⟨⟨_, mem _ (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])⟩, rfl⟩
  obtain ⟨Pi, hPiv⟩ : ∃ X : S, X.1 = ϖ⁻¹ • 1 :=
    ⟨⟨_, mem _ (by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])⟩, rfl⟩
  have IU : ∀ i j, ‖U.1 i j‖ ≤ 1 := by rw [hUv]; exact fun i j => (hI i j).2.2.2.1
  have IUi : ∀ i j, ‖Ui.1 i j‖ ≤ 1 := by rw [hUiv]; exact huiI
  have IB : ∀ i j, ‖B.1 i j‖ ≤ 1 := by rw [hBv]; exact hbI
  have IBi : ∀ i j, ‖Bi.1 i j‖ ≤ 1 := by rw [hBiv]; exact hbiI
  have IA2 : ∀ i j, ‖A2.1 i j‖ ≤ 1 := by rw [hA2v]; exact fun i j => (hI i j).2.2.2.2.1
  have NearKilling : ∀ i j, ‖A3.1 i j‖ ≤ 1 := by rw [hA3v]; exact fun i j => (hI i j).2.2.2.2.2
  have IE1 : ∀ i j, ‖E1.1 i j‖ ≤ 1 := by rw [hE1v]; exact fun i j => (hI i j).1
  have IE2 : ∀ i j, ‖E2.1 i j‖ ≤ 1 := by rw [hE2v]; exact fun i j => (hI i j).2.1
  have IE3 : ∀ i j, ‖E3.1 i j‖ ≤ 1 := by rw [hE3v]; exact fun i j => (hI i j).2.2.1
  have IP : ∀ i j, ‖P.1 i j‖ ≤ 1 := by rw [hPv]; exact integ_smul hϖle integ_one
  have hUd : ‖U.1.det‖ = 1 := by rw [hUv]; exact hud
  have hBd : ‖B.1.det‖ = 1 := by rw [hBv]; exact hbd

  have hp : P * Pi = 1 := Subtype.ext (by
    show P.1 * Pi.1 = 1
    rw [hPv, hPiv, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hϖne, one_smul])
  have hci : C * Ci = 1 := Subtype.ext (by
    show C.1 * Ci.1 = 1
    rw [hCv, hCiv]; exact Matrix.mul_nonsing_inv c hcd)
  have hUi : U * Ui = 1 := Subtype.ext (by
    show U.1 * Ui.1 = 1
    rw [hUv, hUiv]; exact Matrix.mul_nonsing_inv u ((Matrix.isUnit_iff_isUnit_det u).1 hu))
  have hBi : B * Bi = 1 := Subtype.ext (by
    show B.1 * Bi.1 = 1
    rw [hBv, hBiv]; exact Matrix.mul_nonsing_inv b ((Matrix.isUnit_iff_isUnit_det b).1 hb))
  have h11S : E1 * E1 = E1 := Subtype.ext (by show E1.1 * E1.1 = E1.1; rw [hE1v]; exact h11)
  have h22S : E2 * E2 = E2 := Subtype.ext (by show E2.1 * E2.1 = E2.1; rw [hE2v]; exact h22)
  have h33S : E3 * E3 = E3 := Subtype.ext (by show E3.1 * E3.1 = E3.1; rw [hE3v]; exact h33)
  have h12S : E1 * E2 = 0 := Subtype.ext (by show E1.1 * E2.1 = 0; rw [hE1v, hE2v]; exact h12)
  have h13S : E1 * E3 = 0 := Subtype.ext (by show E1.1 * E3.1 = 0; rw [hE1v, hE3v]; exact h13)
  have h23S : E2 * E3 = 0 := Subtype.ext (by show E2.1 * E3.1 = 0; rw [hE2v, hE3v]; exact h23)
  have hsS : E1 + E2 + E3 = 1 := Subtype.ext (by
    show E1.1 + E2.1 + E3.1 = 1; rw [hE1v, hE2v, hE3v]; exact hs)
  have hc1S : C * E1 = U * E1 := Subtype.ext (by
    show C.1 * E1.1 = U.1 * E1.1; rw [hCv, hE1v, hUv]; exact hc1)
  have hc2S : C * E2 = P * (A2 * E2) := Subtype.ext (by
    show C.1 * E2.1 = P.1 * (A2.1 * E2.1)
    rw [hCv, hE2v, hPv, hA2v, Matrix.smul_mul, Matrix.one_mul]; exact hc2)
  have hc3S : Ci * E3 = P * (A3 * E3) := Subtype.ext (by
    show Ci.1 * E3.1 = P.1 * (A3.1 * E3.1)
    rw [hCiv, hE3v, hPv, hA3v, Matrix.smul_mul, Matrix.one_mul]; exact hc3)

  have mk : ∀ g w x : S, g = w * (1 + P * x) → (∀ i j, ‖w.1 i j‖ ≤ 1) → ‖w.1.det‖ = 1 →
      (∀ i j, ‖x.1 i j‖ ≤ 1) → ∃ k : S, g * k = 1 ∧ ∀ i j, ‖k.1 i j‖ ≤ 1 := by
    intro g w x hg hw hwd hx
    have hgv : g.1 = w.1 * (1 + ϖ • x.1) := by
      rw [hg]; show w.1 * (1 + P.1 * x.1) = _; rw [hPv, Matrix.smul_mul, Matrix.one_mul]
    have hgI : ∀ i j, ‖g.1 i j‖ ≤ 1 := by
      rw [hgv]; exact integ_mul hw (integ_add integ_one (integ_smul hϖle hx))
    have hgd : ‖g.1.det‖ = 1 := by
      rw [hgv, Matrix.det_mul, norm_mul, hwd, GlobalTheory.T.ultrametric_norm_det_one_add_smul E n x.1 ϖ hϖ1 hx, one_mul]
    obtain ⟨hgu, hgiI⟩ := isUnit_and_integ_inv_of_norm_det_eq_one E n g.1 hgI hgd
    refine ⟨⟨g.1⁻¹, mem _ (inv_comm (memN g))⟩, Subtype.ext ?_, hgiI⟩
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hgu)
  have wpow : ∀ w : S, (∀ i j, ‖w.1 i j‖ ≤ 1) → ‖w.1.det‖ = 1 → ∀ k : ℕ,
      (∀ i j, ‖(w ^ k).1 i j‖ ≤ 1) ∧ ‖(w ^ k).1.det‖ = 1 := fun w hw hd k =>
    ⟨integ_pow hw k, by show ‖(w.1 ^ k).det‖ = 1; rw [Matrix.det_pow, norm_pow, hd, one_pow]⟩
  have w1 : (∀ i j, ‖(1 : S).1 i j‖ ≤ 1) ∧ ‖(1 : S).1.det‖ = 1 :=
    ⟨integ_one, by show ‖(1 : Matrix (Fin n) (Fin n) E).det‖ = 1; simp⟩
  obtain ⟨k11, hk11, Ik11⟩ := mk (P + U ^ 2) (U ^ 2) (Ui ^ 2)
    (by linear_combination -P * (U * Ui + 1) * hUi) (wpow U IU hUd 2).1 (wpow U IU hUd 2).2
    (I_pow _ _ IUi)
  obtain ⟨k12, hk12, Ik12⟩ := mk (1 + P * A2 ^ 2) 1 (A2 ^ 2) (by ring) w1.1 w1.2 (I_pow _ _ IA2)
  obtain ⟨k13, hk13, Ik13⟩ := mk (1 + P ^ 3 * A3 ^ 2) 1 (P ^ 2 * A3 ^ 2) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling))
  obtain ⟨k21, hk21, Ik21⟩ := mk (P + U ^ 3) (U ^ 3) (Ui ^ 3)
    (by linear_combination -P * ((U * Ui) ^ 2 + U * Ui + 1) * hUi) (wpow U IU hUd 3).1
    (wpow U IU hUd 3).2 (I_pow _ _ IUi)
  obtain ⟨k22, hk22, Ik22⟩ := mk (1 + P ^ 2 * A2 ^ 3) 1 (P * A2 ^ 3) (by ring) w1.1 w1.2
    (I_mul _ _ IP (I_pow _ _ IA2))
  obtain ⟨k23, hk23, Ik23⟩ := mk (1 + P ^ 4 * A3 ^ 3) 1 (P ^ 3 * A3 ^ 3) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling))
  obtain ⟨k31, hk31, Ik31⟩ := mk (P * U ^ 2 + B ^ 2) (B ^ 2) (Bi ^ 2 * U ^ 2)
    (by linear_combination -P * U ^ 2 * (B * Bi + 1) * hBi) (wpow B IB hBd 2).1
    (wpow B IB hBd 2).2 (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IU))
  obtain ⟨k32, hk32, Ik32⟩ := mk (B ^ 2 + P ^ 3 * A2 ^ 2) (B ^ 2) (P ^ 2 * (Bi ^ 2 * A2 ^ 2))
    (by linear_combination -P ^ 3 * A2 ^ 2 * (B * Bi + 1) * hBi) (wpow B IB hBd 2).1
    (wpow B IB hBd 2).2 (I_mul _ _ (I_pow _ _ IP) (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IA2)))
  obtain ⟨k33, hk33, Ik33⟩ := mk (1 + P * B ^ 2 * A3 ^ 2) 1 (B ^ 2 * A3 ^ 2) (by ring) w1.1 w1.2
    (I_mul _ _ (I_pow _ _ IB) (I_pow _ _ NearKilling))
  obtain ⟨k41, hk41, Ik41⟩ := mk (P * U ^ 3 + B ^ 3) (B ^ 3) (Bi ^ 3 * U ^ 3)
    (by linear_combination -P * U ^ 3 * ((B * Bi) ^ 2 + B * Bi + 1) * hBi) (wpow B IB hBd 3).1
    (wpow B IB hBd 3).2 (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IU))
  obtain ⟨k42, hk42, Ik42⟩ := mk (B ^ 3 + P ^ 4 * A2 ^ 3) (B ^ 3) (P ^ 3 * (Bi ^ 3 * A2 ^ 3))
    (by linear_combination -P ^ 4 * A2 ^ 3 * ((B * Bi) ^ 2 + B * Bi + 1) * hBi)
    (wpow B IB hBd 3).1 (wpow B IB hBd 3).2
    (I_mul _ _ (I_pow _ _ IP) (I_mul _ _ (I_pow _ _ IBi) (I_pow _ _ IA2)))
  obtain ⟨k43, hk43, Ik43⟩ := mk (1 + P ^ 2 * B ^ 3 * A3 ^ 3) 1 (P * (B ^ 3 * A3 ^ 3)) (by ring)
    w1.1 w1.2 (I_mul _ _ IP (I_mul _ _ (I_pow _ _ IB) (I_pow _ _ NearKilling)))
  obtain ⟨hX1, hX2, hX3, hX4, hQ, hYY⟩ := core P Pi C Ci U A2 A3 B E1 E2 E3
    k11 k12 k13 k21 k22 k23 k31 k32 k33 k41 k42 k43 hp hci h11S h22S h33S h12S h13S h23S hsS
    hc1S hc2S hc3S hk11 hk12 hk13 hk21 hk22 hk23 hk31 hk32 hk33 hk41 hk42 hk43
  set Y : S := ((P * U ^ 3 + B ^ 3) * (P + U ^ 2) * k21 * k31) * E1
        + ((B ^ 3 + P ^ 4 * A2 ^ 3) * (1 + P * A2 ^ 2) * k22 * k32) * E2
        + ((1 + P ^ 2 * B ^ 3 * A3 ^ 3) * (1 + P ^ 3 * A3 ^ 2) * k23 * k33) * E3 with hY
  set Y' : S := ((P + U ^ 3) * (P * U ^ 2 + B ^ 2) * k41 * k11) * E1
        + ((1 + P ^ 2 * A2 ^ 3) * (B ^ 2 + P ^ 3 * A2 ^ 2) * k42 * k12) * E2
        + ((1 + P ^ 4 * A3 ^ 3) * (1 + P * B ^ 2 * A3 ^ 2) * k43 * k13) * E3 with hY'
  have IY : ∀ i j, ‖Y.1 i j‖ ≤ 1 := by
    rw [hY]
    exact I_add _ _ (I_add _ _
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ (I_mul _ _ IP (I_pow _ _ IU)) (I_pow _ _ IB))
        (I_add _ _ IP (I_pow _ _ IU))) Ik21) Ik31) IE1)
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ (I_pow _ _ IB) (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))
        (I_add _ _ I_one (I_mul _ _ IP (I_pow _ _ IA2)))) Ik22) Ik32) IE2))
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _
        (I_add _ _ I_one (I_mul _ _ (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IB)) (I_pow _ _ NearKilling)))
        (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling)))) Ik23) Ik33) IE3)
  have IY' : ∀ i j, ‖Y'.1 i j‖ ≤ 1 := by
    rw [hY']
    exact I_add _ _ (I_add _ _
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ IP (I_pow _ _ IU))
        (I_add _ _ (I_mul _ _ IP (I_pow _ _ IU)) (I_pow _ _ IB))) Ik41) Ik11) IE1)
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))
        (I_add _ _ (I_pow _ _ IB) (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ IA2)))) Ik42) Ik12) IE2))
      (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_mul _ _ (I_add _ _ I_one (I_mul _ _ (I_pow _ _ IP) (I_pow _ _ NearKilling)))
        (I_add _ _ I_one (I_mul _ _ (I_mul _ _ IP (I_pow _ _ IB)) (I_pow _ _ NearKilling)))) Ik43) Ik13) IE3)
  have hX1v : (P + C ^ 2).1 = ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2 := by
    show P.1 + C.1 ^ 2 = _; rw [hPv, hCv]
  have hX2v : (P + C ^ 3).1 = ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3 := by
    show P.1 + C.1 ^ 3 = _; rw [hPv, hCv]
  have hX3v : (P * C ^ 2 + B ^ 2).1 = ϖ • c ^ 2 + b ^ 2 := by
    show P.1 * C.1 ^ 2 + B.1 ^ 2 = _; rw [hPv, hCv, hBv, Matrix.smul_mul, Matrix.one_mul]
  have hX4v : (P * C ^ 3 + B ^ 3).1 = ϖ • c ^ 3 + b ^ 3 := by
    show P.1 * C.1 ^ 3 + B.1 ^ 3 = _; rw [hPv, hCv, hBv, Matrix.smul_mul, Matrix.one_mul]
  have u1 := isU _ _ hX1
  have u2 := isU _ _ hX2
  have u3 := isU _ _ hX3
  have u4 := isU _ _ hX4
  rw [hX1v] at u1; rw [hX2v] at u2; rw [hX3v] at u3; rw [hX4v] at u4
  have hdet23 : IsUnit ((P + C ^ 3).1 * (P * C ^ 2 + B ^ 2).1).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((isU _ _ hX2).mul (isU _ _ hX3))
  have hQv : (P * C ^ 3 + B ^ 3).1 * (P + C ^ 2).1 = Y.1 * ((P + C ^ 3).1 * (P * C ^ 2 + B ^ 2).1) :=
    congrArg Subtype.val hQ
  have Qm : (ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) *
      ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹ = Y.1 := by
    rw [← hX1v, ← hX2v, ← hX3v, ← hX4v, hQv, Matrix.mul_nonsing_inv_cancel_right _ _ hdet23]
  have hYYv : Y.1 * Y'.1 = 1 := congrArg Subtype.val hYY
  have hdY : ‖Y.1.det‖ = 1 := by
    have h1 := GlobalTheory.norm_det_le_one_of_entries_le_one E n Y.1 IY
    have h2 := GlobalTheory.norm_det_le_one_of_entries_le_one E n Y'.1 IY'
    have h3 : ‖Y.1.det‖ * ‖Y'.1.det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, hYYv, Matrix.det_one, norm_one]
    exact eq_one_of_mul_eq_one (norm_nonneg _) (norm_nonneg _) h1 h2 h3
  exact ⟨u1, u2, u3, u4, by rw [Qm]; exact IY, by rw [Qm]; exact hdY⟩

end GlobalTheory.UnitDiscAlg.QuotAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientIntegralUnitStatement
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integral_unit_alt : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N c b e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) → (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) → ‖u.det‖ = 1 → e₁ * e₁ = e₁ → e₂ * e₂ = e₂ → e₃ * e₃ = e₃ → e₁ * e₂ = 0 → e₁ * e₃ = 0 → e₂ * e₃ = 0 → e₁ + e₂ + e₃ = 1 → c * e₁ = u * e₁ → c * e₂ = ϖ • (a₂ * e₂) → c⁻¹ * e₃ = ϖ • (a₃ * e₃) → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | exact GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit | (intros; apply GlobalTheory.UnitDiscAlg.QuotAlg.quotient_integral_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecomposition
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.ValDecomp

section Abstract
variable {R : Type*} [CommRing R]

end Abstract
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp
section Abstract2
variable {R : Type*} [CommRing R]

end Abstract2
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp
section Mat
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

end Mat
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem exists_pow_smul_entries_norm_le_one {ϖ : E} (h1 : ‖ϖ‖ < 1)
    (c : Matrix (Fin n) (Fin n) E) : ∃ k : ℕ, ∀ i j, ‖(ϖ ^ k • c) i j‖ ≤ 1 := by
  set B : ℝ := 1 + ∑ i, ∑ j, ‖c i j‖
  have hB : 0 < B := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hB) h1
  refine ⟨k, fun i j => ?_⟩
  have hij : ‖c i j‖ ≤ B := by
    have h := (Finset.single_le_sum (f := fun j => ‖c i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖c i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    linarith
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  calc ‖ϖ‖ ^ k * ‖c i j‖ ≤ B⁻¹ * B := mul_le_mul hk.le hij (norm_nonneg _) (inv_pos.2 hB).le
    _ = 1 := inv_mul_cancel₀ hB.ne'

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem inv_mul_comm_of_mul_comm' {x N : Matrix (Fin n) (Fin n) E} (hx : IsUnit x.det)
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by
  calc x⁻¹ * N = x⁻¹ * (N * x) * x⁻¹ := by
        rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv x hx, mul_one]
    _ = x⁻¹ * (x * N) * x⁻¹ := by rw [h]
    _ = N * x⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul x hx, one_mul]

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem norm_det_le_one_of_entries_norm_le_one' {x : Matrix (Fin n) (Fin n) E}
    (hx : ∀ i j, ‖x i j‖ ≤ 1) : ‖x.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp only [h, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hx _ _

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem inv_entries_norm_le_one_of_norm_det_one {x : Matrix (Fin n) (Fin n) E}
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (hd : ‖x.det‖ = 1) : ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv', norm_inv,
    hd, inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one_of_entries_norm_le_one'
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp
  · exact hx _ _

theorem _root_.GlobalTheory.ValDecomp.valuation_decomp : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → (∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧ e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a) → ∀ c : Matrix (Fin n) (Fin n) E, IsUnit c → c * N = N * c → ∃ e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E, (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ ‖u.det‖ = 1 ∧ e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧ e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ e₁ + e₂ + e₃ = 1 ∧ c * e₁ = u * e₁ ∧ c * e₂ = ϖ • (a₂ * e₂) ∧ c⁻¹ * e₃ = ϖ • (a₃ * e₃) := by
  intro E _ _ n N ϖ h0 h1 hcomm hdec c hc hcN
  have hϖ : ϖ ≠ 0 := norm_pos_iff.1 h0
  have hpow : ∀ k : ℕ, ‖ϖ ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le
  have hone : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 :=
    fun i j => _root_.GlobalTheory.UnitDiscAlg.integ_one i j
  let S := Subalgebra.centralizer E ({N} : Set (Matrix (Fin n) (Fin n) E))
  have memS : ∀ {x : Matrix (Fin n) (Fin n) E}, x * N = N * x → x ∈ S := fun hx => by
    rw [Subalgebra.mem_centralizer_iff]; rintro g rfl; exact hx.symm
  have ofS : ∀ {x : Matrix (Fin n) (Fin n) E}, x ∈ S → x * N = N * x := fun hx =>
    ((Subalgebra.mem_centralizer_iff E).1 hx N rfl).symm
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun x y => Subtype.ext (hcomm x y (ofS x.2) (ofS y.2)) }
  have toM : ∀ {X Y : S}, X = Y → (X : Matrix (Fin n) (Fin n) E) = Y := fun h => congrArg _ h
  have hscal : ∀ r : E, (r • (1 : Matrix (Fin n) (Fin n) E)) * N = N * (r • 1) := fun r => by
    rw [smul_one_mul, Matrix.mul_smul, mul_one]
  let Pp : S := ⟨ϖ • 1, memS (hscal ϖ)⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_entries_norm_le_one h1 c
  induction k generalizing c with
  | zero =>
    have hc0 : ∀ i j, ‖c i j‖ ≤ 1 := by simpa using hk
    obtain ⟨e, a, heN, haN, hea, hee, hdet, hca⟩ := hdec c hcN hc0
    have he : ∀ i j, ‖e i j‖ ≤ 1 := fun i j => (hea i j).1
    let C : S := ⟨c, memS hcN⟩
    let Ee : S := ⟨e, memS heN⟩
    let A : S := ⟨a, memS haN⟩
    have re : Ee * Ee = Ee := Subtype.ext hee
    have rca : C * (1 - Ee) = Pp * A :=
      Subtype.ext (show c * (1 - e) = (ϖ • 1) * a by rw [smul_one_mul]; exact hca)
    refine ⟨e, 1 - e, 0, c * e + (1 - e), a, 0, ⟨heN, ofS (1 - Ee).2, by simp,
      ofS (C * Ee + (1 - Ee)).2, haN, by simp⟩, fun i j => ⟨he i j,
      _root_.GlobalTheory.UnitDiscAlg.integ_sub hone he i j, by simp,
      _root_.GlobalTheory.UnitDiscAlg.integ_add (_root_.GlobalTheory.UnitDiscAlg.integ_mul hc0 he)
        (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j, (hea i j).2, by simp⟩, hdet, hee,
      toM (by linear_combination re : (1 - Ee) * (1 - Ee) = 1 - Ee), by simp,
      toM (by linear_combination (-1 : S) * re : Ee * (1 - Ee) = 0), by simp, by simp,
      by abel, toM (by linear_combination (1 - C) * re : C * Ee = (C * Ee + (1 - Ee)) * Ee),
      ?_, by simp⟩
    have h := toM (by linear_combination (1 - Ee) * rca - C * re :
      C * (1 - Ee) = Pp * (A * (1 - Ee)))
    rw [← smul_one_mul]; exact h
  | succ k ih =>
    have hyN : (ϖ ^ (k + 1) • c) * N = N * (ϖ ^ (k + 1) • c) :=
      (show Commute c N from hcN).smul_left _
    obtain ⟨e, a, heN, haN, hea, hee, hdet, hya⟩ := hdec _ hyN hk
    have he : ∀ i j, ‖e i j‖ ≤ 1 := fun i j => (hea i j).1
    have ha : ∀ i j, ‖a i j‖ ≤ 1 := fun i j => (hea i j).2
    have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    have hciN : c⁻¹ * N = N * c⁻¹ := inv_mul_comm_of_mul_comm' hcd hcN
    let C : S := ⟨c, memS hcN⟩
    let Ci : S := ⟨c⁻¹, memS hciN⟩
    let Ee : S := ⟨e, memS heN⟩
    let Pk : S := ⟨ϖ ^ k • 1, memS (hscal _)⟩
    have re : Ee * Ee = Ee := Subtype.ext hee
    have r1 : C * Ci = 1 := Subtype.ext (Matrix.mul_nonsing_inv c hcd)
    have hsplit : ϖ ^ (k + 1) • c = (ϖ • 1) * (ϖ ^ k • 1) * c := by
      rw [smul_one_mul, smul_mul_assoc, smul_one_mul, smul_smul, ← pow_succ']
    have hzN : (ϖ ^ (k + 1) • c * e + (1 - e)) * N = N * (ϖ ^ (k + 1) • c * e + (1 - e)) := by
      rw [hsplit]; exact ofS (Pp * Pk * C * Ee + (1 - Ee)).2
    have hzint : ∀ i j, ‖(ϖ ^ (k + 1) • c * e + (1 - e)) i j‖ ≤ 1 :=
      _root_.GlobalTheory.UnitDiscAlg.integ_add (_root_.GlobalTheory.UnitDiscAlg.integ_mul hk he)
        (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he)
    have hzd : IsUnit (ϖ ^ (k + 1) • c * e + (1 - e)).det :=
      isUnit_iff_ne_zero.2 fun h => by rw [h, norm_zero] at hdet; exact zero_ne_one hdet
    have hw := inv_entries_norm_le_one_of_norm_det_one hzint hdet
    have hwN := inv_mul_comm_of_mul_comm' hzd hzN
    let W : S := ⟨_, memS hwN⟩
    have rwz : (Pp * Pk * C * Ee + (1 - Ee)) * W = 1 := Subtype.ext (show
      ((ϖ • 1) * (ϖ ^ k • 1) * c * e + (1 - e)) * (ϖ ^ (k + 1) • c * e + (1 - e))⁻¹ = 1 by
        rw [← hsplit]; exact Matrix.mul_nonsing_inv _ hzd)
    have hA : Ci * Ee = Pp * Pk * (Ee * W) := by
      linear_combination (-(Ci * Ee)) * rwz + (Pp * Pk * W - Ci * W) * re
        + (Pp * Pk * Ee ^ 2 * W) * r1
    have ha' : ϖ ^ k • (c * (1 - e)) = a := smul_right_injective _ hϖ
      (show ϖ • (ϖ ^ k • (c * (1 - e))) = ϖ • a by
        rw [← hya, smul_smul, ← pow_succ', smul_mul_assoc])
    have hc'int : ∀ i j, ‖(ϖ ^ k • (c * (1 - e) + e)) i j‖ ≤ 1 := by
      rw [smul_add, ha']
      exact _root_.GlobalTheory.UnitDiscAlg.integ_add ha (_root_.GlobalTheory.UnitDiscAlg.integ_smul (hpow k) he)
    have rcd : (C * (1 - Ee) + Ee) * (Ci * (1 - Ee) + Ee) = 1 := by
      linear_combination (1 - Ee) * r1 + (C * Ci - C - Ci + 1) * re
    have hmat : (c * (1 - e) + e) * (c⁻¹ * (1 - e) + e) = 1 := toM rcd
    have hunit : IsUnit (c * (1 - e) + e) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hmat)
    have hinv : (c * (1 - e) + e)⁻¹ = c⁻¹ * (1 - e) + e := Matrix.inv_eq_right_inv hmat
    obtain ⟨f₁, f₂, f₃, u, b₂, b₃, ⟨h1N, h2N, h3N, huN, hb2N, hb3N⟩, hint, hu, h11, h22, h33,
      h12, h13, h23, hsum, hc1, hc2, hc3⟩ := ih _ hunit (ofS (C * (1 - Ee) + Ee).2) hc'int
    rw [hinv] at hc3
    have hF1 : ∀ i j, ‖f₁ i j‖ ≤ 1 := fun i j => (hint i j).1
    have hF2 : ∀ i j, ‖f₂ i j‖ ≤ 1 := fun i j => (hint i j).2.1
    have hF3 : ∀ i j, ‖f₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.1
    have hB3 : ∀ i j, ‖b₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2.2
    let F1 : S := ⟨f₁, memS h1N⟩
    let F2 : S := ⟨f₂, memS h2N⟩
    let F3 : S := ⟨f₃, memS h3N⟩
    let U : S := ⟨u, memS huN⟩
    let B2 : S := ⟨b₂, memS hb2N⟩
    let B3 : S := ⟨b₃, memS hb3N⟩
    have s11 : F1 * F1 = F1 := Subtype.ext h11
    have s22 : F2 * F2 = F2 := Subtype.ext h22
    have s33 : F3 * F3 = F3 := Subtype.ext h33
    have s12 : F1 * F2 = 0 := Subtype.ext h12
    have s13 : F1 * F3 = 0 := Subtype.ext h13
    have s23 : F2 * F3 = 0 := Subtype.ext h23
    have ssum : F1 + F2 + F3 = 1 := Subtype.ext hsum
    have sc1 : (C * (1 - Ee) + Ee) * F1 = U * F1 := Subtype.ext hc1
    have sc2 : (C * (1 - Ee) + Ee) * F2 = Pp * (B2 * F2) := Subtype.ext
      (show (c * (1 - e) + e) * f₂ = (ϖ • 1) * (b₂ * f₂) by rw [smul_one_mul]; exact hc2)
    have sc3 : (Ci * (1 - Ee) + Ee) * F3 = Pp * (B3 * F3) := Subtype.ext
      (show (c⁻¹ * (1 - e) + e) * f₃ = (ϖ • 1) * (b₃ * f₃) by rw [smul_one_mul]; exact hc3)
    refine ⟨f₁ * (1 - e), f₂ * (1 - e), f₃ * (1 - e) + e, u, b₂,
      b₃ * (1 - e) + (ϖ ^ k • 1) * (e * (ϖ ^ (k + 1) • c * e + (1 - e))⁻¹),
      ⟨ofS (F1 * (1 - Ee)).2, ofS (F2 * (1 - Ee)).2, ofS (F3 * (1 - Ee) + Ee).2, huN, hb2N,
        ofS (B3 * (1 - Ee) + Pk * (Ee * W)).2⟩,
      fun i j => ⟨_root_.GlobalTheory.UnitDiscAlg.integ_mul hF1 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j,
        _root_.GlobalTheory.UnitDiscAlg.integ_mul hF2 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j,
        _root_.GlobalTheory.UnitDiscAlg.integ_add
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul hF3 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he)) he i j,
        (hint i j).2.2.2.1, (hint i j).2.2.2.2.1,
        _root_.GlobalTheory.UnitDiscAlg.integ_add
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul hB3 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he))
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_smul (hpow k) hone)
            (_root_.GlobalTheory.UnitDiscAlg.integ_mul he hw)) i j⟩, hu,
      toM (by linear_combination (1 - Ee) ^ 2 * s11 + F1 * re :
        F1 * (1 - Ee) * (F1 * (1 - Ee)) = F1 * (1 - Ee)),
      toM (by linear_combination (1 - Ee) ^ 2 * s22 + F2 * re :
        F2 * (1 - Ee) * (F2 * (1 - Ee)) = F2 * (1 - Ee)),
      toM (by linear_combination (1 - Ee) ^ 2 * s33 + (1 - F3) * re :
        (F3 * (1 - Ee) + Ee) * (F3 * (1 - Ee) + Ee) = F3 * (1 - Ee) + Ee),
      toM (by linear_combination (1 - Ee) ^ 2 * s12 : F1 * (1 - Ee) * (F2 * (1 - Ee)) = 0),
      toM (by linear_combination (1 - Ee) ^ 2 * s13 - F1 * re :
        F1 * (1 - Ee) * (F3 * (1 - Ee) + Ee) = 0),
      toM (by linear_combination (1 - Ee) ^ 2 * s23 - F2 * re :
        F2 * (1 - Ee) * (F3 * (1 - Ee) + Ee) = 0),
      toM (by linear_combination (1 - Ee) * ssum :
        F1 * (1 - Ee) + F2 * (1 - Ee) + (F3 * (1 - Ee) + Ee) = 1),
      toM (by linear_combination (1 - Ee) * sc1 - (C * F1 - F1) * re :
        C * (F1 * (1 - Ee)) = U * (F1 * (1 - Ee))), ?_, ?_⟩
    · have h := toM (by linear_combination (1 - Ee) * sc2 - (C * F2 - F2) * re :
        C * (F2 * (1 - Ee)) = Pp * (B2 * (F2 * (1 - Ee))))
      rw [← smul_one_mul]; exact h
    · have h := toM (by
        linear_combination (1 - Ee) * sc3 + hA
          + (F3 - Ci * F3 - Pp * B3 * F3 + Pp * B3 + Pp * Pk * W * F3 - Pp * Pk * W) * re :
        Ci * (F3 * (1 - Ee) + Ee) = Pp * ((B3 * (1 - Ee) + Pk * (Ee * W)) * (F3 * (1 - Ee) + Ee)))
      rw [← smul_one_mul]; exact h

end GlobalTheory.ValDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecompositionStatement
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_commutant_valuation_decomposition : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → (∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧ e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a) → ∀ c : Matrix (Fin n) (Fin n) E, IsUnit c → c * N = N * c → ∃ e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E, (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ ‖u.det‖ = 1 ∧ e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧ e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ e₁ + e₂ + e₃ = 1 ∧ c * e₁ = u * e₁ ∧ c * e₂ = ϖ • (a₂ * e₂) ∧ c⁻¹ * e₃ = ϖ • (a₃ * e₃) := by
  first | exact @GlobalTheory.ValDecomp.valuation_decomp | exact GlobalTheory.ValDecomp.valuation_decomp | (intros; apply GlobalTheory.ValDecomp.valuation_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewton
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewton
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.IdemLift

open Filter Topology

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

noncomputable def step (y : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  y * y + y * y + y * y - (y * y * y + y * y * y)

noncomputable def seq (x : Matrix (Fin n) (Fin n) E) : ℕ → Matrix (Fin n) (Fin n) E
  | 0 => x
  | k + 1 => step (seq x k)

theorem step_sq (y : Matrix (Fin n) (Fin n) E) :
    step y * step y - step y = (y * y - y) * (y * y - y) *
      ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)) := by
  unfold step; noncomm_ring

theorem step_sub (y : Matrix (Fin n) (Fin n) E) :
    step y - y = (y * y - y) * (1 - (y + y)) := by
  unfold step; noncomm_ring

theorem step_integ {y : Matrix (Fin n) (Fin n) E} (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖step y i j‖ ≤ 1 := by
  have h2 := integ_mul hy hy
  have h3 := integ_mul h2 hy
  exact integ_sub (integ_add (integ_add h2 h2) h2) (integ_add h3 h3)

theorem step_comm {y N : Matrix (Fin n) (Fin n) E} (h : y * N = N * y) :
    step y * N = N * step y := by
  have hc : Commute y N := h
  have h2 := hc.mul_left hc
  have h3 := h2.mul_left hc
  exact ((h2.add_left h2).add_left h2).sub_left (h3.add_left h3)

theorem seq_inv (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    (∀ i j, ‖seq x k i j‖ ≤ 1) ∧ seq x k * N = N * seq x k ∧
      ∃ b : Matrix (Fin n) (Fin n) E, (∀ i j, ‖b i j‖ ≤ 1) ∧
        seq x k * seq x k - seq x k = ϖ ^ (2 ^ k) • b := by
  induction k with
  | zero => exact ⟨hx, hxN, a, ha, by simpa [seq] using hxa⟩
  | succ k ih =>
    obtain ⟨hi, hc, b, hb, hd⟩ := ih
    refine ⟨step_integ hi, step_comm hc, ?_⟩
    set y := seq x k
    have hdi : ∀ i j, ‖(y * y - y) i j‖ ≤ 1 := integ_sub (integ_mul hi hi) hi
    refine ⟨b * b * ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)),
      integ_mul (integ_mul hb hb) (integ_sub (integ_add (integ_add (integ_add hdi hdi) hdi) hdi)
        (integ_add (integ_add integ_one integ_one) integ_one)), ?_⟩
    show step y * step y - step y = _
    rw [step_sq, hd, smul_mul_smul_comm, smul_mul_assoc, ← pow_add, pow_succ, mul_two]

theorem seq_succ_sub (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x (k + 1) - seq x k) i j‖ ≤ ‖ϖ‖ ^ (2 ^ k) := by
  obtain ⟨hi, -, b, hb, hd⟩ := seq_inv x N a ϖ hxN hx ha hxa k
  intro i j
  have hc : ∀ i j, ‖(b * (1 - (seq x k + seq x k))) i j‖ ≤ 1 :=
    integ_mul hb (integ_sub integ_one (integ_add hi hi))
  show ‖(step (seq x k) - seq x k) i j‖ ≤ _
  rw [step_sub, hd, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (hc i j)

theorem seq_sub_le (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x k - x) i j‖ ≤ ‖ϖ‖ := by
  induction k with
  | zero => intro i j; simp [seq]
  | succ k ih =>
    intro i j
    have h1 := seq_succ_sub x N a ϖ hxN hx ha hxa k i j
    have h2 : ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ := by
      calc ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.one_le_two_pow)
        _ = ‖ϖ‖ := pow_one _
    have : (seq x (k + 1) - x) i j = (seq x (k + 1) - seq x k) i j + (seq x k - x) i j := by
      simp [Matrix.sub_apply]
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans h2) (ih i j))

theorem idem_lift (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E]
    (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E) :
    ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a →
    ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧
      (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  intro hϖ hxN hx ha hxa
  have hinv := seq_inv x N a ϖ hxN hx ha hxa
  have hpow : ∀ k : ℕ, ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ k := fun k =>
    pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.lt_two_pow_self).le
  have hcs : ∀ i j, CauchySeq (fun k => seq x k i j) := by
    intro i j
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 hϖ (fun k => ?_)
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (seq_succ_sub x N a ϖ hxN hx ha hxa k i j).trans (hpow k)
  choose e he using fun i j => cauchySeq_tendsto_of_complete (hcs i j)
  have hT : Tendsto (seq x) atTop (𝓝 (Matrix.of e)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => he i j

  have heN : Matrix.of e * N = N * Matrix.of e := by
    have hcl : IsClosed {M : Matrix (Fin n) (Fin n) E | M * N = N * M} :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    exact hcl.mem_of_tendsto hT (Eventually.of_forall fun k => (hinv k).2.1)

  have heI : ∀ i j, ‖Matrix.of e i j‖ ≤ 1 := fun i j =>
    le_of_tendsto' (he i j).norm fun k => (hinv k).1 i j

  have hee : Matrix.of e * Matrix.of e = Matrix.of e := by
    have hD : Tendsto (fun k => seq x k * seq x k - seq x k) atTop
        (𝓝 (Matrix.of e * Matrix.of e - Matrix.of e)) := (hT.mul hT).sub hT
    rw [← sub_eq_zero]
    ext i j
    have h1 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop
        (𝓝 ((Matrix.of e * Matrix.of e - Matrix.of e) i j)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hD i) j
    have h0 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg ϖ) hϖ)
      obtain ⟨-, -, b, hb, hd⟩ := hinv k
      rw [hd, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (by positivity) (hb i j)).trans (hpow k)
    simpa using tendsto_nhds_unique h1 h0

  have hex : ∀ i j, ‖(Matrix.of e - x) i j‖ ≤ ‖ϖ‖ := by
    intro i j
    have h1 : Tendsto (fun k => (seq x k - x) i j) atTop (𝓝 ((Matrix.of e - x) i j)) := by
      simpa [Matrix.sub_apply] using (he i j).sub_const (x i j)
    exact le_of_tendsto' h1.norm fun k => seq_sub_le x N a ϖ hϖ hxN hx ha hxa k i j
  by_cases h0 : ϖ = 0
  · have hz : Matrix.of e - x = 0 := by
      ext i j
      have := hex i j
      rw [h0, norm_zero] at this
      simpa using norm_le_zero_iff.1 this
    refine ⟨Matrix.of e, 0, heN, by simp, hee, heI, integ_zero, ?_⟩
    rw [hz, smul_zero]
  · refine ⟨Matrix.of e, ϖ⁻¹ • (Matrix.of e - x), heN, ?_, hee, heI, ?_, ?_⟩
    · rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, heN, hxN]
    · intro i j
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      exact inv_mul_le_one_of_le₀ (hex i j) (norm_nonneg _)
    · rw [smul_inv_smul₀ h0]

end GlobalTheory.IdemLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewtonStatement
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_idempotent_lift_newton : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E] (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a → ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧ (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  first | exact @GlobalTheory.IdemLift.idem_lift | exact GlobalTheory.IdemLift.idem_lift | (intros; apply GlobalTheory.IdemLift.idem_lift <;> assumption)
end
end

open Matrix

namespace GlobalTheory.UnitDiscAlg

theorem unit_split {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E]
    [LocallyCompactSpace E] {n : ℕ} {N : Matrix (Fin n) (Fin n) E} {ϖ : E}
    (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hB : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1) (hϖ : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖)
    (hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x)
    (y : Matrix (Fin n) (Fin n) E) (hyN : y * N = N * y) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧
      e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a := by
  obtain ⟨x, z, a₁, a₂, a₃, ⟨hxN, hzN, h1N, h2N, h3N⟩, hint, hx, hyx, hyz⟩ :=
    GlobalTheory.T.commuting_integral_matrix_decompose E n N ϖ hN hB h0 h1 hϖ y hyN hy
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  obtain ⟨e, a', heN, ha'N, he, heI, ha'I, hea⟩ :=
    GlobalTheory.T.exists_integral_idempotent_lift_newton E n N x a₁ ϖ h1 hxN (fun i j => (hint i j).1) (fun i j => (hint i j).2.2.1) hx
  have hzI : ∀ i j, ‖z i j‖ ≤ 1 := fun i j => (hint i j).2.1
  have ha₂I : ∀ i j, ‖a₂ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.1
  have ha₃I : ∀ i j, ‖a₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2
  refine ⟨e, a₂ - y * a', heN, ?_, fun i j => ⟨heI i j, integ_sub ha₂I (integ_mul hy ha'I) i j⟩,
    he, ?_, ?_⟩
  · rw [sub_mul, mul_sub, h2N, Matrix.mul_assoc, ha'N, ← Matrix.mul_assoc, hyN, Matrix.mul_assoc]
  ·
    have hye : y * e = e * y := hcomm y e hyN heN
    have hze : z * e = e * z := hcomm z e hzN heN
    have hyz' : y * z = z * y := hcomm y z hyN hzN
    have hprod : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + ϖ • (a₃ + y * z * a' - a') := by
      have e1 : e = x + ϖ • a' := by rw [← hea]; abel
      have e2 : y * z * x = x + ϖ • a₃ := by rw [← hyz]; abel
      have key : (y * e + (1 - e)) * (z * e + (1 - e)) = 1 + y * z * e - e := by
        have : (y * e + (1 - e)) * (z * e + (1 - e)) =
            y * (e * z) * e + y * e * (1 - e) + (1 - e) * z * e + (1 - e) * (1 - e) := by
          noncomm_ring
        rw [this, ← hze]
        have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have hee' : (1 - e) * z * e = 0 := by
          rw [Matrix.mul_assoc, hze, ← Matrix.mul_assoc, sub_mul, one_mul, he, sub_self,
            Matrix.zero_mul]
        have hee'' : (1 - e) * (1 - e) = 1 - e := by
          rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
        rw [Matrix.mul_assoc y e (1 - e), hee, Matrix.mul_zero, hee', hee'',
          ← Matrix.mul_assoc, Matrix.mul_assoc (y * z) e e, he]
        abel
      rw [key]
      conv_lhs => rw [e1]
      rw [Matrix.mul_add, e2, Matrix.mul_smul]
      simp only [smul_add, smul_sub]
      abel
    have hwI : ∀ i j, ‖(y * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hy heI) (integ_sub integ_one heI)
    have hw'I : ∀ i j, ‖(z * e + (1 - e)) i j‖ ≤ 1 :=
      integ_add (integ_mul hzI heI) (integ_sub integ_one heI)
    have hd := congrArg (fun m => ‖m.det‖) hprod
    simp only [Matrix.det_mul, norm_mul] at hd
    rw [GlobalTheory.T.ultrametric_norm_det_one_add_smul E n _ ϖ h1 (integ_sub (integ_add ha₃I (integ_mul (integ_mul hy hzI) ha'I)) ha'I)]
      at hd
    have ha := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hwI
    have hb := GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one E n _ hw'I
    nlinarith [norm_nonneg (y * e + (1 - e)).det, norm_nonneg (z * e + (1 - e)).det]
  · have : y * (1 - e) = y * (1 - x) - y * (e - x) := by noncomm_ring
    rw [this, hyx, hea, Matrix.mul_smul, ← smul_sub]

theorem units_quotient : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N c b : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ _ n N c b ϖ hN hB h0 h1 hϖ hc hcN hbN hb hbd
  have hB' : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1 := by
    obtain ⟨u, v, -, -, h⟩ := hB
    exact ⟨u, v, h⟩
  have hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x :=
    fun x y hx hy => comm_of_bezout hB' hx hy
  obtain ⟨e₁, e₂, e₃, u, a₂, a₃, hN6, hI6, hu, h11, h22, h33, h12, h13, h23, hs, hc1, hc2, hc3⟩ :=
    GlobalTheory.T.matrix_commutant_valuation_decomposition E n N ϖ h0 h1 hcomm (unit_split hN hB h0 h1 hϖ hcomm) c hc hcN
  exact GlobalTheory.T.quotient_integral_unit_alt E n N c b e₁ e₂ e₃ u a₂ a₃ ϖ h0 h1 hcomm hc hcN hbN hb hbd hN6 hI6 hu h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3

end GlobalTheory.UnitDiscAlg
