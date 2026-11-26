module

public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Density
public import GroundTheory.AutomorphicForms.RealGroupsIwasawa

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.ExpEqOfHasDerivAt
namespace GroundTheory.Automorphic.ArchWhittakerC

open Matrix NormedSpace Complex MeasureTheory
open scoped Matrix.Norms.L2Operator

abbrev GL2C : Subgroup (GL (Fin 2) ℂ) := ⊤

noncomputable def toGLC (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) : GL2C :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, Subgroup.mem_top _⟩

@[simp] theorem coe_toGLC (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0) :
    (((toGLC A hA : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := rfl

theorem GL2C_ext {g g' : GL2C}
    (h : ((g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = ((g' : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    g = g' := Subtype.ext (Units.ext h)

noncomputable def dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) : GL2C :=
  toGLC !![(d₁ : ℂ), 0; 0, (d₂ : ℂ)] (by
    simp [Matrix.det_fin_two_of, h₁.ne', h₂.ne'])

@[simp] theorem coe_dC (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (((dC d₁ d₂ h₁ h₂ : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(d₁ : ℂ), 0; 0, (d₂ : ℂ)] := rfl

abbrev U2 : Type := unitaryGroup (Fin 2) ℂ

theorem det_ne_zero_of_U2 (k : U2) : ((k : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := by
  intro h
  have h1 : (star (k : Matrix (Fin 2) (Fin 2) ℂ) * k).det = 1 := by
    rw [Matrix.UnitaryGroup.star_mul_self, Matrix.det_one]
  rw [Matrix.det_mul, h, mul_zero] at h1
  exact zero_ne_one h1

noncomputable def kC : U2 →* GL2C where
  toFun k := toGLC (k : Matrix (Fin 2) (Fin 2) ℂ) (det_ne_zero_of_U2 k)
  map_one' := by apply GL2C_ext; rfl
  map_mul' k k' := by apply GL2C_ext; rfl

@[simp] theorem coe_kC (k : U2) :
    (((kC k : GL2C) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

theorem coe_kC_inv (k : U2) :
    ((((kC k : GL2C) : GL (Fin 2) ℂ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      star (k : Matrix (Fin 2) (Fin 2) ℂ) :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 k.2)

theorem continuous_kC : Continuous kC := by
  have hval : Continuous fun k : U2 => ((kC k : GL (Fin 2) ℂ)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : (fun k : U2 => ((((kC k : GL2C) : GL (Fin 2) ℂ)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun k : U2 => star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext k; exact coe_kC_inv k
    rw [e]
    exact continuous_star.comp continuous_subtype_val
  exact continuous_induced_rng.2 hval

noncomputable def tC (a b : ℝ) : U2 :=
  ⟨!![Complex.exp (a * I), 0; 0, Complex.exp (b * I)], by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : ∀ r : ℝ, Complex.exp (r * I) * (starRingEnd ℂ) (Complex.exp (r * I)) = 1 := fun r => by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      simp
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose, h]⟩

@[simp] theorem coe_tC (a b : ℝ) : ((tC a b : U2) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![Complex.exp (a * I), 0; 0, Complex.exp (b * I)] := rfl

end GroundTheory.Automorphic.ArchWhittakerC
end

namespace GroundTheory.Automorphic.ArchWhittakerC

open Matrix MeasureTheory

noncomputable instance : MeasurableSpace U2 := borel U2

instance : BorelSpace U2 := ⟨rfl⟩

noncomputable def μK : Measure U2 := Measure.haarMeasure ⊤

instance : μK.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _

instance : IsProbabilityMeasure μK := ⟨by
  have := Measure.haarMeasure_self (G := U2) (K₀ := ⊤)
  simpa [μK] using this⟩

instance : μK.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  haveI : (Measure.map (· * g) μK).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μK g
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

instance : μK.IsInvInvariant := by
  refine ⟨?_⟩
  haveI : μK.inv.IsHaarMeasure :=
    { lt_top_of_isCompact := fun K hK => by
        rw [Measure.inv_apply]; exact hK.inv.measure_lt_top
      toIsOpenPosMeasure := ⟨fun U hU hne => by
        rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μK (by simpa using hne)⟩ }
  haveI : IsProbabilityMeasure μK.inv := by
    rw [Measure.inv]
    infer_instance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem integral_mul_left_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E)
    (g : U2) : ∫ k, f (g * k) ∂μK = ∫ k, f k ∂μK :=
  integral_mul_left_eq_self f g

theorem integral_mul_right_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E)
    (g : U2) : ∫ k, f (k * g) ∂μK = ∫ k, f k ∂μK :=
  integral_mul_right_eq_self f g

theorem integral_inv_K {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : U2 → E) :
    ∫ k, f k⁻¹ ∂μK = ∫ k, f k ∂μK :=
  integral_inv_eq_self f μK

end GroundTheory.Automorphic.ArchWhittakerC
