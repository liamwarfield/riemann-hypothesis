module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LocallyCompactAEf

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.CharEqOneOfPreimage
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MulEquivHaarCharEqOfChart
noncomputable section

namespace PI.IwaMeasEx.MG

open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal

theorem smul_cancel {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hKx).ne'
  have htop : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have hK' : (a : ℝ≥0∞) * ρ K = (b : ℝ≥0∞) * ρ K := by
    have e := congrArg (fun m : Measure Y => m K) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have hab : (a : ℝ≥0∞) = b := (ENNReal.mul_left_inj h0 htop).mp hK'
  exact_mod_cast hab

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

theorem mulEquivHaarChar_eq_of_chart (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (ν : Measure Y)
    [IsAddHaarMeasure ν] [Regular ν] (χ : G → Y) (hχm : Measurable χ) (hχ : μ.map χ = ν) (φ : G ≃ₜ* G)
    (L : Y ≃ₜ+ Y) (h : ∀ x, χ (φ x) = L (χ x)) : mulEquivHaarChar φ = addEquivAddHaarChar L := by
  have hφ : Measurable φ := (map_continuous φ).measurable
  have hL : Measurable L := (map_continuous L).measurable
  have hcomp : χ ∘ φ = L ∘ χ := funext h
  have h1 : mulEquivHaarChar φ • map L ν = ν := by
    have e := congrArg (Measure.map χ) (mulEquivHaarChar_smul_map μ φ)
    rw [Measure.map_smul, Measure.map_map hχm hφ, hcomp, ← Measure.map_map hL hχm, hχ] at e
      <;> try exact hχm.aemeasurable
    exact e
  have h2 : addEquivAddHaarChar L • map L ν = ν := addEquivAddHaarChar_smul_map ν L
  have h3 : addEquivAddHaarChar L • ν = mulEquivHaarChar φ • ν := by
    calc addEquivAddHaarChar L • ν = addEquivAddHaarChar L • (mulEquivHaarChar φ • map L ν) := by rw [h1]
      _ = mulEquivHaarChar φ • (addEquivAddHaarChar L • map L ν) := by
        rw [smul_smul, smul_smul, mul_comm]
      _ = mulEquivHaarChar φ • ν := by rw [h2]
  exact (smul_cancel ν h3).symm

theorem shear_map {A B : Type*} [MeasurableSpace A] [AddGroup B] [MeasurableSpace B] [MeasurableAdd₂ B]
    [MeasurableAdd B] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    (f : A → B) (hf : Measurable f) :
    (μ.prod ν).map (fun p : A × B => (p.1, p.2 + f p.1)) = μ.prod ν := by
  have hm : Measurable (fun p : A × B => (p.1, p.2 + f p.1)) :=
    measurable_fst.prodMk (measurable_snd.add (hf.comp measurable_fst))
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply hs, Measure.prod_apply (hm hs)]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : A × B => (p.1, p.2 + f p.1)) ⁻¹' s)
      = (fun b => b + f x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre, measure_preimage_add_right]

end PI.IwaMeasEx.MG

end
end

noncomputable section

namespace PI.IwaMeasEx.MH

open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal

section Gen

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem nnreal_eq_of_smul (μ : Measure A) [μ.IsAddHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  have h0 : μ K ≠ 0 := (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK := congrArg (fun ν : Measure A => ν K) h
  simp only [Measure.smul_apply, nnreal_smul_coe_apply] at hK
  exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 hK

theorem char_eq_of_map (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (φ : A ≃ₜ+ A) {c : ℝ≥0} (hc : c ≠ 0)
    (h : μ.map φ = c • μ) : addEquivAddHaarChar φ = c⁻¹ := by
  have h1 := addEquivAddHaarChar_smul_map μ φ
  rw [h, smul_smul] at h1
  exact eq_inv_of_mul_eq_one_left (nnreal_eq_of_smul μ (h1.trans (one_smul _ _).symm))

theorem map_char (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular] (φ : A ≃ₜ+ A) :
    μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
  conv_rhs => rw [← addEquivAddHaarChar_smul_map μ φ]
  rw [smul_smul, inv_mul_cancel₀ (addEquivAddHaarChar_pos φ).ne', one_smul]

variable {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
  [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem char_transport (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) :
    addEquivAddHaarChar ((e.symm.trans φ).trans e) = addEquivAddHaarChar φ := by
  have : ((addHaar : Measure A).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have : ((addHaar : Measure A).map e).Regular := Regular.map e.toHomeomorph
  refine (char_eq_of_map ((addHaar : Measure A).map e) _
    (inv_ne_zero (addEquivAddHaarChar_pos φ).ne') ?_).trans (inv_inv _)
  have hcomp : ((e.symm.trans φ).trans e : B → B) ∘ e = e ∘ φ := by
    funext x
    simp
  rw [Measure.map_map (map_continuous _).measurable (map_continuous e).measurable, hcomp,
    ← Measure.map_map (map_continuous e).measurable (map_continuous φ).measurable,
    map_char (addHaar : Measure A) φ, Measure.map_smul]
  exact e.continuous.measurable.aemeasurable

def prodE (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) : A × B ≃ₜ+ A × B where
  toFun p := (φ p.1, ψ p.2)
  invFun p := (φ.symm p.1, ψ.symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp
  continuous_toFun := (φ.continuous.comp continuous_fst).prodMk (ψ.continuous.comp continuous_snd)
  continuous_invFun := (φ.symm.continuous.comp continuous_fst).prodMk (ψ.symm.continuous.comp continuous_snd)

theorem char_prod (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) :
    addEquivAddHaarChar (prodE φ ψ) = addEquivAddHaarChar φ * addEquivAddHaarChar ψ := by
  have hmap : ((addHaar : Measure A).prod (addHaar : Measure B)).map (prodE φ ψ) =
      ((addEquivAddHaarChar φ)⁻¹ * (addEquivAddHaarChar ψ)⁻¹) •
        ((addHaar : Measure A).prod (addHaar : Measure B)) := by
    rw [show (prodE φ ψ : A × B → A × B) = Prod.map φ ψ from rfl,
      ← Measure.map_prod_map _ _ (map_continuous φ).measurable (map_continuous ψ).measurable,
      map_char (addHaar : Measure A) φ, map_char (addHaar : Measure B) ψ,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [char_eq_of_map _ _ (mul_ne_zero (inv_ne_zero (addEquivAddHaarChar_pos φ).ne')
    (inv_ne_zero (addEquivAddHaarChar_pos ψ).ne')) hmap, mul_inv, inv_inv, inv_inv]

end Gen

end PI.IwaMeasEx.MH

end
end

noncomputable section

namespace PI.IwaMeasEx.MH

open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne

section Gen

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem char_eq_of_map' (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) {c : ℝ≥0} (hc : c ≠ 0)
    (h : μ.map φ = c • μ) : addEquivAddHaarChar φ = c⁻¹ := by
  have hreg : μ.Regular := inferInstance
  have h1 := MeasureTheory.addEquivAddHaarChar_smul_map μ φ
  rw [h, smul_smul] at h1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : A)
  have hpos : 0 < μ K := MeasureTheory.Measure.measure_pos_of_mem_nhds μ hKn
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun ν : Measure A => ν K) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : μ K * ((addEquivAddHaarChar φ * c : ℝ≥0) : ℝ≥0∞) = μ K * 1 := by
    rw [mul_one, mul_comm]
    exact_mod_cast h2
  have h4 : ((addEquivAddHaarChar φ * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_right_inj hpos.ne' hfin).1 h3
  have h5 : addEquivAddHaarChar φ * c = 1 := by exact_mod_cast h4
  exact eq_inv_of_mul_eq_one_left h5

def piE {ι : Type*} [Fintype ι] (φ : ι → A ≃ₜ+ A) : (ι → A) ≃ₜ+ (ι → A) where
  toFun x i := φ i (x i)
  invFun x i := (φ i).symm (x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' x y := by funext i; simp
  continuous_toFun := continuous_pi fun i => (φ i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (φ i).symm.continuous.comp (continuous_apply i)

theorem char_pi {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → A ≃ₜ+ A) :
    addEquivAddHaarChar (piE φ) = ∏ i, addEquivAddHaarChar (φ i) := by
  classical
  set μ : Measure A := Measure.addHaar with hμ
  set c : ι → ℝ≥0 := fun i => addEquivAddHaarChar (φ i) with hcdef
  have hc0 : ∀ i, c i ≠ 0 := fun i => (addEquivAddHaarChar_pos (φ i)).ne'
  have hmap : ∀ i, μ.map (φ i) = (c i)⁻¹ • μ := by
    intro i
    have h1 := addEquivAddHaarChar_smul_map μ (φ i)
    calc μ.map (φ i) = (c i)⁻¹ • (c i • μ.map (φ i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hc0 i), one_smul]
      _ = (c i)⁻¹ • μ := by rw [h1]
  haveI : ∀ i, SigmaFinite (μ.map (φ i)) := fun i => by rw [hmap i]; infer_instance
  have hbox : ∀ d : ι → ℝ≥0, Measure.pi (fun i => d i • μ) = (∏ i, d i) • Measure.pi (fun _ : ι => μ) := by
    intro d
    refine (Measure.pi_eq (μ := fun i => d i • μ) (μ' := (∏ i, d i) • Measure.pi (fun _ : ι => μ)) fun s hs => ?_)
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
    push_cast
    rfl
  have hpm : (Measure.pi (fun _ : ι => μ)).map (piE φ) = (∏ i, (c i)⁻¹) • Measure.pi (fun _ : ι => μ) := by
    have h2 : ⇑(piE φ) = fun x i => φ i (x i) := rfl
    rw [h2, Measure.pi_map_pi (f := fun i => (φ i : A → A)) (fun i => (φ i).continuous.measurable.aemeasurable)]
    simp only [hmap]
    exact hbox _
  have h3 := char_eq_of_map' (Measure.pi fun _ : ι => μ) (piE φ)
    (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (hc0 i)) hpm
  rw [h3, Finset.prod_inv_distrib, inv_inv]

end Gen

section AEf

variable (I : AutInst)

attribute [local instance] AfT.tAf Nrm.topRing Nrm.t2 Nrm.mAf Nrm.borel_mAf MFI.locallyCompact_AEf

end AEf

end PI.IwaMeasEx.MH

end
